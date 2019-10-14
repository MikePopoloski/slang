//------------------------------------------------------------------------------
// Statements.h
// Statement creation and analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/EvalContext.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/util/ScopeGuard.h"

namespace slang {

class SequentialBlockStatement;
class SequentialBlockSymbol;
class TimingControl;
class VariableSymbol;

// clang-format off
#define STATEMENT(x) \
    x(Invalid) \
    x(Empty) \
    x(List) \
    x(SequentialBlock) \
    x(ExpressionStatement) \
    x(VariableDeclaration) \
    x(Return) \
    x(Continue) \
    x(Break) \
    x(Conditional) \
    x(Case) \
    x(ForLoop) \
    x(RepeatLoop) \
    x(WhileLoop) \
    x(DoWhileLoop) \
    x(ForeverLoop) \
    x(Timed) \
    x(Assertion)
ENUM(StatementKind, STATEMENT);
#undef STATEMENT
// clang-format on

/// The base class for all statements in SystemVerilog.
class Statement {
public:
    /// The kind of statement; indicates the type of derived class.
    StatementKind kind;

    /// The syntax used to create this statement, if it was parsed from a source file.
    const StatementSyntax* syntax = nullptr;

    /// Indicates whether the statement is invalid.
    bool bad() const { return kind == StatementKind::Invalid; }

    /// Specifies possible results of evaluating a statement.
    enum class EvalResult {
        /// Evaluation totally failed and we should give up on any further processing.
        Fail,

        /// Evaluation succeeded.
        Success,

        /// A return statement was invoked; we should exit the current function.
        Return,

        /// A break statement was invoked; we should exit the current loop.
        Break,

        /// A continue statement was invoked; we should continue the current loop.
        Continue
    };

    /// Evaluates the statement under the given evaluation context.
    EvalResult eval(EvalContext& context) const;

    /// Verifies that this statement is valid in a constant function.
    /// If it's not, appropriate diagnostics will be issued.
    bool verifyConstant(EvalContext& context) const;

    /// Additional information passed along during statement binding.
    struct StatementContext {
        /// A series of block symbols that are expected to be bound, in order,
        /// during the creation of the statement tree. Each statement created
        /// can pop blocks off the beginning of this list.
        span<const SequentialBlockSymbol* const> blocks;

        /// Tracks whether we're currently within a loop (which can control,
        /// for example, whether a break or continue statement is allowed).
        bool inLoop = false;

        /// Attempts to match up the head of the block list with the given
        /// statement syntax node. If they match, the block symbol is popped
        /// and returned wrapped inside a SequentialBlockStatement.
        /// Otherwise nullptr is returned.
        SequentialBlockStatement* tryGetBlock(Compilation& compilation, const SyntaxNode& syntax);

        /// Records that we've entered a loop, and returns a guard that will
        /// revert back to the previous inLoop state on destruction.
        [[nodiscard]] auto enterLoop() {
            auto guard = ScopeGuard([this, saved = inLoop] { inLoop = saved; });
            inLoop = true;
            return guard;
        }
    };

    /// Binds a statement tree from the given syntax nodes.
    static const Statement& bind(const StatementSyntax& syntax, const BindContext& context,
                                 StatementContext& stmtCtx);

    template<typename T>
    T& as() {
        ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    template<typename T>
    const T& as() const {
        ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

protected:
    explicit Statement(StatementKind kind) : kind(kind) {}

    static Statement& badStmt(Compilation& compilation, const Statement* stmt);
};

/// A wrapper around a statement syntax node and some associated symbols that can later
/// be turned into an actual statement tree. The point of this is to allow symbols to
/// defer statement binding until its actually needed.
class StatementBinder {
public:
    void setSyntax(const Scope& scope, const StatementSyntax& syntax);
    void setSyntax(const SequentialBlockSymbol& scope, const ForLoopStatementSyntax& syntax);
    void setItems(Scope& scope, const SyntaxList<SyntaxNode>& syntax);

    const Statement& getStatement(const BindContext& context) const;
    span<const SequentialBlockSymbol* const> getBlocks() const { return blocks; }

private:
    const Statement& bindStatement(const BindContext& context) const;

    std::variant<const StatementSyntax*, const SyntaxList<SyntaxNode>*> syntax;
    mutable const Statement* stmt = nullptr;
    span<const SequentialBlockSymbol* const> blocks;
};

/// Represents an invalid statement, which is usually generated and inserted
/// into a statement list due to violation of language semantics or type checking.
class InvalidStatement : public Statement {
public:
    /// A wrapped sub-statement that is considered invalid.
    const Statement* child;

    explicit InvalidStatement(const Statement* child) :
        Statement(StatementKind::Invalid), child(child) {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::Invalid; }

    static const InvalidStatement Instance;
};

/// Represents an empty statement, used as a placeholder or an anchor for attributes.
class EmptyStatement : public Statement {
public:
    EmptyStatement() : Statement(StatementKind::Empty) {}

    EvalResult evalImpl(EvalContext&) const { return EvalResult::Success; }
    bool verifyConstantImpl(EvalContext&) const { return true; }

    static bool isKind(StatementKind kind) { return kind == StatementKind::Empty; }
};

/// Represents a list of statements.
class StatementList : public Statement {
public:
    span<const Statement* const> list;

    explicit StatementList(span<const Statement* const> list) :
        Statement(StatementKind::List), list(list) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::List; }
    static const StatementList Empty;
};

/// Represents a sequential block statement.
class SequentialBlockStatement : public Statement {
public:
    explicit SequentialBlockStatement(const SequentialBlockSymbol& block) :
        Statement(StatementKind::SequentialBlock), block(&block) {}

    explicit SequentialBlockStatement(const StatementList& list) :
        Statement(StatementKind::SequentialBlock), list(&list) {}

    const Statement& getStatements() const;
    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const BlockStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::SequentialBlock; }

private:
    const SequentialBlockSymbol* block = nullptr;
    const StatementList* list = nullptr;
};

class ReturnStatement : public Statement {
public:
    const Expression* expr;

    explicit ReturnStatement(const Expression* expr) :
        Statement(StatementKind::Return), expr(expr) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ReturnStatementSyntax& syntax,
                                 const BindContext& context);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Return; }
};

class BreakStatement : public Statement {
public:
    BreakStatement() : Statement(StatementKind::Break) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const JumpStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Break; }
};

class ContinueStatement : public Statement {
public:
    ContinueStatement() : Statement(StatementKind::Continue) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const JumpStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Continue; }
};

class VariableDeclStatement : public Statement {
public:
    const VariableSymbol& symbol;

    explicit VariableDeclStatement(const VariableSymbol& symbol) :
        Statement(StatementKind::VariableDeclaration), symbol(symbol) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::VariableDeclaration; }
};

class ConditionalStatement : public Statement {
public:
    const Expression& cond;
    const Statement& ifTrue;
    const Statement* ifFalse;

    ConditionalStatement(const Expression& cond, const Statement& ifTrue,
                         const Statement* ifFalse) :
        Statement(StatementKind::Conditional),
        cond(cond), ifTrue(ifTrue), ifFalse(ifFalse) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ConditionalStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Conditional; }
};

class CaseStatement : public Statement {
public:
    struct ItemGroup {
        span<const Expression* const> expressions;
        not_null<const Statement*> stmt;
    };

    enum class Condition { Normal, WildcardXOrZ, WildcardJustZ };
    enum class Check { None, Unique, Unique0, Priority };

    const Expression& expr;
    span<ItemGroup const> items;
    const Statement* defaultCase = nullptr;
    Condition condition;
    Check check;

    CaseStatement(Condition condition, Check check, const Expression& expr,
                  span<ItemGroup const> items, const Statement* defaultCase) :
        Statement(StatementKind::Case),
        expr(expr), items(items), defaultCase(defaultCase), condition(condition), check(check) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const CaseStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Case; }
};

class ForLoopStatement : public Statement {
public:
    span<const Expression* const> initializers;
    const Expression* stopExpr;
    span<const Expression* const> steps;
    const Statement& body;

    ForLoopStatement(span<const Expression* const> initializers, const Expression* stopExpr,
                     span<const Expression* const> steps, const Statement& body) :
        Statement(StatementKind::ForLoop),
        initializers(initializers), stopExpr(stopExpr), steps(steps), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ForLoopStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::ForLoop; }
};

class RepeatLoopStatement : public Statement {
public:
    const Expression& count;
    const Statement& body;

    RepeatLoopStatement(const Expression& count, const Statement& body) :
        Statement(StatementKind::RepeatLoop), count(count), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const LoopStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::RepeatLoop; }
};

class WhileLoopStatement : public Statement {
public:
    const Expression& cond;
    const Statement& body;

    WhileLoopStatement(const Expression& cond, const Statement& body) :
        Statement(StatementKind::WhileLoop), cond(cond), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const LoopStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::WhileLoop; }
};

class DoWhileLoopStatement : public Statement {
public:
    const Expression& cond;
    const Statement& body;

    DoWhileLoopStatement(const Expression& cond, const Statement& body) :
        Statement(StatementKind::DoWhileLoop), cond(cond), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const DoWhileStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::DoWhileLoop; }
};

class ForeverLoopStatement : public Statement {
public:
    const Statement& body;

    explicit ForeverLoopStatement(const Statement& body) :
        Statement(StatementKind::ForeverLoop), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ForeverStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::ForeverLoop; }
};

class ExpressionStatement : public Statement {
public:
    const Expression& expr;

    explicit ExpressionStatement(const Expression& expr) :
        Statement(StatementKind::ExpressionStatement), expr(expr) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ExpressionStatementSyntax& syntax,
                                 const BindContext& context);

    static bool isKind(StatementKind kind) { return kind == StatementKind::ExpressionStatement; }
};

class TimedStatement : public Statement {
public:
    const TimingControl& timing;
    const Statement& stmt;

    TimedStatement(const TimingControl& timing, const Statement& stmt) :
        Statement(StatementKind::Timed), timing(timing), stmt(stmt) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const TimingControlStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Timed; }
};

class AssertionStatement : public Statement {
public:
    const Expression& cond;
    const Statement* ifTrue;
    const Statement* ifFalse;
    AssertionKind assertionKind;
    bool isDeferred;
    bool isFinal;

    AssertionStatement(AssertionKind assertionKind, const Expression& cond, const Statement* ifTrue,
                       const Statement* ifFalse, bool isDeferred, bool isFinal) :
        Statement(StatementKind::Assertion),
        cond(cond), ifTrue(ifTrue), ifFalse(ifFalse), assertionKind(assertionKind),
        isDeferred(isDeferred), isFinal(isFinal) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const ImmediateAssertionStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Assertion; }
};

} // namespace slang