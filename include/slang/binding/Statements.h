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

class BlockStatement;
class StatementBlockSymbol;
class TimingControl;
class VariableSymbol;
struct ForLoopStatementSyntax;
struct StatementSyntax;

// clang-format off
#define STATEMENT(x) \
    x(Invalid) \
    x(Empty) \
    x(List) \
    x(Block) \
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

    /// The source range of this statement, if it originated from source code.
    SourceRange sourceRange;

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
        span<const StatementBlockSymbol* const> blocks;

        /// Tracks whether we're currently within a loop (which can control,
        /// for example, whether a break or continue statement is allowed).
        bool inLoop = false;

        /// Attempts to match up the head of the block list with the given
        /// statement syntax node. If they match, the block symbol is popped
        /// and returned wrapped inside a BlockStatement.
        /// Otherwise nullptr is returned.
        BlockStatement* tryGetBlock(Compilation& compilation, const SyntaxNode& syntax);

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
                                 StatementContext& stmtCtx, bool inList = false,
                                 bool labelHandled = false);

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
    Statement(StatementKind kind, SourceRange sourceRange) : kind(kind), sourceRange(sourceRange) {}

    static Statement& badStmt(Compilation& compilation, const Statement* stmt);
};

/// A wrapper around a statement syntax node and some associated symbols that can later
/// be turned into an actual statement tree. The point of this is to allow symbols to
/// defer statement binding until its actually needed.
class StatementBinder {
public:
    void setSyntax(const Scope& scope, const StatementSyntax& syntax, bool labelHandled);
    void setSyntax(const StatementBlockSymbol& scope, const ForLoopStatementSyntax& syntax);
    void setItems(Scope& scope, const SyntaxList<SyntaxNode>& syntax, SourceRange sourceRange);

    const Statement& getStatement(const BindContext& context) const;
    span<const StatementBlockSymbol* const> getBlocks() const { return blocks; }

private:
    const Statement& bindStatement(const BindContext& context) const;

    std::variant<const StatementSyntax*, const SyntaxList<SyntaxNode>*> syntax;
    span<const StatementBlockSymbol* const> blocks;
    mutable const Statement* stmt = nullptr;
    SourceRange sourceRange;
    mutable bool isBinding = false;
    bool labelHandled = false;
};

/// Represents an invalid statement, which is usually generated and inserted
/// into a statement list due to violation of language semantics or type checking.
class InvalidStatement : public Statement {
public:
    /// A wrapped sub-statement that is considered invalid.
    const Statement* child;

    explicit InvalidStatement(const Statement* child) :
        Statement(StatementKind::Invalid, SourceRange()), child(child) {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::Invalid; }

    static const InvalidStatement Instance;
};

/// Represents an empty statement, used as a placeholder or an anchor for attributes.
class EmptyStatement : public Statement {
public:
    explicit EmptyStatement(SourceRange sourceRange) :
        Statement(StatementKind::Empty, sourceRange) {}

    EvalResult evalImpl(EvalContext&) const { return EvalResult::Success; }
    bool verifyConstantImpl(EvalContext&) const { return true; }

    static bool isKind(StatementKind kind) { return kind == StatementKind::Empty; }
};

/// Represents a list of statements.
class StatementList : public Statement {
public:
    span<const Statement* const> list;

    StatementList(span<const Statement* const> list, SourceRange sourceRange) :
        Statement(StatementKind::List, sourceRange), list(list) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::List; }
};

struct BlockStatementSyntax;

/// Represents a sequential or parallel block statement.
class BlockStatement : public Statement {
public:
    StatementBlockKind blockKind;

    BlockStatement(const StatementBlockSymbol& block, SourceRange sourceRange);
    BlockStatement(const StatementList& list, StatementBlockKind blockKind,
                   SourceRange sourceRange) :
        Statement(StatementKind::Block, sourceRange),
        blockKind(blockKind), list(&list) {}

    const Statement& getStatements() const;
    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const BlockStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Block; }

private:
    const StatementBlockSymbol* block = nullptr;
    const StatementList* list = nullptr;
};

struct ReturnStatementSyntax;

class ReturnStatement : public Statement {
public:
    const Expression* expr;

    explicit ReturnStatement(const Expression* expr, SourceRange sourceRange) :
        Statement(StatementKind::Return, sourceRange), expr(expr) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ReturnStatementSyntax& syntax,
                                 const BindContext& context);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Return; }
};

struct JumpStatementSyntax;

class BreakStatement : public Statement {
public:
    explicit BreakStatement(SourceRange sourceRange) :
        Statement(StatementKind::Break, sourceRange) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const JumpStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Break; }
};

class ContinueStatement : public Statement {
public:
    explicit ContinueStatement(SourceRange sourceRange) :
        Statement(StatementKind::Continue, sourceRange) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const JumpStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Continue; }
};

class VariableDeclStatement : public Statement {
public:
    const VariableSymbol& symbol;

    VariableDeclStatement(const VariableSymbol& symbol, SourceRange sourceRange) :
        Statement(StatementKind::VariableDeclaration, sourceRange), symbol(symbol) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::VariableDeclaration; }
};

struct ConditionalStatementSyntax;

class ConditionalStatement : public Statement {
public:
    const Expression& cond;
    const Statement& ifTrue;
    const Statement* ifFalse;

    ConditionalStatement(const Expression& cond, const Statement& ifTrue, const Statement* ifFalse,
                         SourceRange sourceRange) :
        Statement(StatementKind::Conditional, sourceRange),
        cond(cond), ifTrue(ifTrue), ifFalse(ifFalse) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ConditionalStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Conditional; }
};

struct CaseStatementSyntax;

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
                  span<ItemGroup const> items, const Statement* defaultCase,
                  SourceRange sourceRange) :
        Statement(StatementKind::Case, sourceRange),
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
                     span<const Expression* const> steps, const Statement& body,
                     SourceRange sourceRange) :
        Statement(StatementKind::ForLoop, sourceRange),
        initializers(initializers), stopExpr(stopExpr), steps(steps), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ForLoopStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::ForLoop; }
};

struct LoopStatementSyntax;

class RepeatLoopStatement : public Statement {
public:
    const Expression& count;
    const Statement& body;

    RepeatLoopStatement(const Expression& count, const Statement& body, SourceRange sourceRange) :
        Statement(StatementKind::RepeatLoop, sourceRange), count(count), body(body) {}

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

    WhileLoopStatement(const Expression& cond, const Statement& body, SourceRange sourceRange) :
        Statement(StatementKind::WhileLoop, sourceRange), cond(cond), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const LoopStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::WhileLoop; }
};

struct DoWhileStatementSyntax;

class DoWhileLoopStatement : public Statement {
public:
    const Expression& cond;
    const Statement& body;

    DoWhileLoopStatement(const Expression& cond, const Statement& body, SourceRange sourceRange) :
        Statement(StatementKind::DoWhileLoop, sourceRange), cond(cond), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const DoWhileStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::DoWhileLoop; }
};

struct ForeverStatementSyntax;

class ForeverLoopStatement : public Statement {
public:
    const Statement& body;

    ForeverLoopStatement(const Statement& body, SourceRange sourceRange) :
        Statement(StatementKind::ForeverLoop, sourceRange), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ForeverStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::ForeverLoop; }
};

struct ExpressionStatementSyntax;
struct VoidCastedCallStatementSyntax;

class ExpressionStatement : public Statement {
public:
    const Expression& expr;

    ExpressionStatement(const Expression& expr, SourceRange sourceRange) :
        Statement(StatementKind::ExpressionStatement, sourceRange), expr(expr) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ExpressionStatementSyntax& syntax,
                                 const BindContext& context);

    static Statement& fromSyntax(Compilation& compilation,
                                 const VoidCastedCallStatementSyntax& syntax,
                                 const BindContext& context);

    static bool isKind(StatementKind kind) { return kind == StatementKind::ExpressionStatement; }
};

struct TimingControlStatementSyntax;

class TimedStatement : public Statement {
public:
    const TimingControl& timing;
    const Statement& stmt;

    TimedStatement(const TimingControl& timing, const Statement& stmt, SourceRange sourceRange) :
        Statement(StatementKind::Timed, sourceRange), timing(timing), stmt(stmt) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const TimingControlStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Timed; }
};

struct ImmediateAssertionStatementSyntax;

class AssertionStatement : public Statement {
public:
    const Expression& cond;
    const Statement* ifTrue;
    const Statement* ifFalse;
    AssertionKind assertionKind;
    bool isDeferred;
    bool isFinal;

    AssertionStatement(AssertionKind assertionKind, const Expression& cond, const Statement* ifTrue,
                       const Statement* ifFalse, bool isDeferred, bool isFinal,
                       SourceRange sourceRange) :
        Statement(StatementKind::Assertion, sourceRange),
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