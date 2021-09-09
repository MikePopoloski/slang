//------------------------------------------------------------------------------
//! @file Statements.h
//! @brief Statement creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/AssertionExpr.h"
#include "slang/binding/EvalContext.h"
#include "slang/binding/Expression.h"
#include "slang/binding/TimingControl.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/util/Enum.h"
#include "slang/util/ScopeGuard.h"

namespace slang {

class BlockStatement;
class RandSeqProductionSymbol;
class StatementBlockSymbol;
class VariableSymbol;
struct ForLoopStatementSyntax;
struct ForeachLoopStatementSyntax;
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
    x(Disable) \
    x(Conditional) \
    x(Case) \
    x(ForLoop) \
    x(RepeatLoop) \
    x(ForeachLoop) \
    x(WhileLoop) \
    x(DoWhileLoop) \
    x(ForeverLoop) \
    x(Timed) \
    x(ImmediateAssertion) \
    x(ConcurrentAssertion) \
    x(DisableFork) \
    x(Wait) \
    x(WaitFork) \
    x(WaitOrder) \
    x(EventTrigger) \
    x(ProceduralAssign) \
    x(ProceduralDeassign) \
    x(RandCase) \
    x(RandSequence)
ENUM(StatementKind, STATEMENT);
#undef STATEMENT

#define CASE_CONDITION(x) \
    x(Normal) \
    x(WildcardXOrZ) \
    x(WildcardJustZ) \
    x(Inside)
ENUM(CaseStatementCondition, CASE_CONDITION)
#undef CASE_CONDITION

#define CASE_CHECK(x) \
    x(None) \
    x(Unique) \
    x(Unique0) \
    x(Priority)
ENUM(CaseStatementCheck, CASE_CHECK)
#undef CASE_CHECK
// clang-format on

enum class StatementFlags {
    None = 0,
    InLoop = 1 << 0,
    Func = 1 << 1,
    Final = 1 << 2,
    InForkJoin = 1 << 3,
    InForkJoinNone = 1 << 4,
    AutoLifetime = 1 << 5,
    InRandSeq = 1 << 6
};
BITMASK(StatementFlags, InRandSeq);

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
        Continue,

        /// A disable statement was invoked; we should exit blocks until we find the target.
        Disable
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

        /// Tracks various bits of context about where we are in statement binding.
        bitmask<StatementFlags> flags;

        /// Attempts to match up the head of the block list with the given
        /// statement syntax node. If they match, the block symbol is popped
        /// and returned wrapped inside a BlockStatement.
        /// Otherwise nullptr is returned.
        BlockStatement* tryGetBlock(Compilation& compilation, const SyntaxNode& syntax);

        /// Records that we've entered a loop, and returns a guard that will
        /// revert back to the previous state on destruction.
        [[nodiscard]] auto enterLoop() {
            auto guard = ScopeGuard([this, saved = flags.has(StatementFlags::InLoop)] {
                if (saved)
                    flags |= StatementFlags::InLoop;
                else
                    flags &= ~StatementFlags::InLoop;
            });
            flags |= StatementFlags::InLoop;
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
    decltype(auto) visit(TVisitor&& visitor, Args&&... args) const;

protected:
    Statement(StatementKind kind, SourceRange sourceRange) : kind(kind), sourceRange(sourceRange) {}

    static Statement& badStmt(Compilation& compilation, const Statement* stmt);
};

/// A wrapper around a statement syntax node and some associated symbols that can later
/// be turned into an actual statement tree. The point of this is to allow symbols to
/// defer statement binding until its actually needed.
class StatementBinder {
public:
    void setSyntax(const Scope& scope, const StatementSyntax& syntax, bool labelHandled,
                   bitmask<StatementFlags> flags);
    void setSyntax(const StatementBlockSymbol& scope, const ForLoopStatementSyntax& syntax,
                   bitmask<StatementFlags> flags);
    void setItems(Scope& scope, const SyntaxList<SyntaxNode>& syntax, SourceRange sourceRange,
                  bitmask<StatementFlags> flags);

    const Statement& getStatement(const BindContext& context) const;
    span<const StatementBlockSymbol* const> getBlocks() const { return blocks; }
    const StatementSyntax* getSyntax() const;

private:
    const Statement& bindStatement(const BindContext& context) const;

    std::variant<const StatementSyntax*, const SyntaxList<SyntaxNode>*> syntax;
    span<const StatementBlockSymbol* const> blocks;
    mutable const Statement* stmt = nullptr;
    SourceRange sourceRange;
    bitmask<StatementFlags> flags;
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

    void serializeTo(ASTSerializer& serializer) const;

    static const InvalidStatement Instance;
};

/// Represents an empty statement, used as a placeholder or an anchor for attributes.
class EmptyStatement : public Statement {
public:
    explicit EmptyStatement(SourceRange sourceRange) :
        Statement(StatementKind::Empty, sourceRange) {}

    EvalResult evalImpl(EvalContext&) const { return EvalResult::Success; }
    bool verifyConstantImpl(EvalContext&) const { return true; }

    void serializeTo(ASTSerializer&) const {}

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

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::List; }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        for (auto stmt : list)
            stmt->visit(visitor);
    }
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
    bool isNamedBlock() const;

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Statement& fromSyntax(Compilation& compilation, const BlockStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Block; }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        getStatements().visit(visitor);
    }

private:
    const StatementBlockSymbol* block = nullptr;
    const StatementList* list = nullptr;
};

struct ReturnStatementSyntax;

class ReturnStatement : public Statement {
public:
    const Expression* expr;

    ReturnStatement(const Expression* expr, SourceRange sourceRange) :
        Statement(StatementKind::Return, sourceRange), expr(expr) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ReturnStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Return; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        if (expr)
            expr->visit(visitor);
    }
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

    void serializeTo(const ASTSerializer&) const {}

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

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::Continue; }
};

struct DisableStatementSyntax;

class DisableStatement : public Statement {
public:
    const Symbol& target;
    bool isHierarchical;

    DisableStatement(const Symbol& target, bool isHierarchical, SourceRange sourceRange) :
        Statement(StatementKind::Disable, sourceRange), target(target),
        isHierarchical(isHierarchical) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const DisableStatementSyntax& syntax,
                                 const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Disable; }
};

class VariableDeclStatement : public Statement {
public:
    const VariableSymbol& symbol;

    VariableDeclStatement(const VariableSymbol& symbol, SourceRange sourceRange) :
        Statement(StatementKind::VariableDeclaration, sourceRange), symbol(symbol) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

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

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Conditional; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        cond.visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        ifTrue.visit(visitor);
        if (ifFalse)
            ifFalse->visit(visitor);
    }
};

struct CaseStatementSyntax;

class CaseStatement : public Statement {
public:
    struct ItemGroup {
        span<const Expression* const> expressions;
        not_null<const Statement*> stmt;
    };

    const Expression& expr;
    span<ItemGroup const> items;
    const Statement* defaultCase = nullptr;
    CaseStatementCondition condition;
    CaseStatementCheck check;

    CaseStatement(CaseStatementCondition condition, CaseStatementCheck check,
                  const Expression& expr, span<ItemGroup const> items, const Statement* defaultCase,
                  SourceRange sourceRange) :
        Statement(StatementKind::Case, sourceRange),
        expr(expr), items(items), defaultCase(defaultCase), condition(condition), check(check) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const CaseStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Case; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
        for (auto& item : items) {
            for (auto itemExpr : item.expressions)
                itemExpr->visit(visitor);
        }
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        for (auto& item : items)
            item.stmt->visit(visitor);
        if (defaultCase)
            defaultCase->visit(visitor);
    }
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

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ForLoop; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto init : initializers)
            init->visit(visitor);
        if (stopExpr)
            stopExpr->visit(visitor);
        for (auto step : steps)
            step->visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        body.visit(visitor);
    }
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

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::RepeatLoop; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        count.visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        body.visit(visitor);
    }
};

struct ForeachLoopListSyntax;
struct ForeachLoopStatementSyntax;

class ForeachLoopStatement : public Statement {
public:
    /// Describes one dimension that will be iterated by the loop.
    struct LoopDim {
        /// The static range of the dimension, or nullopt if the
        /// dimension is dynamically sized.
        optional<ConstantRange> range;

        /// The loop variable for this dimension, or nullptr if
        /// the dimension is being skipped.
        const IteratorSymbol* loopVar = nullptr;
    };

    const Expression& arrayRef;
    span<const LoopDim> loopDims;
    const Statement& body;

    ForeachLoopStatement(const Expression& arrayRef, span<const LoopDim> loopDims,
                         const Statement& body, SourceRange sourceRange) :
        Statement(StatementKind::ForeachLoop, sourceRange),
        arrayRef(arrayRef), loopDims(loopDims), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const ForeachLoopStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static const Expression* buildLoopDims(const ForeachLoopListSyntax& loopList,
                                           BindContext& context, SmallVector<LoopDim>& dims);

    static bool isKind(StatementKind kind) { return kind == StatementKind::ForeachLoop; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        arrayRef.visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        body.visit(visitor);
    }

private:
    EvalResult evalRecursive(EvalContext& context, const ConstantValue& cv,
                             span<const LoopDim> loopDims) const;
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

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::WhileLoop; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        cond.visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        body.visit(visitor);
    }
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

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::DoWhileLoop; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        cond.visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        body.visit(visitor);
    }
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

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ForeverLoop; }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        body.visit(visitor);
    }
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

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ExpressionStatement; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
    }
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

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Timed; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        timing.visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        stmt.visit(visitor);
    }
};

struct ImmediateAssertionStatementSyntax;

class ImmediateAssertionStatement : public Statement {
public:
    const Expression& cond;
    const Statement* ifTrue;
    const Statement* ifFalse;
    AssertionKind assertionKind;
    bool isDeferred;
    bool isFinal;

    ImmediateAssertionStatement(AssertionKind assertionKind, const Expression& cond,
                                const Statement* ifTrue, const Statement* ifFalse, bool isDeferred,
                                bool isFinal, SourceRange sourceRange) :
        Statement(StatementKind::ImmediateAssertion, sourceRange),
        cond(cond), ifTrue(ifTrue), ifFalse(ifFalse), assertionKind(assertionKind),
        isDeferred(isDeferred), isFinal(isFinal) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const ImmediateAssertionStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ImmediateAssertion; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        cond.visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        if (ifTrue)
            ifTrue->visit(visitor);
        if (ifFalse)
            ifFalse->visit(visitor);
    }
};

struct ConcurrentAssertionStatementSyntax;

class ConcurrentAssertionStatement : public Statement {
public:
    const AssertionExpr& propertySpec;
    const Statement* ifTrue;
    const Statement* ifFalse;
    AssertionKind assertionKind;

    ConcurrentAssertionStatement(AssertionKind assertionKind, const AssertionExpr& propertySpec,
                                 const Statement* ifTrue, const Statement* ifFalse,
                                 SourceRange sourceRange) :
        Statement(StatementKind::ConcurrentAssertion, sourceRange),
        propertySpec(propertySpec), ifTrue(ifTrue), ifFalse(ifFalse), assertionKind(assertionKind) {
    }

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const ConcurrentAssertionStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ConcurrentAssertion; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        propertySpec.visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        if (ifTrue)
            ifTrue->visit(visitor);
        if (ifFalse)
            ifFalse->visit(visitor);
    }
};

struct DisableForkStatementSyntax;

class DisableForkStatement : public Statement {
public:
    explicit DisableForkStatement(SourceRange sourceRange) :
        Statement(StatementKind::DisableFork, sourceRange) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const DisableForkStatementSyntax& syntax);

    void serializeTo(const ASTSerializer&) const {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::DisableFork; }
};

struct WaitStatementSyntax;

class WaitStatement : public Statement {
public:
    const Expression& cond;
    const Statement& stmt;

    WaitStatement(const Expression& cond, const Statement& stmt, SourceRange sourceRange) :
        Statement(StatementKind::Wait, sourceRange), cond(cond), stmt(stmt) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const WaitStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Wait; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        cond.visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        stmt.visit(visitor);
    }
};

struct WaitForkStatementSyntax;

class WaitForkStatement : public Statement {
public:
    explicit WaitForkStatement(SourceRange sourceRange) :
        Statement(StatementKind::WaitFork, sourceRange) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const WaitForkStatementSyntax& syntax);

    void serializeTo(const ASTSerializer&) const {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::WaitFork; }
};

struct WaitOrderStatementSyntax;

class WaitOrderStatement : public Statement {
public:
    span<const Expression* const> events;
    const Statement* ifTrue;
    const Statement* ifFalse;

    WaitOrderStatement(span<const Expression* const> events, const Statement* ifTrue,
                       const Statement* ifFalse, SourceRange sourceRange) :
        Statement(StatementKind::WaitOrder, sourceRange),
        events(events), ifTrue(ifTrue), ifFalse(ifFalse) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const WaitOrderStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::WaitOrder; }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        if (ifTrue)
            ifTrue->visit(visitor);
        if (ifFalse)
            ifFalse->visit(visitor);
    }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto ev : events)
            ev->visit(visitor);
    }
};

struct EventTriggerStatementSyntax;

class EventTriggerStatement : public Statement {
public:
    const Expression& target;
    const TimingControl* timing;
    bool isNonBlocking;

    EventTriggerStatement(const Expression& target, const TimingControl* timing, bool isNonBlocking,
                          SourceRange sourceRange) :
        Statement(StatementKind::EventTrigger, sourceRange),
        target(target), timing(timing), isNonBlocking(isNonBlocking) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const EventTriggerStatementSyntax& syntax,
                                 const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::EventTrigger; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        target.visit(visitor);
        if (timing)
            timing->visit(visitor);
    }
};

struct ProceduralAssignStatementSyntax;

class ProceduralAssignStatement : public Statement {
public:
    const Expression& assignment;
    bool isForce;

    ProceduralAssignStatement(const Expression& assignment, bool isForce, SourceRange sourceRange) :
        Statement(StatementKind::ProceduralAssign, sourceRange), assignment(assignment),
        isForce(isForce) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const ProceduralAssignStatementSyntax& syntax,
                                 const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ProceduralAssign; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        assignment.visit(visitor);
    }
};

struct ProceduralDeassignStatementSyntax;

class ProceduralDeassignStatement : public Statement {
public:
    const Expression& lvalue;
    bool isRelease;

    ProceduralDeassignStatement(const Expression& lvalue, bool isRelease, SourceRange sourceRange) :
        Statement(StatementKind::ProceduralDeassign, sourceRange), lvalue(lvalue),
        isRelease(isRelease) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const ProceduralDeassignStatementSyntax& syntax,
                                 const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ProceduralDeassign; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        lvalue.visit(visitor);
    }
};

struct RandCaseStatementSyntax;

class RandCaseStatement : public Statement {
public:
    struct Item {
        not_null<const Expression*> expr;
        not_null<const Statement*> stmt;
    };

    span<Item const> items;

    RandCaseStatement(span<Item const> items, SourceRange sourceRange) :
        Statement(StatementKind::RandCase, sourceRange), items(items) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation, const RandCaseStatementSyntax& syntax,
                                 const BindContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::RandCase; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto& item : items)
            item.expr->visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        for (auto& item : items)
            item.stmt->visit(visitor);
    }
};

struct RandSequenceStatementSyntax;

class RandSequenceStatement : public Statement {
public:
    const RandSeqProductionSymbol* firstProduction;

    RandSequenceStatement(const RandSeqProductionSymbol* firstProduction, SourceRange sourceRange) :
        Statement(StatementKind::RandSequence, sourceRange), firstProduction(firstProduction) {}

    EvalResult evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const RandSequenceStatementSyntax& syntax,
                                 const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::RandSequence; }
};

} // namespace slang
