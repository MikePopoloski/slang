//------------------------------------------------------------------------------
//! @file Statements.h
//! @brief Statement creation and analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Expression.h"
#include "slang/ast/Patterns.h"
#include "slang/ast/TimingControl.h"
#include "slang/ast/expressions/AssertionExpr.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Enum.h"
#include "slang/util/ScopeGuard.h"

namespace slang::ast {

class EvalContext;
class IteratorSymbol;
class RandSeqProductionSymbol;
class StatementBlockSymbol;
class VariableSymbol;
enum class StatementBlockKind : int;

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
    x(PatternCase) \
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
    x(RandSequence) \
    x(ProceduralChecker)
SLANG_ENUM(StatementKind, STATEMENT)
#undef STATEMENT

#define CASE_CONDITION(x) \
    x(Normal) \
    x(WildcardXOrZ) \
    x(WildcardJustZ) \
    x(Inside)
SLANG_ENUM(CaseStatementCondition, CASE_CONDITION)
#undef CASE_CONDITION

#define UNIQUE_PRIORITY(x) \
    x(None) \
    x(Unique) \
    x(Unique0) \
    x(Priority)
SLANG_ENUM(UniquePriorityCheck, UNIQUE_PRIORITY)
#undef UNIQUE_PRIORITY
// clang-format on

/// Various flags that control statement construction.
enum class StatementFlags {
    /// No specific flags specified.
    None = 0,

    /// Statement creation is happening inside a loop.
    InLoop = 1 << 0,

    /// Statement creation is happening inside a fork-join block.
    InForkJoin = 1 << 1,

    /// Statement creation is happening inside a randseq block.
    InRandSeq = 1 << 2,

    /// Statement creation is happening inside a for loop.
    InForLoop = 1 << 3,

    /// Statement creation has seen a timing-related error
    /// (and so should not issue another).
    HasTimingError = 1 << 4
};
SLANG_BITMASK(StatementFlags, HasTimingError)

/// The base class for all statements in SystemVerilog.
class SLANG_EXPORT Statement {
public:
    using StatementSyntax = syntax::StatementSyntax;

    /// The kind of statement; indicates the type of derived class.
    StatementKind kind;

    /// The syntax used to create this statement, if it was parsed from a source file.
    const StatementSyntax* syntax = nullptr;

    /// The source range of this statement, if it originated from source code.
    SourceRange sourceRange;

    Statement(const Statement&) = delete;
    Statement& operator=(const Statement&) = delete;

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

    /// Additional information passed along during statement creation.
    struct StatementContext {
        /// A series of block symbols that are expected to be used, in order,
        /// during the creation of the statement tree. Each statement created
        /// can pop blocks off the beginning of this list.
        std::span<const StatementBlockSymbol* const> blocks;

        /// Tracks various bits of context about where we are in statement creation.
        bitmask<StatementFlags> flags;

        /// A source range indicating the last event control observed
        /// while creating statements. This is only updated in always_ff blocks.
        SourceRange lastEventControl;

        /// The context used for creating statements.
        const ASTContext& rootAstContext;

        explicit StatementContext(const ASTContext& context) : rootAstContext(context) {}
        ~StatementContext();

        /// Attempts to match up the head of the block list with the given
        /// statement syntax node. If they match, the block symbol is popped
        /// and returned wrapped inside a BlockStatement.
        /// Otherwise nullptr is returned.
        const Statement* tryGetBlock(const ASTContext& context, const syntax::SyntaxNode& syntax);

        /// Observes that the given timing control has been created and checks it
        /// for correctness given the current statement context.
        void observeTiming(const TimingControl& timing);

        /// Records that we've entered a loop, and returns a guard that will
        /// revert back to the previous state on destruction.
        [[nodiscard]] auto enterLoop(bool isForLoop = false) {
            auto guard = ScopeGuard([this, savedFlags = flags] {
                auto savableFlags = StatementFlags::InLoop | StatementFlags::InForLoop;
                flags &= ~savableFlags;
                flags |= savedFlags & savableFlags;
            });

            flags |= StatementFlags::InLoop;
            if (isForLoop)
                flags |= StatementFlags::InForLoop;

            return guard;
        }
    };

    /// Binds a statement tree from the given syntax nodes.
    static const Statement& bind(const StatementSyntax& syntax, const ASTContext& context,
                                 StatementContext& stmtCtx, bool inList = false,
                                 bool labelHandled = false);

    /// Binds a statement tree that forms the contents of a block.
    static const Statement& bindBlock(const StatementBlockSymbol& block,
                                      const syntax::SyntaxNode& syntax, const ASTContext& context,
                                      StatementContext& stmtCtx);

    /// Binds a list of statement items.
    static const Statement& bindItems(const syntax::SyntaxList<syntax::SyntaxNode>& items,
                                      const ASTContext& context, StatementContext& stmtCtx);

    /// Creates any symbols declared by the given statement syntax, such as local variables.
    static std::span<const StatementBlockSymbol* const> createBlockItems(
        const Scope& scope, const StatementSyntax& syntax, bool labelHandled,
        SmallVector<const syntax::SyntaxNode*>& extraMembers);

    /// Creates any symbols declared by the given list of syntax nodes, such as local variables,
    /// and ignores any statement syntax nodes. The created symbols are added to the given scope.
    static std::span<const StatementBlockSymbol* const> createAndAddBlockItems(
        Scope& scope, const syntax::SyntaxList<syntax::SyntaxNode>& items);

    /// Creates any symbols declared by the given statement syntax, such as local variables.
    /// The created symbols are added to the given scope.
    static std::span<const StatementBlockSymbol* const> createAndAddBlockItems(
        Scope& scope, const StatementSyntax& syntax, bool labelHandled);

    /// @brief Casts this statement to the given concrete derived type.
    ///
    /// Asserts that the type is appropriate given this statement's kind.
    template<typename T>
    T& as() {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    /// @brief Casts this statement to the given concrete derived type.
    ///
    /// Asserts that the type is appropriate given this statement's kind.
    template<typename T>
    const T& as() const {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    /// @brief Tries to cast this statement to the given concrete derived type.
    ///
    /// If the type is not appropriate given this statement's kind, returns nullptr.
    template<typename T>
    T* as_if() {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<T*>(this);
    }

    /// @brief Tries to cast this statement to the given concrete derived type.
    ///
    /// If the type is not appropriate given this statement's kind, returns nullptr.
    template<typename T>
    const T* as_if() const {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<const T*>(this);
    }

    /// Visits this statement's concrete derived type via the provided visitor object.
    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor&& visitor, Args&&... args) const;

protected:
    Statement(StatementKind kind, SourceRange sourceRange) : kind(kind), sourceRange(sourceRange) {}

    static Statement& badStmt(Compilation& compilation, const Statement* stmt);
    static void bindScopeInitializers(const ASTContext& context,
                                      SmallVectorBase<const Statement*>& results);
};

/// @brief Represents an invalid statement
///
/// Usually generated and inserted into a statement tree due
/// to violation of language semantics or type checking.
class SLANG_EXPORT InvalidStatement : public Statement {
public:
    /// A wrapped sub-statement that is considered invalid.
    const Statement* child;

    explicit InvalidStatement(const Statement* child) :
        Statement(StatementKind::Invalid, SourceRange()), child(child) {}

    EvalResult evalImpl(EvalContext&) const { return EvalResult::Fail; }

    static bool isKind(StatementKind kind) { return kind == StatementKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;

    static const InvalidStatement Instance;
};

/// Represents an empty statement, used as a placeholder or an anchor for attributes.
class SLANG_EXPORT EmptyStatement : public Statement {
public:
    explicit EmptyStatement(SourceRange sourceRange) :
        Statement(StatementKind::Empty, sourceRange) {}

    EvalResult evalImpl(EvalContext&) const { return EvalResult::Success; }

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::Empty; }
};

/// Represents a list of statements.
class SLANG_EXPORT StatementList : public Statement {
public:
    /// The list of child statements.
    std::span<const Statement* const> list;

    StatementList(std::span<const Statement* const> list, SourceRange sourceRange) :
        Statement(StatementKind::List, sourceRange), list(list) {}

    EvalResult evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Statement& makeEmpty(Compilation& compilation);

    static bool isKind(StatementKind kind) { return kind == StatementKind::List; }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        for (auto stmt : list)
            stmt->visit(visitor);
    }
};

/// Represents a sequential or parallel block statement.
class SLANG_EXPORT BlockStatement : public Statement {
public:
    /// The block body.
    const Statement& body;

    /// An optional symbol associated with the block.
    const StatementBlockSymbol* blockSymbol = nullptr;

    /// The kind of statement block.
    StatementBlockKind blockKind;

    BlockStatement(const Statement& body, StatementBlockKind blockKind, SourceRange sourceRange) :
        Statement(StatementKind::Block, sourceRange), body(body), blockKind(blockKind) {}

    EvalResult evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::BlockStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx,
                                 bool addInitializers = false);

    static Statement& makeEmpty(Compilation& compilation);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Block; }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return body.visit(visitor);
    }
};

/// Represents a return statement.
class SLANG_EXPORT ReturnStatement : public Statement {
public:
    /// The return value expression, or nullptr if there is none.
    const Expression* expr;

    ReturnStatement(const Expression* expr, SourceRange sourceRange) :
        Statement(StatementKind::Return, sourceRange), expr(expr) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ReturnStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Return; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        if (expr)
            expr->visit(visitor);
    }
};

/// Represents a break statement.
class SLANG_EXPORT BreakStatement : public Statement {
public:
    explicit BreakStatement(SourceRange sourceRange) :
        Statement(StatementKind::Break, sourceRange) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::JumpStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(const ASTSerializer&) const {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::Break; }
};

/// Represents a continue statement.
class SLANG_EXPORT ContinueStatement : public Statement {
public:
    explicit ContinueStatement(SourceRange sourceRange) :
        Statement(StatementKind::Continue, sourceRange) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::JumpStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::Continue; }
};

/// Represents a disable statement.
class SLANG_EXPORT DisableStatement : public Statement {
public:
    /// The target of the disable.
    const Symbol& target;

    /// True if the target name was a hierarchical name.
    bool isHierarchical;

    DisableStatement(const Symbol& target, bool isHierarchical, SourceRange sourceRange) :
        Statement(StatementKind::Disable, sourceRange), target(target),
        isHierarchical(isHierarchical) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::DisableStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Disable; }
};

/// Represents a variable declaration in a statement context.
class SLANG_EXPORT VariableDeclStatement : public Statement {
public:
    /// The variable that was declared.
    const VariableSymbol& symbol;

    VariableDeclStatement(const VariableSymbol& symbol, SourceRange sourceRange) :
        Statement(StatementKind::VariableDeclaration, sourceRange), symbol(symbol) {}

    EvalResult evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::VariableDeclaration; }
};

/// Represents a conditional statement.
class SLANG_EXPORT ConditionalStatement : public Statement {
public:
    /// A condition.
    struct Condition {
        /// The condition expression.
        not_null<const Expression*> expr;

        /// An optional pattern associated with the condition.
        const Pattern* pattern = nullptr;
    };

    /// The list of conditions that control the statement.
    std::span<const Condition> conditions;

    /// The body for if-true evaluation.
    const Statement& ifTrue;

    /// The optional body for else-false evaluation.
    const Statement* ifFalse;

    /// An optional unique or priority check that should be applied to the condition.
    UniquePriorityCheck check;

    ConditionalStatement(std::span<const Condition> conditions, UniquePriorityCheck check,
                         const Statement& ifTrue, const Statement* ifFalse,
                         SourceRange sourceRange) :
        Statement(StatementKind::Conditional, sourceRange), conditions(conditions), ifTrue(ifTrue),
        ifFalse(ifFalse), check(check) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ConditionalStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Conditional; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto& cond : conditions) {
            cond.expr->visit(visitor);
            if (cond.pattern)
                cond.pattern->visit(visitor);
        }
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        ifTrue.visit(visitor);
        if (ifFalse)
            ifFalse->visit(visitor);
    }
};

/// Represents a case statement.
class SLANG_EXPORT CaseStatement : public Statement {
public:
    /// A group of items in a case statement.
    struct ItemGroup {
        /// A list of expression that can match this group.
        std::span<const Expression* const> expressions;

        /// The group statement body.
        not_null<const Statement*> stmt;
    };

    /// The controlling case condition.
    const Expression& expr;

    /// A list of items to match against.
    std::span<ItemGroup const> items;

    /// An optional default case item that applies if no items match.
    const Statement* defaultCase = nullptr;

    /// The kind of case condition to evaluate.
    CaseStatementCondition condition;

    /// An optional unique or priority check that should be applied to the condition.
    UniquePriorityCheck check;

    CaseStatement(CaseStatementCondition condition, UniquePriorityCheck check,
                  const Expression& expr, std::span<ItemGroup const> items,
                  const Statement* defaultCase, SourceRange sourceRange) :
        Statement(StatementKind::Case, sourceRange), expr(expr), items(items),
        defaultCase(defaultCase), condition(condition), check(check) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::CaseStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

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

/// Represents a pattern case statement.
class SLANG_EXPORT PatternCaseStatement : public Statement {
public:
    /// A group of items in a pattern case statement.
    struct ItemGroup {
        /// The pattern that controls whether the group matches.
        not_null<const Pattern*> pattern;

        /// An optional filter condition.
        const Expression* filter;

        /// The statement to execute if a match is found.
        not_null<const Statement*> stmt;
    };

    /// The controlling case condition.
    const Expression& expr;

    /// A list of items to match against.
    std::span<ItemGroup const> items;

    /// An optional default case item that applies if no items match.
    const Statement* defaultCase = nullptr;

    /// The kind of case condition to evaluate.
    CaseStatementCondition condition;

    /// An optional unique or priority check that should be applied to the condition.
    UniquePriorityCheck check;

    PatternCaseStatement(CaseStatementCondition condition, UniquePriorityCheck check,
                         const Expression& expr, std::span<ItemGroup const> items,
                         const Statement* defaultCase, SourceRange sourceRange) :
        Statement(StatementKind::PatternCase, sourceRange), expr(expr), items(items),
        defaultCase(defaultCase), condition(condition), check(check) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::CaseStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::PatternCase; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
        for (auto& item : items) {
            item.pattern->visit(visitor);
            if (item.filter)
                item.filter->visit(visitor);
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

/// Represents a `for` loop statement.
class SLANG_EXPORT ForLoopStatement : public Statement {
public:
    /// A list of variable initializers (mutually exclusive with @a loopVars )
    std::span<const Expression* const> initializers;

    /// A list of variables declared in the for loop (mutually exclusive with @a initializers )
    std::span<const VariableSymbol* const> loopVars;

    /// An optional expression that controls when the loop stops.
    const Expression* stopExpr;

    /// A list of steps to apply on each iteration.
    std::span<const Expression* const> steps;

    /// The body of the loop.
    const Statement& body;

    ForLoopStatement(std::span<const Expression* const> initializers, const Expression* stopExpr,
                     std::span<const Expression* const> steps, const Statement& body,
                     SourceRange sourceRange) :
        Statement(StatementKind::ForLoop, sourceRange), initializers(initializers),
        stopExpr(stopExpr), steps(steps), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ForLoopStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

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
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return body.visit(visitor);
    }
};

/// Represents a `repeat` loop statement.
class SLANG_EXPORT RepeatLoopStatement : public Statement {
public:
    /// An expression that controls the number of times to repeat the loop.
    const Expression& count;

    /// The body of the loop.
    const Statement& body;

    RepeatLoopStatement(const Expression& count, const Statement& body, SourceRange sourceRange) :
        Statement(StatementKind::RepeatLoop, sourceRange), count(count), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::LoopStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::RepeatLoop; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return count.visit(visitor);
    }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return body.visit(visitor);
    }
};

/// Represents a `foreach` loop statement.
class SLANG_EXPORT ForeachLoopStatement : public Statement {
public:
    /// Describes one dimension that will be iterated by the loop.
    struct LoopDim {
        /// The static range of the dimension, or nullopt if the
        /// dimension is dynamically sized.
        std::optional<ConstantRange> range;

        /// The loop variable for this dimension, or nullptr if
        /// the dimension is being skipped.
        const IteratorSymbol* loopVar = nullptr;
    };

    /// An expression indicating the array to iterate.
    const Expression& arrayRef;

    /// A list of dimensions iterated by the loop.
    std::span<const LoopDim> loopDims;

    /// The body of the loop.
    const Statement& body;

    ForeachLoopStatement(const Expression& arrayRef, std::span<const LoopDim> loopDims,
                         const Statement& body, SourceRange sourceRange) :
        Statement(StatementKind::ForeachLoop, sourceRange), arrayRef(arrayRef), loopDims(loopDims),
        body(body) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ForeachLoopStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static const Expression* buildLoopDims(const syntax::ForeachLoopListSyntax& loopList,
                                           ASTContext& context, SmallVectorBase<LoopDim>& dims);

    static bool isKind(StatementKind kind) { return kind == StatementKind::ForeachLoop; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return arrayRef.visit(visitor);
    }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return body.visit(visitor);
    }

private:
    EvalResult evalRecursive(EvalContext& context, const ConstantValue& cv,
                             std::span<const LoopDim> loopDims) const;
};

/// Represents a `while` loop statement.
class SLANG_EXPORT WhileLoopStatement : public Statement {
public:
    /// A condition that controls whether the loop continues to execute.
    const Expression& cond;

    /// The body of the loop.
    const Statement& body;

    WhileLoopStatement(const Expression& cond, const Statement& body, SourceRange sourceRange) :
        Statement(StatementKind::WhileLoop, sourceRange), cond(cond), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::LoopStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::WhileLoop; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return cond.visit(visitor);
    }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return body.visit(visitor);
    }
};

/// Represents a `do` `while` loop statement.
class SLANG_EXPORT DoWhileLoopStatement : public Statement {
public:
    /// A condition that controls whether the loop continues to execute.
    const Expression& cond;

    /// The body of the loop.
    const Statement& body;

    DoWhileLoopStatement(const Expression& cond, const Statement& body, SourceRange sourceRange) :
        Statement(StatementKind::DoWhileLoop, sourceRange), cond(cond), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::DoWhileStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::DoWhileLoop; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return cond.visit(visitor);
    }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return body.visit(visitor);
    }
};

/// Represents a `forever` loop statement.
class SLANG_EXPORT ForeverLoopStatement : public Statement {
public:
    /// The body of the loop.
    const Statement& body;

    ForeverLoopStatement(const Statement& body, SourceRange sourceRange) :
        Statement(StatementKind::ForeverLoop, sourceRange), body(body) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ForeverStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ForeverLoop; }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return body.visit(visitor);
    }
};

/// Represents an expression that is executed as a standalone statement.
class SLANG_EXPORT ExpressionStatement : public Statement {
public:
    /// The expression to execute.
    const Expression& expr;

    ExpressionStatement(const Expression& expr, SourceRange sourceRange) :
        Statement(StatementKind::ExpressionStatement, sourceRange), expr(expr) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ExpressionStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::VoidCastedCallStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ExpressionStatement; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return expr.visit(visitor);
    }
};

/// Represents a statement that has an associated timing control.
class SLANG_EXPORT TimedStatement : public Statement {
public:
    /// The timing that controls the statement.
    const TimingControl& timing;

    /// The statement.
    const Statement& stmt;

    TimedStatement(const TimingControl& timing, const Statement& stmt, SourceRange sourceRange) :
        Statement(StatementKind::Timed, sourceRange), timing(timing), stmt(stmt) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::TimingControlStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Timed; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return timing.visit(visitor);
    }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return stmt.visit(visitor);
    }
};

/// Represents an immediate assertion statement.
class SLANG_EXPORT ImmediateAssertionStatement : public Statement {
public:
    /// The assertion condition.
    const Expression& cond;

    /// An optional action to take if the assertion passes.
    const Statement* ifTrue;

    /// An optional action to take if the assertion fails.
    const Statement* ifFalse;

    /// The kind of assertion.
    AssertionKind assertionKind;

    /// True if the assertion is a "deferred" immediate assertion.
    bool isDeferred;

    /// True if the assertion is declared "final".
    bool isFinal;

    ImmediateAssertionStatement(AssertionKind assertionKind, const Expression& cond,
                                const Statement* ifTrue, const Statement* ifFalse, bool isDeferred,
                                bool isFinal, SourceRange sourceRange) :
        Statement(StatementKind::ImmediateAssertion, sourceRange), cond(cond), ifTrue(ifTrue),
        ifFalse(ifFalse), assertionKind(assertionKind), isDeferred(isDeferred), isFinal(isFinal) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ImmediateAssertionStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ImmediateAssertion; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return cond.visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        if (ifTrue)
            ifTrue->visit(visitor);
        if (ifFalse)
            ifFalse->visit(visitor);
    }
};

/// Represents a concurrent assertion statement.
class SLANG_EXPORT ConcurrentAssertionStatement : public Statement {
public:
    /// The assertion body.
    const AssertionExpr& propertySpec;

    /// An optional action to take if the assertion passes.
    const Statement* ifTrue;

    /// An optional action to take if the assertion fails.
    const Statement* ifFalse;

    /// The kind of assertion.
    AssertionKind assertionKind;

    ConcurrentAssertionStatement(AssertionKind assertionKind, const AssertionExpr& propertySpec,
                                 const Statement* ifTrue, const Statement* ifFalse,
                                 SourceRange sourceRange) :
        Statement(StatementKind::ConcurrentAssertion, sourceRange), propertySpec(propertySpec),
        ifTrue(ifTrue), ifFalse(ifFalse), assertionKind(assertionKind) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ConcurrentAssertionStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ConcurrentAssertion; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return propertySpec.visit(visitor);
    }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        if (ifTrue)
            ifTrue->visit(visitor);
        if (ifFalse)
            ifFalse->visit(visitor);
    }
};

/// Represents a `disable fork` statement.
class SLANG_EXPORT DisableForkStatement : public Statement {
public:
    explicit DisableForkStatement(SourceRange sourceRange) :
        Statement(StatementKind::DisableFork, sourceRange) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::DisableForkStatementSyntax& syntax);

    void serializeTo(const ASTSerializer&) const {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::DisableFork; }
};

/// Represents a `wait` statement.
class SLANG_EXPORT WaitStatement : public Statement {
public:
    /// The wait condition.
    const Expression& cond;

    /// The statement to execute after the condition passes.
    const Statement& stmt;

    WaitStatement(const Expression& cond, const Statement& stmt, SourceRange sourceRange) :
        Statement(StatementKind::Wait, sourceRange), cond(cond), stmt(stmt) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::WaitStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::Wait; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return cond.visit(visitor);
    }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return stmt.visit(visitor);
    }
};

/// Represents a `wait fork` statement.
class SLANG_EXPORT WaitForkStatement : public Statement {
public:
    explicit WaitForkStatement(SourceRange sourceRange) :
        Statement(StatementKind::WaitFork, sourceRange) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::WaitForkStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(const ASTSerializer&) const {}

    static bool isKind(StatementKind kind) { return kind == StatementKind::WaitFork; }
};

/// Represents a `wait_order` statement.
class SLANG_EXPORT WaitOrderStatement : public Statement {
public:
    /// A list of expressions denoting the events on which to wait, in order.
    std::span<const Expression* const> events;

    /// An optional statement to execute if the events all trigger in order.
    const Statement* ifTrue;

    /// An optional statement to execute if any of the events did not trigger in order.
    const Statement* ifFalse;

    WaitOrderStatement(std::span<const Expression* const> events, const Statement* ifTrue,
                       const Statement* ifFalse, SourceRange sourceRange) :
        Statement(StatementKind::WaitOrder, sourceRange), events(events), ifTrue(ifTrue),
        ifFalse(ifFalse) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::WaitOrderStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

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

/// Represents an event triggering statement.
class SLANG_EXPORT EventTriggerStatement : public Statement {
public:
    /// An expression denoting the target event to trigger.
    const Expression& target;

    /// An optional timing control delaying the triggering.
    const TimingControl* timing;

    /// True if the event trigger is a non-blocking operation, and false otherwise.
    bool isNonBlocking;

    EventTriggerStatement(const Expression& target, const TimingControl* timing, bool isNonBlocking,
                          SourceRange sourceRange) :
        Statement(StatementKind::EventTrigger, sourceRange), target(target), timing(timing),
        isNonBlocking(isNonBlocking) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::EventTriggerStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::EventTrigger; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        target.visit(visitor);
        if (timing)
            timing->visit(visitor);
    }
};

/// Represents a procedural `assign` statement.
class SLANG_EXPORT ProceduralAssignStatement : public Statement {
public:
    /// The assignment expression.
    const Expression& assignment;

    /// True if this is a `force` statement and false if it's an `assign` statement.
    bool isForce;

    ProceduralAssignStatement(const Expression& assignment, bool isForce, SourceRange sourceRange) :
        Statement(StatementKind::ProceduralAssign, sourceRange), assignment(assignment),
        isForce(isForce) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ProceduralAssignStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ProceduralAssign; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return assignment.visit(visitor);
    }
};

/// Represents a procedural `deassign` statement.
class SLANG_EXPORT ProceduralDeassignStatement : public Statement {
public:
    /// The target lvalue to deassign.
    const Expression& lvalue;

    /// True if this is a `release` statement and false if it's a `deassign` statement.
    bool isRelease;

    ProceduralDeassignStatement(const Expression& lvalue, bool isRelease, SourceRange sourceRange) :
        Statement(StatementKind::ProceduralDeassign, sourceRange), lvalue(lvalue),
        isRelease(isRelease) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::ProceduralDeassignStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ProceduralDeassign; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return lvalue.visit(visitor);
    }
};

/// Represents a `randcase` statement.
class SLANG_EXPORT RandCaseStatement : public Statement {
public:
    /// An item in the randcase list.
    struct Item {
        /// The expression to match against.
        not_null<const Expression*> expr;

        /// The statement to execute upon a match.
        not_null<const Statement*> stmt;
    };

    /// The list of items to pick from.
    std::span<Item const> items;

    RandCaseStatement(std::span<Item const> items, SourceRange sourceRange) :
        Statement(StatementKind::RandCase, sourceRange), items(items) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::RandCaseStatementSyntax& syntax,
                                 const ASTContext& context, StatementContext& stmtCtx);

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

/// Represents a `randsequence` statement.
class SLANG_EXPORT RandSequenceStatement : public Statement {
public:
    /// A pointer to the first production that starts the random sequence,
    /// or nullptr if the sequence is empty.
    const RandSeqProductionSymbol* firstProduction;

    RandSequenceStatement(const RandSeqProductionSymbol* firstProduction, SourceRange sourceRange) :
        Statement(StatementKind::RandSequence, sourceRange), firstProduction(firstProduction) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::RandSequenceStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::RandSequence; }
};

/// Represents a procedural checker instantiation statement.
class SLANG_EXPORT ProceduralCheckerStatement : public Statement {
public:
    /// A list of checkers to instantiate.
    std::span<const Symbol* const> instances;

    ProceduralCheckerStatement(std::span<const Symbol* const> instances, SourceRange sourceRange) :
        Statement(StatementKind::ProceduralChecker, sourceRange), instances(instances) {}

    EvalResult evalImpl(EvalContext& context) const;

    static Statement& fromSyntax(Compilation& compilation,
                                 const syntax::CheckerInstanceStatementSyntax& syntax,
                                 const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(StatementKind kind) { return kind == StatementKind::ProceduralChecker; }
};

} // namespace slang::ast
