//------------------------------------------------------------------------------
//! @file Statement.h
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
class StatementBlockSymbol;
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

    static BlockStatement& makeEmpty(Compilation& compilation);

    static bool isKind(StatementKind kind) { return kind == StatementKind::Block; }

    template<typename TVisitor>
    decltype(auto) visitStmts(TVisitor&& visitor) const {
        return body.visit(visitor);
    }
};

} // namespace slang::ast
