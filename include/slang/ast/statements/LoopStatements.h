//------------------------------------------------------------------------------
//! @file LoopStatements.h
//! @brief Loop statement definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Statement.h"

namespace slang::ast {

class IteratorSymbol;
class VariableSymbol;

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

} // namespace slang::ast
