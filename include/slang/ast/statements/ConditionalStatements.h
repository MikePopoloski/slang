//------------------------------------------------------------------------------
//! @file ConditionalStatements.h
//! @brief Conditional / case statement definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Statement.h"

namespace slang::ast {

// clang-format off
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

} // namespace slang::ast
