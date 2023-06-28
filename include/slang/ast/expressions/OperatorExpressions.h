//------------------------------------------------------------------------------
//! @file OperatorExpressions.h
//! @brief Definitions for operator expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Expression.h"
#include "slang/ast/Patterns.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

class Pattern;

/// Represents a unary operator expression.
class SLANG_EXPORT UnaryExpression : public Expression {
public:
    UnaryOperator op;

    UnaryExpression(UnaryOperator op, const Type& type, Expression& operand,
                    SourceRange sourceRange) :
        Expression(ExpressionKind::UnaryOp, type, sourceRange),
        op(op), operand_(&operand) {}

    const Expression& operand() const { return *operand_; }
    Expression& operand() { return *operand_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool propagateType(const ASTContext& context, const Type& newType);
    std::optional<bitwidth_t> getEffectiveWidthImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::PrefixUnaryExpressionSyntax& syntax,
                                  const ASTContext& context);

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::PostfixUnaryExpressionSyntax& syntax,
                                  const ASTContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::UnaryOp; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return operand().visit(visitor);
    }

private:
    Expression* operand_;
};

/// Represents a binary operator expression.
class SLANG_EXPORT BinaryExpression : public Expression {
public:
    BinaryOperator op;

    BinaryExpression(BinaryOperator op, const Type& type, Expression& left, Expression& right,
                     SourceRange sourceRange) :
        Expression(ExpressionKind::BinaryOp, type, sourceRange),
        op(op), left_(&left), right_(&right) {}

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool propagateType(const ASTContext& context, const Type& newType);
    std::optional<bitwidth_t> getEffectiveWidthImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::BinaryExpressionSyntax& syntax,
                                  const ASTContext& context);

    static Expression& fromComponents(Expression& lhs, Expression& rhs, BinaryOperator op,
                                      SourceLocation opLoc, SourceRange sourceRange,
                                      const ASTContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::BinaryOp; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        left().visit(visitor);
        right().visit(visitor);
    }

private:
    Expression* left_;
    Expression* right_;
};

/// Represents a conditional operator expression.
class SLANG_EXPORT ConditionalExpression : public Expression {
public:
    struct Condition {
        not_null<const Expression*> expr;
        const Pattern* pattern = nullptr;
    };
    std::span<const Condition> conditions;

    ConditionalExpression(const Type& type, std::span<const Condition> conditions, Expression& left,
                          Expression& right, SourceRange sourceRange) :
        Expression(ExpressionKind::ConditionalOp, type, sourceRange),
        conditions(conditions), left_(&left), right_(&right) {}

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool propagateType(const ASTContext& context, const Type& newType);
    std::optional<bitwidth_t> getEffectiveWidthImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::ConditionalExpressionSyntax& syntax,
                                  const ASTContext& context, const Type* assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::ConditionalOp; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto& cond : conditions) {
            cond.expr->visit(visitor);
            if (cond.pattern)
                cond.pattern->visit(visitor);
        }

        left().visit(visitor);
        right().visit(visitor);
    }

private:
    Expression* left_;
    Expression* right_;
};

/// Represents a set membership operator expression.
class SLANG_EXPORT InsideExpression : public Expression {
public:
    InsideExpression(const Type& type, const Expression& left,
                     std::span<const Expression* const> rangeList, SourceRange sourceRange) :
        Expression(ExpressionKind::Inside, type, sourceRange),
        left_(&left), rangeList_(rangeList) {}

    const Expression& left() const { return *left_; }

    std::span<const Expression* const> rangeList() const { return rangeList_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::InsideExpressionSyntax& syntax,
                                  const ASTContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Inside; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        left().visit(visitor);
        for (auto range : rangeList())
            range->visit(visitor);
    }

private:
    const Expression* left_;
    std::span<const Expression* const> rangeList_;
};

/// Represents a concatenation expression.
class SLANG_EXPORT ConcatenationExpression : public Expression {
public:
    ConcatenationExpression(const Type& type, std::span<const Expression* const> operands,
                            SourceRange sourceRange) :
        Expression(ExpressionKind::Concatenation, type, sourceRange),
        operands_(operands) {}

    std::span<const Expression* const> operands() const { return operands_; }

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::ConcatenationExpressionSyntax& syntax,
                                  const ASTContext& context, const Type* assignmentTarget);

    static Expression& fromEmpty(Compilation& compilation,
                                 const syntax::EmptyQueueExpressionSyntax& syntax,
                                 const ASTContext& context, const Type* assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Concatenation; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto op : operands())
            op->visit(visitor);
    }

private:
    std::span<const Expression* const> operands_;
};

/// Represents a replication expression.
class SLANG_EXPORT ReplicationExpression : public Expression {
public:
    ReplicationExpression(const Type& type, const Expression& count, Expression& concat,
                          SourceRange sourceRange) :
        Expression(ExpressionKind::Replication, type, sourceRange),
        count_(&count), concat_(&concat) {}

    const Expression& count() const { return *count_; }

    const Expression& concat() const { return *concat_; }
    Expression& concat() { return *concat_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::MultipleConcatenationExpressionSyntax& syntax,
                                  const ASTContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Replication; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        count().visit(visitor);
        concat().visit(visitor);
    }

private:
    const Expression* count_;
    Expression* concat_;
};

/// Represents a streaming concatenation.
class SLANG_EXPORT StreamingConcatenationExpression : public Expression {
public:
    /// The size of the blocks to slice and reorder: if 0, this is a left-to-right
    /// concatenation. Otherwise, it's a right-to-left concatenation.
    const size_t sliceSize;

    struct StreamExpression {
        not_null<const Expression*> operand;
        const Expression* withExpr;
        std::optional<bitwidth_t> constantWithWidth;
    };

    StreamingConcatenationExpression(const Type& type, size_t sliceSize,
                                     std::span<const StreamExpression> streams,
                                     SourceRange sourceRange) :
        Expression(ExpressionKind::Streaming, type, sourceRange),
        sliceSize(sliceSize), streams_(streams) {}

    bool isFixedSize() const;
    size_t bitstreamWidth() const;

    std::span<const StreamExpression> streams() const { return streams_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::StreamingConcatenationExpressionSyntax& syntax,
                                  const ASTContext& context, const Type* assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Streaming; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto& stream : streams()) {
            stream.operand->visit(visitor);
            if (stream.withExpr)
                stream.withExpr->visit(visitor);
        }
    }

private:
    std::span<const StreamExpression> streams_;
};

/// Denotes a range of values by providing expressions for the lower and upper
/// bounds of the range. This expression needs special handling in the various
/// places that allow it, since it doesn't really have a type.
class SLANG_EXPORT OpenRangeExpression : public Expression {
public:
    OpenRangeExpression(const Type& type, Expression& left, Expression& right,
                        SourceRange sourceRange) :
        Expression(ExpressionKind::OpenRange, type, sourceRange),
        left_(&left), right_(&right) {}

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool propagateType(const ASTContext& context, const Type& newType);

    ConstantValue checkInside(EvalContext& context, const ConstantValue& val) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& comp,
                                  const syntax::OpenRangeExpressionSyntax& syntax,
                                  const ASTContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::OpenRange; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        left().visit(visitor);
        right().visit(visitor);
    }

private:
    Expression* left_;
    Expression* right_;
};

} // namespace slang::ast
