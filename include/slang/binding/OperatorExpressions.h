//------------------------------------------------------------------------------
//! @file OperatorExpressions.h
//! @brief Definitions for operator expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"

namespace slang {

class Pattern;
struct PostfixUnaryExpressionSyntax;
struct PrefixUnaryExpressionSyntax;

/// Represents a unary operator expression.
class UnaryExpression : public Expression {
public:
    UnaryOperator op;

    UnaryExpression(UnaryOperator op, const Type& type, Expression& operand,
                    SourceRange sourceRange) :
        Expression(ExpressionKind::UnaryOp, type, sourceRange),
        op(op), operand_(&operand) {}

    const Expression& operand() const { return *operand_; }
    Expression& operand() { return *operand_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool propagateType(const BindContext& context, const Type& newType);
    optional<bitwidth_t> getEffectiveWidthImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const PrefixUnaryExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& fromSyntax(Compilation& compilation,
                                  const PostfixUnaryExpressionSyntax& syntax,
                                  const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::UnaryOp; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        operand().visit(visitor);
    }

private:
    Expression* operand_;
};

struct BinaryExpressionSyntax;

/// Represents a binary operator expression.
class BinaryExpression : public Expression {
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
    bool propagateType(const BindContext& context, const Type& newType);
    optional<bitwidth_t> getEffectiveWidthImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const BinaryExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& fromComponents(Expression& lhs, Expression& rhs, BinaryOperator op,
                                      SourceLocation opLoc, SourceRange sourceRange,
                                      const BindContext& context);

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

struct ConditionalExpressionSyntax;

/// Represents a conditional operator expression.
class ConditionalExpression : public Expression {
public:
    struct Condition {
        not_null<const Expression*> expr;
        const Pattern* pattern = nullptr;
    };
    span<const Condition> conditions;

    ConditionalExpression(const Type& type, span<const Condition> conditions, Expression& left,
                          Expression& right, SourceRange sourceRange) :
        Expression(ExpressionKind::ConditionalOp, type, sourceRange),
        conditions(conditions), left_(&left), right_(&right) {}

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool propagateType(const BindContext& context, const Type& newType);
    optional<bitwidth_t> getEffectiveWidthImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const ConditionalExpressionSyntax& syntax,
                                  const BindContext& context, const Type* assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::ConditionalOp; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto& cond : conditions)
            cond.expr->visit(visitor);

        left().visit(visitor);
        right().visit(visitor);
    }

private:
    Expression* left_;
    Expression* right_;
};

struct InsideExpressionSyntax;

/// Represents a set membership operator expression.
class InsideExpression : public Expression {
public:
    InsideExpression(const Type& type, const Expression& left,
                     span<const Expression* const> rangeList, SourceRange sourceRange) :
        Expression(ExpressionKind::Inside, type, sourceRange),
        left_(&left), rangeList_(rangeList) {}

    const Expression& left() const { return *left_; }

    span<const Expression* const> rangeList() const { return rangeList_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const InsideExpressionSyntax& syntax,
                                  const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Inside; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        left().visit(visitor);
        for (auto range : rangeList())
            range->visit(visitor);
    }

private:
    const Expression* left_;
    span<const Expression* const> rangeList_;
};

struct ConcatenationExpressionSyntax;
struct EmptyQueueExpressionSyntax;

/// Represents a concatenation expression.
class ConcatenationExpression : public Expression {
public:
    ConcatenationExpression(const Type& type, span<const Expression* const> operands,
                            SourceRange sourceRange) :
        Expression(ExpressionKind::Concatenation, type, sourceRange),
        operands_(operands) {}

    span<const Expression* const> operands() const { return operands_; }

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const ConcatenationExpressionSyntax& syntax,
                                  const BindContext& context, const Type* assignmentTarget);

    static Expression& fromEmpty(Compilation& compilation, const EmptyQueueExpressionSyntax& syntax,
                                 const BindContext& context, const Type* assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Concatenation; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto op : operands())
            op->visit(visitor);
    }

private:
    span<const Expression* const> operands_;
};

struct MultipleConcatenationExpressionSyntax;

/// Represents a replication expression.
class ReplicationExpression : public Expression {
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
                                  const MultipleConcatenationExpressionSyntax& syntax,
                                  const BindContext& context);

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

struct StreamingConcatenationExpressionSyntax;

/// @cond NOPE
#define RANGE(x) x(Simple) x(IndexedUp) x(IndexedDown) x(Bit)
ENUM(WithRangeKind, RANGE) // RangeSelectionKind + Bit
#undef RANGE
/// @endcond

/// Represents a streaming concatenation.
class StreamingConcatenationExpression : public Expression {
public:
    /// The size of the blocks to slice and reorder: if 0, this is a left-to-right
    /// concatenation. Otherwise, it's a right-to-left concatenation.
    const size_t sliceSize;

    struct WithExpression {
        WithRangeKind kind;
        not_null<const Expression*> left;
        const Expression* right;
        optional<int32_t> width; // elaboration-time constant width
    };

    struct StreamExpression {
        not_null<const Expression*> operand;
        const WithExpression* with;
    };

    StreamingConcatenationExpression(const Type& type, size_t sliceSize,
                                     span<const StreamExpression* const> streams,
                                     SourceRange sourceRange) :
        Expression(ExpressionKind::Streaming, type, sourceRange),
        sliceSize(sliceSize), streams_(streams) {}

    span<const StreamExpression* const> streams() const { return streams_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const StreamingConcatenationExpressionSyntax& syntax,
                                  const BindContext& context, const Type* assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Streaming; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto stream : streams()) {
            stream->operand->visit(visitor);
            if (stream->with) {
                stream->with->left->visit(visitor);
                if (stream->with->right)
                    stream->with->right->visit(visitor);
            }
        }
    }

    bool isFixedSize() const;
    size_t bitstreamWidth() const;

private:
    span<const StreamExpression* const> streams_;
};

struct OpenRangeExpressionSyntax;

/// Denotes a range of values by providing expressions for the lower and upper
/// bounds of the range. This expression needs special handling in the various
/// places that allow it, since it doesn't really have a type.
class OpenRangeExpression : public Expression {
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
    bool propagateType(const BindContext& context, const Type& newType);

    ConstantValue checkInside(EvalContext& context, const ConstantValue& val) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& comp, const OpenRangeExpressionSyntax& syntax,
                                  const BindContext& context);

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

} // namespace slang
