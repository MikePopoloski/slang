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
#include "slang/ast/expressions/Operator.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

class Pattern;

/// Represents a unary operator expression.
class SLANG_EXPORT UnaryExpression : public Expression {
public:
    /// The operator.
    UnaryOperator op;

    /// The source range of the operator token.
    SourceRange opRange;

    UnaryExpression(UnaryOperator op, const Type& type, Expression& operand,
                    SourceRange sourceRange, SourceRange opRange) :
        Expression(ExpressionKind::UnaryOp, type, sourceRange), op(op), opRange(opRange),
        operand_(&operand) {}

    /// @returns the operand
    const Expression& operand() const { return *operand_; }

    /// @returns the operand
    Expression& operand() { return *operand_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool propagateType(const ASTContext& context, const Type& newType, SourceRange opRange,
                       ConversionKind conversionKind);
    std::optional<bitwidth_t> getEffectiveWidthImpl() const;
    EffectiveSign getEffectiveSignImpl(bool isForConversion) const;

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
private:
    Expression* left_;
    Expression* right_;

public:
    /// The operator.
    BinaryOperator op;

    /// The source range of the operator token.
    SourceRange opRange;

    BinaryExpression(BinaryOperator op, const Type& type, Expression& left, Expression& right,
                     SourceRange sourceRange, SourceRange opRange) :
        Expression(ExpressionKind::BinaryOp, type, sourceRange), left_(&left), right_(&right),
        op(op), opRange(opRange) {}

    /// @returns the left-hand side of the expression
    const Expression& left() const { return *left_; }

    /// @returns the left-hand side of the expression
    Expression& left() { return *left_; }

    /// @returns the right-hand side of the expression
    const Expression& right() const { return *right_; }

    /// @returns the right-hand side of the expression
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool propagateType(const ASTContext& context, const Type& newType, SourceRange opRange,
                       ConversionKind conversionKind);
    std::optional<bitwidth_t> getEffectiveWidthImpl() const;
    EffectiveSign getEffectiveSignImpl(bool isForConversion) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::BinaryExpressionSyntax& syntax,
                                  const ASTContext& context);

    static Expression& fromComponents(Expression& lhs, Expression& rhs, BinaryOperator op,
                                      SourceRange opRange, SourceRange sourceRange,
                                      const ASTContext& context);

    static void analyzeOpTypes(const Type& clt, const Type& crt, const Type& originalLt,
                               const Type& originalRt, const Expression& lhs, const Expression& rhs,
                               const ASTContext& context, SourceRange opRange, DiagCode code,
                               bool isComparison, std::optional<std::string_view> extraDiagArg);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::BinaryOp; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        left().visit(visitor);
        right().visit(visitor);
    }
};

/// Represents a conditional operator expression.
class SLANG_EXPORT ConditionalExpression : public Expression {
public:
    /// A condition.
    struct Condition {
        /// The expression representing the condition.
        not_null<const Expression*> expr;

        /// An optional pattern to apply to the condition.
        const Pattern* pattern = nullptr;
    };

    /// The list of conditions controlling the expression.
    std::span<const Condition> conditions;

    /// The location of the conditional '?' operator token.
    SourceLocation opLoc;

    ConditionalExpression(const Type& type, std::span<const Condition> conditions,
                          SourceLocation opLoc, Expression& left, Expression& right,
                          SourceRange sourceRange, bool isConst, bool isTrue) :
        Expression(ExpressionKind::ConditionalOp, type, sourceRange), conditions(conditions),
        opLoc(opLoc), left_(&left), right_(&right), isConst(isConst), isTrue(isTrue) {}

    /// @returns the left-hand side operand
    const Expression& left() const { return *left_; } // NOLINT

    /// @returns the left-hand side operand
    Expression& left() { return *left_; }

    /// @returns the right-hand side operand
    const Expression& right() const { return *right_; } // NOLINT

    /// @returns the right-hand side operand
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool propagateType(const ASTContext& context, const Type& newType, SourceRange opRange,
                       ConversionKind conversionKind);
    std::optional<bitwidth_t> getEffectiveWidthImpl() const;
    EffectiveSign getEffectiveSignImpl(bool isForConversion) const;

    /// If the condition for this expression is a known constant value,
    /// this method returns the side of the expression that will be selected
    /// (i.e. the left or right expression). Otherwise returns nullptr.
    const Expression* knownSide() const { return isConst ? (isTrue ? left_ : right_) : nullptr; }

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
    bool isConst;
    bool isTrue;
};

/// Represents a set membership operator expression.
class SLANG_EXPORT InsideExpression : public Expression {
public:
    InsideExpression(const Type& type, const Expression& left,
                     std::span<const Expression* const> rangeList, SourceRange sourceRange) :
        Expression(ExpressionKind::Inside, type, sourceRange), left_(&left), rangeList_(rangeList) {
    }

    /// @returns the left-hand side operand
    const Expression& left() const { return *left_; }

    /// @returns the lsit of ranges denoting the set to check for membership.
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
        Expression(ExpressionKind::Concatenation, type, sourceRange), operands_(operands) {}

    /// @returns the list of operands in the concatenation
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
        Expression(ExpressionKind::Replication, type, sourceRange), count_(&count),
        concat_(&concat) {}

    /// @returns the expression denoting the number of times to replicate
    const Expression& count() const { return *count_; }

    /// @returns the concatenation that will be replicated
    const Expression& concat() const { return *concat_; }

    /// @returns the concatenation that will be replicated
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
    /// A single stream expression within the concatenation.
    struct StreamExpression {
        /// The operand expression.
        not_null<const Expression*> operand;

        /// An optional `with` clause selecting a range for the operand.
        const Expression* withExpr;

        /// If there is a @a withExpr and it has a constant value, this is
        /// the width of the selection.
        std::optional<bitwidth_t> constantWithWidth;
    };

    StreamingConcatenationExpression(const Type& type, uint64_t sliceSize, uint64_t bitstreamWidth,
                                     std::span<const StreamExpression> streams,
                                     SourceRange sourceRange) :
        Expression(ExpressionKind::Streaming, type, sourceRange), streams_(streams),
        sliceSize(sliceSize), bitstreamWidth(bitstreamWidth) {}

    /// @returns true if the expression has a fixed size, and false if it
    /// involves dynamically sized elements.
    bool isFixedSize() const;

    /// @returns the bitstream width of the expression.
    uint64_t getBitstreamWidth() const { return bitstreamWidth; }

    /// Gets the size of the blocks to slice and reorder: if 0, this is a left-to-right
    /// concatenation. Otherwise, it's a right-to-left concatenation.
    uint64_t getSliceSize() const { return sliceSize; }

    /// @returns the stream elements that make up the concatenation
    std::span<const StreamExpression> streams() const { return streams_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::StreamingConcatenationExpressionSyntax& syntax,
                                  const ASTContext& context);

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
    uint64_t sliceSize;
    uint64_t bitstreamWidth;
};

// clang-format off
#define VRK(x) \
    x(Simple) \
    x(AbsoluteTolerance) \
    x(RelativeTolerance)
// clang-format on
SLANG_ENUM(ValueRangeKind, VRK)
#undef VRK

/// @brief Denotes a range of values by providing expressions for the lower and upper
/// bounds of the range.
///
/// @note This expression needs special handling in the various places that allow it,
/// since it doesn't really have a type.
class SLANG_EXPORT ValueRangeExpression : public Expression {
public:
    ValueRangeKind rangeKind;

    ValueRangeExpression(const Type& type, ValueRangeKind rangeKind, Expression& left,
                         Expression& right, SourceRange sourceRange) :
        Expression(ExpressionKind::ValueRange, type, sourceRange), rangeKind(rangeKind),
        left_(&left), right_(&right) {}

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool propagateType(const ASTContext& context, const Type& newType, SourceRange opRange,
                       ConversionKind conversionKind);

    ConstantValue checkInside(EvalContext& context, const ConstantValue& val) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& comp,
                                  const syntax::ValueRangeExpressionSyntax& syntax,
                                  const ASTContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::ValueRange; }

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
