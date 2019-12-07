//------------------------------------------------------------------------------
// AssignmentExpressions.h
// Definitions for assignment-related expressions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expressions.h"

namespace slang {

struct BinaryExpressionSyntax;

/// Represents an assignment expression.
class AssignmentExpression : public Expression {
public:
    optional<BinaryOperator> op;

    AssignmentExpression(optional<BinaryOperator> op, bool nonBlocking, const Type& type,
                         Expression& left, Expression& right, SourceRange sourceRange) :
        Expression(ExpressionKind::Assignment, type, sourceRange),
        op(op), left_(&left), right_(&right), nonBlocking(nonBlocking) {}

    bool isCompound() const { return op.has_value(); }
    bool isNonBlocking() const { return nonBlocking; }

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void toJson(json& j) const;

    static Expression& fromSyntax(Compilation& compilation, const BinaryExpressionSyntax& syntax,
                                  const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Assignment; }

private:
    Expression* left_;
    Expression* right_;
    bool nonBlocking;
};

} // namespace slang