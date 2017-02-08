//------------------------------------------------------------------------------
// ConstantEvaluator.cpp
// Compile-time constant evaluation.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#include "ConstantEvaluator.h"

#include <algorithm>

#include "SemanticModel.h"

namespace slang {

ConstantValue ConstantEvaluator::evaluate(const BoundNode* tree) {
    ASSERT(tree);
    if (tree->bad())
        return nullptr;

    switch (tree->kind) {
        case BoundNodeKind::Literal: return evaluateLiteral((BoundLiteral*)tree);
        case BoundNodeKind::Parameter: return evaluateParameter((BoundParameter*)tree);
        case BoundNodeKind::UnaryExpression: return evaluateUnary((BoundUnaryExpression*)tree);
        case BoundNodeKind::BinaryExpression: return evaluateBinary((BoundBinaryExpression*)tree);

            DEFAULT_UNREACHABLE;
    }
    return nullptr;
}

ConstantValue ConstantEvaluator::evaluateLiteral(const BoundLiteral* expr) {
    return expr->value;
}

ConstantValue ConstantEvaluator::evaluateParameter(const BoundParameter* expr) {
    return expr->symbol.value;
}

ConstantValue ConstantEvaluator::evaluateUnary(const BoundUnaryExpression* expr) {
    const auto& v = evaluate(expr->operand).integer();

    switch (expr->syntax->kind) {
        case SyntaxKind::UnaryPlusExpression: return v;
        case SyntaxKind::UnaryMinusExpression: return -v;
        case SyntaxKind::UnaryBitwiseNotExpression: return ~v;
        case SyntaxKind::UnaryBitwiseAndExpression: return SVInt(v.reductionAnd());
        case SyntaxKind::UnaryBitwiseOrExpression: return SVInt(v.reductionOr());
        case SyntaxKind::UnaryBitwiseXorExpression: return SVInt(v.reductionXor());
        case SyntaxKind::UnaryBitwiseNandExpression: return SVInt(!v.reductionAnd());
        case SyntaxKind::UnaryBitwiseNorExpression: return SVInt(!v.reductionOr());
        case SyntaxKind::UnaryBitwiseXnorExpression: return SVInt(!v.reductionXor());
        case SyntaxKind::UnaryLogicalNotExpression: return SVInt(!v);
            DEFAULT_UNREACHABLE;
    }
    return nullptr;
}

ConstantValue ConstantEvaluator::evaluateBinary(const BoundBinaryExpression* expr) {
    const auto& l = evaluate(expr->left).integer();
    const auto& r = evaluate(expr->right).integer();

    switch (expr->syntax->kind) {
        case SyntaxKind::AddExpression: return l + r;
        case SyntaxKind::SubtractExpression: return l - r;
        case SyntaxKind::MultiplyExpression: return l * r;
        case SyntaxKind::DivideExpression: return l / r;
        case SyntaxKind::ModExpression: return l % r;
        case SyntaxKind::BinaryAndExpression: return l & r;
        case SyntaxKind::BinaryOrExpression: return l | r;
        case SyntaxKind::BinaryXorExpression: return l ^ r;
        case SyntaxKind::BinaryXnorExpression: return l.xnor(r);
        case SyntaxKind::EqualityExpression: return SVInt(l == r);
        case SyntaxKind::InequalityExpression: return SVInt(l != r);
        case SyntaxKind::CaseEqualityExpression: return SVInt((logic_t)exactlyEqual(l, r));
        case SyntaxKind::CaseInequalityExpression: return SVInt((logic_t)!exactlyEqual(l, r));
        case SyntaxKind::GreaterThanEqualExpression: return SVInt(l >= r);
        case SyntaxKind::GreaterThanExpression: return SVInt(l > r);
        case SyntaxKind::LessThanEqualExpression: return SVInt(l <= r);
        case SyntaxKind::LessThanExpression: return SVInt(l < r);
            DEFAULT_UNREACHABLE;
    }
    return nullptr;
}

}
