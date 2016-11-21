//------------------------------------------------------------------------------
// ExpressionBinder.cpp
// Centralized code for convert expressions into AST trees
// (also includes constant folding).
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#include "ExpressionBinder.h"

#include <algorithm>

#include "SemanticModel.h"

namespace slang {

ExpressionBinder::ExpressionBinder(SemanticModel& sem) :
    sem(sem), alloc(sem.getAllocator())
{
}

BoundExpression* ExpressionBinder::bindExpression(const ExpressionSyntax* syntax) {
    ASSERT(syntax);
    switch (syntax->kind) {
        case SyntaxKind::NullLiteralExpression:
        case SyntaxKind::StringLiteralExpression:
        case SyntaxKind::RealLiteralExpression:
        case SyntaxKind::TimeLiteralExpression:
        case SyntaxKind::WildcardLiteralExpression:
        case SyntaxKind::OneStepLiteralExpression:
        case SyntaxKind::UnbasedUnsizedLiteralExpression:
            break;
        case SyntaxKind::IdentifierName:
            return bindSimpleName(syntax->as<IdentifierNameSyntax>());
        case SyntaxKind::IntegerLiteralExpression:
            return bindLiteral(syntax->as<LiteralExpressionSyntax>());
        case SyntaxKind::IntegerVectorExpression:
            return bindLiteral(syntax->as<IntegerVectorExpressionSyntax>());
        case SyntaxKind::ParenthesizedExpression:
            return bindExpression(syntax->as<ParenthesizedExpressionSyntax>()->expression);
        case SyntaxKind::UnaryPlusExpression:
        case SyntaxKind::UnaryMinusExpression:
        case SyntaxKind::UnaryBitwiseNotExpression:
            return bindUnaryArithmeticOperator(syntax->as<PrefixUnaryExpressionSyntax>());
        case SyntaxKind::UnaryBitwiseAndExpression:
        case SyntaxKind::UnaryBitwiseOrExpression:
        case SyntaxKind::UnaryBitwiseXorExpression:
        case SyntaxKind::UnaryBitwiseNandExpression:
        case SyntaxKind::UnaryBitwiseNorExpression:
        case SyntaxKind::UnaryBitwiseXnorExpression:
        case SyntaxKind::UnaryLogicalNotExpression:
            return bindUnaryReductionOperator(syntax->as<PrefixUnaryExpressionSyntax>());
        case SyntaxKind::AddExpression:
        case SyntaxKind::SubtractExpression:
        case SyntaxKind::MultiplyExpression:
        case SyntaxKind::DivideExpression:
        case SyntaxKind::ModExpression:
        case SyntaxKind::BinaryAndExpression:
        case SyntaxKind::BinaryOrExpression:
        case SyntaxKind::BinaryXorExpression:
        case SyntaxKind::BinaryXnorExpression:
            return bindArithmeticOperator(syntax->as<BinaryExpressionSyntax>());
        case SyntaxKind::EqualityExpression:
        case SyntaxKind::InequalityExpression:
        case SyntaxKind::CaseEqualityExpression:
        case SyntaxKind::CaseInequalityExpression:
        case SyntaxKind::GreaterThanEqualExpression:
        case SyntaxKind::GreaterThanExpression:
        case SyntaxKind::LessThanEqualExpression:
        case SyntaxKind::LessThanExpression:
            return bindComparisonOperator(syntax->as<BinaryExpressionSyntax>());
        case SyntaxKind::LogicalAndExpression:
        case SyntaxKind::LogicalOrExpression:
        case SyntaxKind::LogicalImplicationExpression:
        case SyntaxKind::LogicalEquivalenceExpression:
            return bindRelationalOperator(syntax->as<BinaryExpressionSyntax>());
        case SyntaxKind::LogicalShiftLeftExpression:
        case SyntaxKind::LogicalShiftRightExpression:
        case SyntaxKind::ArithmeticShiftLeftExpression:
        case SyntaxKind::ArithmeticShiftRightExpression:
        case SyntaxKind::PowerExpression:
            return bindShiftOrPowerOperator(syntax->as<BinaryExpressionSyntax>());

            DEFAULT_UNREACHABLE;
    }
    return nullptr;
}

BoundExpression* ExpressionBinder::bindConstantExpression(const ExpressionSyntax* syntax) {
    return bindSelfDeterminedExpression(syntax);
}

BoundExpression* ExpressionBinder::bindSelfDeterminedExpression(const ExpressionSyntax* syntax) {
    BoundExpression* expr = bindExpression(syntax);
    propagateAndFold(expr, expr->type);
    return expr;
}

BoundExpression* ExpressionBinder::bindAssignmentLikeContext(const ExpressionSyntax* syntax, const TypeSymbol* assignmentType) {
    // The rules for determining expression type in an assignment-like context are as follows:
    // - If the destination type width is larger than the width of the expression, propagate that type back down
    // - If the destination width is smaller, insert an implicit truncation of bits
    BoundExpression* expr = bindExpression(syntax);
    if (expr->type->integral().width < assignmentType->integral().width)
        propagateAndFold(expr, assignmentType);
    else
        propagateAndFold(expr, expr->type);

    // TODO: truncation
    return expr;
}

BoundExpression* ExpressionBinder::bindLiteral(const LiteralExpressionSyntax* syntax) {
    switch (syntax->kind) {
        case SyntaxKind::IntegerLiteralExpression: {
            return alloc.emplace<BoundLiteral>(syntax, sem.getKnownType(SyntaxKind::IntType), false);
        }
        default:
            return nullptr;
    }
}

BoundExpression* ExpressionBinder::bindSimpleName(const IdentifierNameSyntax* syntax) {
    // if we have an invalid name token just give up now, the error has already been reported
    StringRef identifier = syntax->identifier.valueText();
    if (!identifier)
        return alloc.emplace<BadBoundExpression>();

    const Symbol* symbol = sem.lookupSymbol(identifier);
    ASSERT(symbol && symbol->kind == SymbolKind::Parameter);

    return alloc.emplace<BoundParameter>(syntax, symbol->as<ParameterSymbol>(), false);
}

BoundExpression* ExpressionBinder::bindLiteral(const IntegerVectorExpressionSyntax* syntax) {
    return alloc.emplace<BoundLiteral>(syntax, sem.getKnownType(SyntaxKind::IntType), false);
}

BoundExpression* ExpressionBinder::bindUnaryArithmeticOperator(const PrefixUnaryExpressionSyntax* syntax) {
    BoundExpression* operand = bindExpression(syntax->operand);
    if (operand->bad)
        return alloc.emplace<BoundUnaryExpression>(syntax, sem.getErrorType(), operand, true);

    return alloc.emplace<BoundUnaryExpression>(syntax, operand->type, operand, false);
}

BoundExpression* ExpressionBinder::bindUnaryReductionOperator(const PrefixUnaryExpressionSyntax* syntax) {
    // result type is always a single bit
    BoundExpression* operand = bindSelfDeterminedExpression(syntax->operand);
    return alloc.emplace<BoundUnaryExpression>(syntax, sem.getKnownType(SyntaxKind::LogicType), operand, operand->bad);
}

BoundExpression* ExpressionBinder::bindArithmeticOperator(const BinaryExpressionSyntax* syntax) {
    BoundExpression* lhs = bindExpression(syntax->left);
    BoundExpression* rhs = bindExpression(syntax->right);
    if (lhs->bad || rhs->bad)
        return alloc.emplace<BoundBinaryExpression>(syntax, sem.getErrorType(), lhs, rhs, true);

    const IntegralTypeSymbol& l = lhs->type->integral();
    const IntegralTypeSymbol& r = rhs->type->integral();
    int width = std::max(l.width, r.width);
    bool isSigned = l.isSigned && r.isSigned;
    const TypeSymbol* type = sem.getIntegralType(width, isSigned);

    return alloc.emplace<BoundBinaryExpression>(syntax, type, lhs, rhs, false);
}

BoundExpression* ExpressionBinder::bindComparisonOperator(const BinaryExpressionSyntax* syntax) {
    BoundExpression* lhs = bindExpression(syntax->left);
    BoundExpression* rhs = bindExpression(syntax->right);
    if (lhs->bad || rhs->bad)
        return alloc.emplace<BoundBinaryExpression>(syntax, sem.getErrorType(), lhs, rhs, true);

    // result type is always a single bit
    return alloc.emplace<BoundBinaryExpression>(syntax, sem.getKnownType(SyntaxKind::LogicType), lhs, rhs, false);
}

BoundExpression* ExpressionBinder::bindRelationalOperator(const BinaryExpressionSyntax* syntax) {
    BoundExpression* lhs = bindSelfDeterminedExpression(syntax->left);
    BoundExpression* rhs = bindSelfDeterminedExpression(syntax->right);
    if (lhs->bad || rhs->bad)
        return alloc.emplace<BoundBinaryExpression>(syntax, sem.getErrorType(), lhs, rhs, true);

    // result type is always a single bit
    return alloc.emplace<BoundBinaryExpression>(syntax, sem.getKnownType(SyntaxKind::LogicType), lhs, rhs, false);
}

BoundExpression* ExpressionBinder::bindShiftOrPowerOperator(const BinaryExpressionSyntax* syntax) {
    // The shift and power operators are handled together here because in both cases the second
    // operand is evaluated in a self determined context.
    BoundExpression* lhs = bindExpression(syntax->left);
    BoundExpression* rhs = bindSelfDeterminedExpression(syntax->right);
    if (lhs->bad || rhs->bad)
        return alloc.emplace<BoundBinaryExpression>(syntax, sem.getErrorType(), lhs, rhs, true);

    const IntegralTypeSymbol& l = lhs->type->integral();
    const IntegralTypeSymbol& r = rhs->type->integral();
    int width = l.width;
    bool isSigned = l.isSigned && r.isSigned;
    const TypeSymbol* type = sem.getIntegralType(width, isSigned);

    return alloc.emplace<BoundBinaryExpression>(syntax, type, lhs, rhs, false);
}

void ExpressionBinder::propagateAndFold(BoundExpression* expression, const TypeSymbol* type) {
    ASSERT(expression);
    if (expression->bad)
        return;

    switch (expression->syntax->kind) {
        case SyntaxKind::IntegerLiteralExpression:
        case SyntaxKind::IntegerVectorExpression:
            return propagateAndFoldLiteral((BoundLiteral*)expression, type);
        case SyntaxKind::UnaryPlusExpression:
        case SyntaxKind::UnaryMinusExpression:
        case SyntaxKind::UnaryBitwiseNotExpression:
            return propagateAndFoldUnaryArithmeticOperator((BoundUnaryExpression*)expression, type);
        case SyntaxKind::UnaryBitwiseAndExpression:
        case SyntaxKind::UnaryBitwiseOrExpression:
        case SyntaxKind::UnaryBitwiseXorExpression:
        case SyntaxKind::UnaryBitwiseNandExpression:
        case SyntaxKind::UnaryBitwiseNorExpression:
        case SyntaxKind::UnaryBitwiseXnorExpression:
        case SyntaxKind::UnaryLogicalNotExpression:
            return propagateAndFoldUnaryReductionOperator((BoundUnaryExpression*)expression, type);
        case SyntaxKind::AddExpression:
        case SyntaxKind::SubtractExpression:
        case SyntaxKind::MultiplyExpression:
        case SyntaxKind::DivideExpression:
        case SyntaxKind::ModExpression:
        case SyntaxKind::BinaryAndExpression:
        case SyntaxKind::BinaryOrExpression:
        case SyntaxKind::BinaryXorExpression:
        case SyntaxKind::BinaryXnorExpression:
            return propagateAndFoldArithmeticOperator((BoundBinaryExpression*)expression, type);
        case SyntaxKind::EqualityExpression:
        case SyntaxKind::InequalityExpression:
        case SyntaxKind::CaseEqualityExpression:
        case SyntaxKind::CaseInequalityExpression:
        case SyntaxKind::GreaterThanEqualExpression:
        case SyntaxKind::GreaterThanExpression:
        case SyntaxKind::LessThanEqualExpression:
        case SyntaxKind::LessThanExpression:
            return propagateAndFoldComparisonOperator((BoundBinaryExpression*)expression, type);
        case SyntaxKind::LogicalAndExpression:
        case SyntaxKind::LogicalOrExpression:
        case SyntaxKind::LogicalImplicationExpression:
        case SyntaxKind::LogicalEquivalenceExpression:
            return propagateAndFoldRelationalOperator((BoundBinaryExpression*)expression, type);
        case SyntaxKind::LogicalShiftLeftExpression:
        case SyntaxKind::LogicalShiftRightExpression:
        case SyntaxKind::ArithmeticShiftLeftExpression:
        case SyntaxKind::ArithmeticShiftRightExpression:
        case SyntaxKind::PowerExpression:
            return propagateAndFoldShiftOrPowerOperator((BoundBinaryExpression*)expression, type);
    }

    switch (expression->kind) {
        case BoundNodeKind::Parameter:
            return propagateAndFoldParameter((BoundParameter*)expression, type);
    }
}

void ExpressionBinder::propagateAndFoldLiteral(BoundLiteral* expression, const TypeSymbol* type) {
    switch (expression->syntax->kind) {
        case SyntaxKind::IntegerLiteralExpression: {
            const SVInt& v = std::get<SVInt>(expression->syntax->as<LiteralExpressionSyntax>()->literal.numericValue());
            if (v.getBitWidth() < type->integral().width)
                expression->constantValue = extend(v, (uint16_t)type->integral().width, type->integral().isSigned);
            else
                expression->constantValue = v;
        }
    }
}

void ExpressionBinder::propagateAndFoldParameter(BoundParameter* expression, const TypeSymbol* type) {
    expression->constantValue = expression->symbol->value;
}

void ExpressionBinder::propagateAndFoldUnaryArithmeticOperator(BoundUnaryExpression* expression, const TypeSymbol* type) {
    expression->type = type;
    propagateAndFold(expression->operand, type);

    ConstantValue cv;
    SVInt& v = std::get<SVInt>(expression->operand->constantValue);

    switch (expression->syntax->kind) {
        case SyntaxKind::UnaryPlusExpression: cv = v; break;
        case SyntaxKind::UnaryMinusExpression: cv = -v; break;
        case SyntaxKind::UnaryBitwiseNotExpression: cv = ~v; break;
            DEFAULT_UNREACHABLE;
    }
    expression->constantValue = cv;
}

void ExpressionBinder::propagateAndFoldUnaryReductionOperator(BoundUnaryExpression* expression, const TypeSymbol* type) {
    // operands are self-determined and result type is always 1 bit
    ConstantValue cv;
    SVInt& v = std::get<SVInt>(expression->operand->constantValue);

    switch (expression->syntax->kind) {
        case SyntaxKind::UnaryBitwiseAndExpression: cv = SVInt(v.reductionAnd()); break;
        case SyntaxKind::UnaryBitwiseOrExpression: cv = SVInt(v.reductionOr()); break;
        case SyntaxKind::UnaryBitwiseXorExpression: cv = SVInt(v.reductionXor()); break;
        case SyntaxKind::UnaryBitwiseNandExpression: cv = SVInt(!v.reductionAnd()); break;
        case SyntaxKind::UnaryBitwiseNorExpression: cv = SVInt(!v.reductionOr()); break;
        case SyntaxKind::UnaryBitwiseXnorExpression: cv = SVInt(!v.reductionXor()); break;
        case SyntaxKind::UnaryLogicalNotExpression: cv = SVInt(!v); break;
            DEFAULT_UNREACHABLE;
    }
    expression->constantValue = cv;
}

void ExpressionBinder::propagateAndFoldArithmeticOperator(BoundBinaryExpression* expression, const TypeSymbol* type) {
    expression->type = type;
    propagateAndFold(expression->left, type);
    propagateAndFold(expression->right, type);

    ConstantValue cv;
    SVInt& l = std::get<SVInt>(expression->left->constantValue);
    SVInt& r = std::get<SVInt>(expression->right->constantValue);

    switch (expression->syntax->kind) {
        case SyntaxKind::AddExpression: cv = l + r; break;
        case SyntaxKind::SubtractExpression: cv = l - r; break;
        case SyntaxKind::MultiplyExpression: cv = l * r; break;
        case SyntaxKind::DivideExpression: cv = l / r; break;
        case SyntaxKind::ModExpression: cv = l % r; break;
        case SyntaxKind::BinaryAndExpression: cv = l & r; break;
        case SyntaxKind::BinaryOrExpression: cv = l | r; break;
        case SyntaxKind::BinaryXorExpression: cv = l ^ r; break;
        case SyntaxKind::BinaryXnorExpression: cv = l.xnor(r); break;
            DEFAULT_UNREACHABLE;
    }
    expression->constantValue = cv;
}

void ExpressionBinder::propagateAndFoldComparisonOperator(BoundBinaryExpression* expression, const TypeSymbol* type) {
}

void ExpressionBinder::propagateAndFoldRelationalOperator(BoundBinaryExpression* expression, const TypeSymbol* type) {
}

void ExpressionBinder::propagateAndFoldShiftOrPowerOperator(BoundBinaryExpression* expression, const TypeSymbol* type) {
}

}