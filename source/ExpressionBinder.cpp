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

ExpressionBinder::ExpressionBinder(SemanticModel& sem, const Scope* scope) :
    sem(sem), alloc(sem.getAllocator()), scope(scope)
{
    ASSERT(scope);
}

BoundExpression* ExpressionBinder::bindExpression(const ExpressionSyntax* syntax) {
    ASSERT(syntax);

    switch (syntax->kind) {
        case SyntaxKind::NullLiteralExpression:
        case SyntaxKind::StringLiteralExpression:
        case SyntaxKind::TimeLiteralExpression:
        case SyntaxKind::WildcardLiteralExpression:
        case SyntaxKind::OneStepLiteralExpression:
        case SyntaxKind::UnbasedUnsizedLiteralExpression:
            break;
        case SyntaxKind::IdentifierName:
            return bindSimpleName(syntax->as<IdentifierNameSyntax>());
        case SyntaxKind::RealLiteralExpression:
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
        case SyntaxKind::AssignmentExpression:
        case SyntaxKind::AddAssignmentExpression:
        case SyntaxKind::SubtractAssignmentExpression:
        case SyntaxKind::MultiplyAssignmentExpression:
        case SyntaxKind::DivideAssignmentExpression:
        case SyntaxKind::ModAssignmentExpression:
        case SyntaxKind::AndAssignmentExpression:
        case SyntaxKind::OrAssignmentExpression:
        case SyntaxKind::XorAssignmentExpression:
        case SyntaxKind::LogicalLeftShiftAssignmentExpression:
        case SyntaxKind::LogicalRightShiftAssignmentExpression:
        case SyntaxKind::ArithmeticLeftShiftAssignmentExpression:
        case SyntaxKind::ArithmeticRightShiftAssignmentExpression:
            return bindAssignmentOperator(syntax->as<BinaryExpressionSyntax>());

            DEFAULT_UNREACHABLE;
    }
    return nullptr;
}

BoundExpression* ExpressionBinder::bindConstantExpression(const ExpressionSyntax* syntax) {
    return bindSelfDeterminedExpression(syntax);
}

BoundExpression* ExpressionBinder::bindSelfDeterminedExpression(const ExpressionSyntax* syntax) {
    BoundExpression* expr = bindExpression(syntax);
    propagate(expr, expr->type);
    return expr;
}

BoundExpression* ExpressionBinder::bindAssignmentLikeContext(const ExpressionSyntax* syntax, SourceLocation location, const TypeSymbol* assignmentType) {
    BoundExpression* expr = bindExpression(syntax);
    const TypeSymbol* type = expr->type;
    if (!assignmentType->isAssignmentCompatible(type)) {
        DiagCode code = assignmentType->isCastCompatible(type) ? DiagCode::NoImplicitConversion : DiagCode::BadAssignment;
        addError(code, location) << syntax->sourceRange();
        expr = makeBad(expr);
    }
    else {
        const IntegralTypeSymbol& exprType = expr->type->as<IntegralTypeSymbol>();
        if (exprType.width < assignmentType->as<IntegralTypeSymbol>().width)
            propagate(expr, assignmentType);
        else
            propagate(expr, expr->type);
    }

    // TODO: truncation
    return expr;
}

BoundExpression* ExpressionBinder::bindLiteral(const LiteralExpressionSyntax* syntax) {
    switch (syntax->kind) {
        case SyntaxKind::IntegerLiteralExpression:
            return alloc.emplace<BoundLiteral>(
                syntax,
                sem.getKnownType(SyntaxKind::IntType),
                std::get<SVInt>(syntax->literal.numericValue())
            );
        case SyntaxKind::RealLiteralExpression:
            return alloc.emplace<BoundLiteral>(
                syntax,
                sem.getKnownType(SyntaxKind::RealType),
                std::get<double>(syntax->literal.numericValue())
            );
        DEFAULT_UNREACHABLE;
    }
    return nullptr;
}

BoundExpression* ExpressionBinder::bindLiteral(const IntegerVectorExpressionSyntax* syntax) {
    if (syntax->value.isMissing())
        return makeBad(alloc.emplace<BoundLiteral>(syntax, sem.getErrorType(), nullptr));

    const SVInt& value = std::get<SVInt>(syntax->value.numericValue());
    const TypeSymbol* type = sem.getIntegralType(value.getBitWidth(), value.isSigned(), value.hasUnknown());
    return alloc.emplace<BoundLiteral>(syntax, type, value);
}

BoundExpression* ExpressionBinder::bindSimpleName(const IdentifierNameSyntax* syntax) {
    // if we have an invalid name token just give up now; the error has already been reported
    StringRef identifier = syntax->identifier.valueText();
    if (!identifier)
        return makeBad(nullptr);

    const Symbol* symbol = scope->lookup(identifier);
    ASSERT(symbol);

    switch (symbol->kind) {
        case SymbolKind::Parameter:
            return alloc.emplace<BoundParameter>(syntax, symbol->as<ParameterSymbol>());
        case SymbolKind::LocalVariable:
            return alloc.emplace<BoundVarRef>(syntax, (const LocalVariableSymbol*)symbol);

            DEFAULT_UNREACHABLE;
    }
    return nullptr;
}

BoundExpression* ExpressionBinder::bindUnaryArithmeticOperator(const PrefixUnaryExpressionSyntax* syntax) {
    // Supported for both integral and real types. Can be overloaded for others.
    BoundExpression* operand = bindExpression(syntax->operand);
    if (!checkOperatorApplicability(syntax->kind, syntax->operatorToken.location(), &operand))
        return makeBad(alloc.emplace<BoundUnaryExpression>(syntax, sem.getErrorType(), operand));

    return alloc.emplace<BoundUnaryExpression>(syntax, operand->type, operand);
}

BoundExpression* ExpressionBinder::bindUnaryReductionOperator(const PrefixUnaryExpressionSyntax* syntax) {
    // Result type is always a single bit. Supported on integral types.
    BoundExpression* operand = bindSelfDeterminedExpression(syntax->operand);
    if (!checkOperatorApplicability(syntax->kind, syntax->operatorToken.location(), &operand))
        return makeBad(alloc.emplace<BoundUnaryExpression>(syntax, sem.getErrorType(), operand));

    return alloc.emplace<BoundUnaryExpression>(syntax, sem.getKnownType(SyntaxKind::LogicType), operand);
}

BoundExpression* ExpressionBinder::bindArithmeticOperator(const BinaryExpressionSyntax* syntax) {
    BoundExpression* lhs = bindExpression(syntax->left);
    BoundExpression* rhs = bindExpression(syntax->right);
    if (!checkOperatorApplicability(syntax->kind, syntax->operatorToken.location(), &lhs, &rhs))
        return makeBad(alloc.emplace<BoundBinaryExpression>(syntax, sem.getErrorType(), lhs, rhs));

    const IntegralTypeSymbol& l = lhs->type->as<IntegralTypeSymbol>();
    const IntegralTypeSymbol& r = rhs->type->as<IntegralTypeSymbol>();
    int width = std::max(l.width, r.width);
    bool isSigned = l.isSigned && r.isSigned;
    const TypeSymbol* type = sem.getIntegralType(width, isSigned);

    return alloc.emplace<BoundBinaryExpression>(syntax, type, lhs, rhs);
}

BoundExpression* ExpressionBinder::bindComparisonOperator(const BinaryExpressionSyntax* syntax) {
    BoundExpression* lhs = bindExpression(syntax->left);
    BoundExpression* rhs = bindExpression(syntax->right);
    if (!checkOperatorApplicability(syntax->kind, syntax->operatorToken.location(), &lhs, &rhs))
        return makeBad(alloc.emplace<BoundBinaryExpression>(syntax, sem.getErrorType(), lhs, rhs));

    // result type is always a single bit
    return alloc.emplace<BoundBinaryExpression>(syntax, sem.getKnownType(SyntaxKind::LogicType), lhs, rhs);
}

BoundExpression* ExpressionBinder::bindRelationalOperator(const BinaryExpressionSyntax* syntax) {
    BoundExpression* lhs = bindSelfDeterminedExpression(syntax->left);
    BoundExpression* rhs = bindSelfDeterminedExpression(syntax->right);
    if (!checkOperatorApplicability(syntax->kind, syntax->operatorToken.location(), &lhs, &rhs))
        return makeBad(alloc.emplace<BoundBinaryExpression>(syntax, sem.getErrorType(), lhs, rhs));

    // result type is always a single bit
    return alloc.emplace<BoundBinaryExpression>(syntax, sem.getKnownType(SyntaxKind::LogicType), lhs, rhs);
}

BoundExpression* ExpressionBinder::bindShiftOrPowerOperator(const BinaryExpressionSyntax* syntax) {
    // The shift and power operators are handled together here because in both cases the second
    // operand is evaluated in a self determined context.
    BoundExpression* lhs = bindExpression(syntax->left);
    BoundExpression* rhs = bindSelfDeterminedExpression(syntax->right);
    if (!checkOperatorApplicability(syntax->kind, syntax->operatorToken.location(), &lhs, &rhs))
        return makeBad(alloc.emplace<BoundBinaryExpression>(syntax, sem.getErrorType(), lhs, rhs));

    const IntegralTypeSymbol& l = lhs->type->as<IntegralTypeSymbol>();
    const IntegralTypeSymbol& r = rhs->type->as<IntegralTypeSymbol>();
    int width = l.width;
    bool isSigned = l.isSigned && r.isSigned;
    const TypeSymbol* type = sem.getIntegralType(width, isSigned);

    return alloc.emplace<BoundBinaryExpression>(syntax, type, lhs, rhs);
}

BoundExpression* ExpressionBinder::bindAssignmentOperator(const BinaryExpressionSyntax* syntax) {
    BoundExpression* lhs = bindExpression(syntax->left);
    BoundExpression* rhs = bindExpression(syntax->right);

    // It seems that the assignment operator is always applicable, it just may cause
    // truncation or other weird behaviour we should consider warning about

    // result type is always the type of the left hand side
    return alloc.emplace<BoundAssignmentExpression>(syntax, lhs->type, lhs, rhs);
}

bool ExpressionBinder::checkOperatorApplicability(SyntaxKind op, SourceLocation location, BoundExpression** operand) {
    if ((*operand)->bad())
        return false;

    const TypeSymbol* type = (*operand)->type;
    bool good;
    switch (op) {
        case SyntaxKind::UnaryPlusExpression:
        case SyntaxKind::UnaryMinusExpression:
        case SyntaxKind::UnaryLogicalNotExpression:
            good = type->kind == SymbolKind::IntegralType || type->kind == SymbolKind::RealType;
            break;
        default:
            good = type->kind == SymbolKind::IntegralType;
            break;
    }
    if (good)
        return true;

    auto& diag = addError(DiagCode::BadUnaryExpression, location);
    diag << type->toString();
    diag << (*operand)->syntax->sourceRange();
    return false;
}

bool ExpressionBinder::checkOperatorApplicability(SyntaxKind op, SourceLocation location, BoundExpression** lhs, BoundExpression** rhs) {
    if ((*lhs)->bad() || (*rhs)->bad())
        return false;

    const TypeSymbol* lt = (*lhs)->type;
    const TypeSymbol* rt = (*rhs)->type;
    bool good;
    switch (op) {
        case SyntaxKind::AddExpression:
        case SyntaxKind::SubtractExpression:
        case SyntaxKind::MultiplyExpression:
        case SyntaxKind::DivideExpression:
        case SyntaxKind::PowerExpression:
        case SyntaxKind::LogicalAndExpression:
        case SyntaxKind::LogicalOrExpression:
        case SyntaxKind::LogicalImplicationExpression:
        case SyntaxKind::LogicalEquivalenceExpression:
        case SyntaxKind::LessThanEqualExpression:
        case SyntaxKind::LessThanExpression:
        case SyntaxKind::GreaterThanEqualExpression:
        case SyntaxKind::GreaterThanExpression:
        case SyntaxKind::EqualityExpression:
        case SyntaxKind::InequalityExpression:
            good = (lt->kind == SymbolKind::IntegralType || lt->kind == SymbolKind::RealType) &&
                   (rt->kind == SymbolKind::IntegralType || rt->kind == SymbolKind::RealType);
            break;
        default:
            good = lt->kind == SymbolKind::IntegralType && rt->kind == SymbolKind::IntegralType;
            break;
    }
    if (good)
        return true;

    auto& diag = addError(DiagCode::BadBinaryExpression, location);
    diag << lt->toString() << rt->toString();
    diag << (*lhs)->syntax->sourceRange();
    diag << (*rhs)->syntax->sourceRange();
    return false;
}

void ExpressionBinder::propagate(BoundExpression* expression, const TypeSymbol* type) {
    ASSERT(expression);
    if (expression->bad())
        return;

    // SystemVerilog rules for width propagation are subtle and very specific
    // to each individual operator type. They also mainly only apply to
    // expressions of integral type (which will be the majority in most designs).

    // If a type of real is propagated to an expression of a non-real type, the type of the
    // direct sub-expression is changed, but it is not propagated any further down
    bool doNotPropogateRealDownToNonReal = type->kind == SymbolKind::RealType && expression->type->kind != SymbolKind::RealType;
    switch (expression->syntax->kind) {
        case SyntaxKind::NullLiteralExpression:
        case SyntaxKind::StringLiteralExpression:
        case SyntaxKind::TimeLiteralExpression:
        case SyntaxKind::WildcardLiteralExpression:
        case SyntaxKind::OneStepLiteralExpression:
        case SyntaxKind::UnbasedUnsizedLiteralExpression:
        case SyntaxKind::IdentifierName:
        case SyntaxKind::RealLiteralExpression:
        case SyntaxKind::IntegerLiteralExpression:
        case SyntaxKind::IntegerVectorExpression:
            expression->type = type;
            break;
        case SyntaxKind::UnaryPlusExpression:
        case SyntaxKind::UnaryMinusExpression:
        case SyntaxKind::UnaryBitwiseNotExpression:
            expression->type = type;
            if (!doNotPropogateRealDownToNonReal)
                propagate(((BoundUnaryExpression*)expression)->operand, type);
            break;
        case SyntaxKind::UnaryBitwiseAndExpression:
        case SyntaxKind::UnaryBitwiseOrExpression:
        case SyntaxKind::UnaryBitwiseXorExpression:
        case SyntaxKind::UnaryBitwiseNandExpression:
        case SyntaxKind::UnaryBitwiseNorExpression:
        case SyntaxKind::UnaryBitwiseXnorExpression:
        case SyntaxKind::UnaryLogicalNotExpression:
            // Type is already set (always 1 bit) and operand is self determined
            break;
        case SyntaxKind::AddExpression:
        case SyntaxKind::SubtractExpression:
        case SyntaxKind::MultiplyExpression:
        case SyntaxKind::DivideExpression:
        case SyntaxKind::ModExpression:
        case SyntaxKind::BinaryAndExpression:
        case SyntaxKind::BinaryOrExpression:
        case SyntaxKind::BinaryXorExpression:
        case SyntaxKind::BinaryXnorExpression:
            expression->type = type;
            if (!doNotPropogateRealDownToNonReal)
                propagate(((BoundBinaryExpression*)expression)->left, type);
                propagate(((BoundBinaryExpression*)expression)->right, type);
            break;
        case SyntaxKind::EqualityExpression:
        case SyntaxKind::InequalityExpression:
        case SyntaxKind::CaseEqualityExpression:
        case SyntaxKind::CaseInequalityExpression:
        case SyntaxKind::GreaterThanEqualExpression:
        case SyntaxKind::GreaterThanExpression:
        case SyntaxKind::LessThanEqualExpression:
        case SyntaxKind::LessThanExpression: {
            // operands are sized to max(l,r) and the result of the operation is always 1 bit
            // no propagations from above have an actual have an effect on the subexpressions
            // This logic is similar to that of assignment operators, except for the
            // reciprocality
            BoundBinaryExpression* expr = ((BoundBinaryExpression*)expression);
            BoundExpression *lhs = expr->left;
            BoundExpression *rhs = expr->right;
            if (lhs->type && rhs->type && lhs->type->kind == SymbolKind::IntegralType && rhs->type->kind == SymbolKind::IntegralType) {
                const IntegralTypeSymbol& lhsym = lhs->type->as<IntegralTypeSymbol>();
                const IntegralTypeSymbol& rhsym = rhs->type->as<IntegralTypeSymbol>();
                if (lhsym.width < rhsym.width) {
                    std::swap(lhs, rhs);
                }
                if (lhsym.width > rhsym.width) {
                    rhs->type = sem.getIntegralType(lhsym.width, rhsym.isSigned, rhsym.isFourState);
                    propagate(rhs, rhs->type);
                }
            }
            break;
        }
        case SyntaxKind::LogicalAndExpression:
        case SyntaxKind::LogicalOrExpression:
        case SyntaxKind::LogicalImplicationExpression:
        case SyntaxKind::LogicalEquivalenceExpression:
            // Type is already set (always 1 bit) and operands are self determined
            break;
        case SyntaxKind::LogicalShiftLeftExpression:
        case SyntaxKind::LogicalShiftRightExpression:
        case SyntaxKind::ArithmeticShiftLeftExpression:
        case SyntaxKind::ArithmeticShiftRightExpression:
        case SyntaxKind::PowerExpression:
            // Only the left hand side gets propagated; the rhs is self determined
            expression->type = type;
            if (!doNotPropogateRealDownToNonReal)
                propagate(((BoundBinaryExpression*)expression)->left, type);
            break;
        case SyntaxKind::AssignmentExpression:
        case SyntaxKind::AddAssignmentExpression:
        case SyntaxKind::SubtractAssignmentExpression:
        case SyntaxKind::MultiplyAssignmentExpression:
        case SyntaxKind::DivideAssignmentExpression:
        case SyntaxKind::ModAssignmentExpression:
        case SyntaxKind::AndAssignmentExpression:
        case SyntaxKind::OrAssignmentExpression:
        case SyntaxKind::XorAssignmentExpression:
        case SyntaxKind::LogicalLeftShiftAssignmentExpression:
        case SyntaxKind::LogicalRightShiftAssignmentExpression:
        case SyntaxKind::ArithmeticLeftShiftAssignmentExpression:
        case SyntaxKind::ArithmeticRightShiftAssignmentExpression: {
            // The operands of an assignment are themselves self determined,
            // but we must increase the size of the RHS to the size of the LHS if it is larger, and then
            // propagate that information down
            BoundBinaryExpression* expr = ((BoundBinaryExpression*)expression);
            BoundExpression *lhs = expr->left;
            BoundExpression *rhs = expr->right;
            if (lhs->type->kind == SymbolKind::IntegralType && rhs->type->kind == SymbolKind::IntegralType) {
                const IntegralTypeSymbol& from = lhs->type->as<IntegralTypeSymbol>();
                const IntegralTypeSymbol& to = rhs->type->as<IntegralTypeSymbol>();
                if (from.width > to.width) {
                    rhs->type = sem.getIntegralType(from.width, to.isSigned, to.isFourState);
                    propagate(rhs, rhs->type);
                }
            }
            break;
        }

            DEFAULT_UNREACHABLE;
    }
}

BadBoundExpression* ExpressionBinder::makeBad(BoundExpression* expr) {
    return alloc.emplace<BadBoundExpression>(expr);
}

Diagnostic& ExpressionBinder::addError(DiagCode code, SourceLocation location) {
    return sem.getDiagnostics().add(code, location);
}

}
