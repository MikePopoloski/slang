#include "SemanticModel.h"

#include <algorithm>

#include "SyntaxTree.h"

namespace slang {

SemanticModel::SemanticModel() {
    specialTypes[(int)SpecialType::ShortInt] = alloc.emplace<IntegralTypeSymbol>(16, true, false);
    specialTypes[(int)SpecialType::Int] = alloc.emplace<IntegralTypeSymbol>(32, true, false);
    specialTypes[(int)SpecialType::LongInt] = alloc.emplace<IntegralTypeSymbol>(64, true, false);
    specialTypes[(int)SpecialType::Byte] = alloc.emplace<IntegralTypeSymbol>(8, true, false);
    specialTypes[(int)SpecialType::Bit] = alloc.emplace<IntegralTypeSymbol>(1, false, false);
    specialTypes[(int)SpecialType::Logic] = alloc.emplace<IntegralTypeSymbol>(1, false, true);
    specialTypes[(int)SpecialType::Reg] = alloc.emplace<IntegralTypeSymbol>(1, false, true);
    specialTypes[(int)SpecialType::Integer] = alloc.emplace<IntegralTypeSymbol>(32, true, true);
    specialTypes[(int)SpecialType::Time] = alloc.emplace<IntegralTypeSymbol>(64, false, true);
    specialTypes[(int)SpecialType::Error] = alloc.emplace<ErrorTypeSymbol>();
}

SemanticModel::SemanticModel(DeclarationTable& declTable) :
    SemanticModel()
{
}

void SemanticModel::bindModuleImplicit(ModuleDeclarationSyntax* module) {
}

BoundParameterDeclaration* SemanticModel::bindParameterDecl(const ParameterDeclarationSyntax* syntax) {
    ASSERT(syntax);
    ASSERT(syntax->kind == SyntaxKind::ParameterDeclaration);

    auto declarator = syntax->declarators[0];
    auto initializer = declarator->initializer;

    auto boundInitializer = bindSelfDeterminedExpression(initializer->expr);
    return alloc.emplace<BoundParameterDeclaration>(syntax, boundInitializer);
}

BoundExpression* SemanticModel::bindExpression(const ExpressionSyntax* syntax) {
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
    }
    return nullptr;
}

BoundExpression* SemanticModel::bindSelfDeterminedExpression(const ExpressionSyntax* syntax) {
    BoundExpression* expr = bindExpression(syntax);
	propagateAndFold(expr, expr->type);
    return expr;
}

BoundExpression* SemanticModel::bindLiteral(const LiteralExpressionSyntax* syntax) {
    switch (syntax->kind) {
        case SyntaxKind::IntegerLiteralExpression: {
            return alloc.emplace<BoundLiteralExpression>(syntax, getSpecialType(SpecialType::Int), false);
        }
        default:
            return nullptr;
    }
}

BoundExpression* SemanticModel::bindLiteral(const IntegerVectorExpressionSyntax* syntax) {
    return alloc.emplace<BoundLiteralExpression>(syntax, getSpecialType(SpecialType::Int), false);
}

BoundExpression* SemanticModel::bindUnaryArithmeticOperator(const PrefixUnaryExpressionSyntax* syntax) {
    BoundExpression* operand = bindExpression(syntax->operand);
    if (operand->bad)
        return alloc.emplace<BoundUnaryExpression>(syntax, getErrorType(), operand, true);

    return alloc.emplace<BoundUnaryExpression>(syntax, operand->type, operand, false);
}

BoundExpression* SemanticModel::bindUnaryReductionOperator(const PrefixUnaryExpressionSyntax* syntax) {
    // result type is always a single bit
    BoundExpression* operand = bindSelfDeterminedExpression(syntax->operand);
    return alloc.emplace<BoundUnaryExpression>(syntax, getSpecialType(SpecialType::Logic), operand, operand->bad);
}

BoundExpression* SemanticModel::bindArithmeticOperator(const BinaryExpressionSyntax* syntax) {
    BoundExpression* lhs = bindExpression(syntax->left);
    BoundExpression* rhs = bindExpression(syntax->right);
    if (lhs->bad || rhs->bad)
        return alloc.emplace<BoundBinaryExpression>(syntax, getErrorType(), lhs, rhs, true);

    const IntegralTypeSymbol& l = lhs->type->integral();
    const IntegralTypeSymbol& r = rhs->type->integral();
    int width = std::max(l.width, r.width);
    bool isSigned = l.isSigned && r.isSigned;
    const TypeSymbol* type = getIntegralType(width, isSigned);

    return alloc.emplace<BoundBinaryExpression>(syntax, type, lhs, rhs, false);
}

BoundExpression* SemanticModel::bindComparisonOperator(const BinaryExpressionSyntax* syntax) {
    BoundExpression* lhs = bindExpression(syntax->left);
    BoundExpression* rhs = bindExpression(syntax->right);
    if (lhs->bad || rhs->bad)
        return alloc.emplace<BoundBinaryExpression>(syntax, getErrorType(), lhs, rhs, true);

    // result type is always a single bit
    return alloc.emplace<BoundBinaryExpression>(syntax, getSpecialType(SpecialType::Logic), lhs, rhs, false);
}

BoundExpression* SemanticModel::bindRelationalOperator(const BinaryExpressionSyntax* syntax) {
    BoundExpression* lhs = bindSelfDeterminedExpression(syntax->left);
    BoundExpression* rhs = bindSelfDeterminedExpression(syntax->right);
    if (lhs->bad || rhs->bad)
        return alloc.emplace<BoundBinaryExpression>(syntax, getErrorType(), lhs, rhs, true);

    // result type is always a single bit
    return alloc.emplace<BoundBinaryExpression>(syntax, getSpecialType(SpecialType::Logic), lhs, rhs, false);
}

BoundExpression* SemanticModel::bindShiftOrPowerOperator(const BinaryExpressionSyntax* syntax) {
    // The shift and power operators are handled together here because in both cases the second
    // operand is evaluated in a self determined context.
    BoundExpression* lhs = bindExpression(syntax->left);
    BoundExpression* rhs = bindSelfDeterminedExpression(syntax->right);
    if (lhs->bad || rhs->bad)
        return alloc.emplace<BoundBinaryExpression>(syntax, getErrorType(), lhs, rhs, true);

    const IntegralTypeSymbol& l = lhs->type->integral();
    const IntegralTypeSymbol& r = rhs->type->integral();
    int width = l.width;
    bool isSigned = l.isSigned && r.isSigned;
    const TypeSymbol* type = getIntegralType(width, isSigned);

    return alloc.emplace<BoundBinaryExpression>(syntax, type, lhs, rhs, false);
}

const TypeSymbol* SemanticModel::getIntegralType(int width, bool isSigned) {
	std::unordered_map<int, const TypeSymbol*>& cache = integralTypeCache[true][isSigned]; // always use the 4-state cache

	auto it = cache.find(width);
	if (it != cache.end())
		return it->second;

	it = cache.emplace_hint(it, width, alloc.emplace<IntegralTypeSymbol>(width, isSigned, true));
	return it->second;
}

void SemanticModel::propagateAndFold(BoundExpression* expression, const TypeSymbol* type) {
    ASSERT(expression);
	if (expression->bad)
		return;

	switch (expression->syntax->kind) {
		case SyntaxKind::IntegerLiteralExpression:
		case SyntaxKind::IntegerVectorExpression:
			return propagateAndFoldLiteral((BoundLiteralExpression*)expression, type);
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
}

void SemanticModel::propagateAndFoldLiteral(BoundLiteralExpression* expression, const TypeSymbol* type) {
	switch (expression->syntax->kind) {
		case SyntaxKind::IntegerLiteralExpression: {
			const SVInt& v = get<SVInt>(expression->syntax->as<LiteralExpressionSyntax>()->literal.numericValue());
			if (v.getBitWidth() < type->integral().width)
				expression->constantValue = extend(v, type->integral().width, type->integral().isSigned);
			else
				expression->constantValue = v;
		}
	}
}

void SemanticModel::propagateAndFoldUnaryArithmeticOperator(BoundUnaryExpression* expression, const TypeSymbol* type) {
}

void SemanticModel::propagateAndFoldUnaryReductionOperator(BoundUnaryExpression* expression, const TypeSymbol* type) {
}

void SemanticModel::propagateAndFoldArithmeticOperator(BoundBinaryExpression* expression, const TypeSymbol* type) {
	expression->type = type;
	propagateAndFold(expression->left, type);
	propagateAndFold(expression->right, type);

	ConstantValue cv;
	SVInt& l = get<SVInt>(expression->left->constantValue);
	SVInt& r = get<SVInt>(expression->right->constantValue);

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

void SemanticModel::propagateAndFoldComparisonOperator(BoundBinaryExpression* expression, const TypeSymbol* type) {
}

void SemanticModel::propagateAndFoldRelationalOperator(BoundBinaryExpression* expression, const TypeSymbol* type) {
}

void SemanticModel::propagateAndFoldShiftOrPowerOperator(BoundBinaryExpression* expression, const TypeSymbol* type) {
}

}