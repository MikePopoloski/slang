#include "SemanticModel.h"

#include <algorithm>

#include "Scope.h"
#include "SyntaxTree.h"

namespace slang {

SemanticModel::SemanticModel(BumpAllocator& alloc, Diagnostics& diagnostics) :
	alloc(alloc), diagnostics(diagnostics)
{
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

InstanceSymbol* SemanticModel::makeImplicitInstance(const ModuleDeclarationSyntax* syntax) {
	ASSERT(syntax);

	// TODO: check that this can actually be implicit (i.e. no parameters without initializers)
	
	// Discover all of the element's parameters. If we have a parameter port list, the only
	// publicly visible parameters are the ones in that list. Otherwise, parameters declared
	// in the module body are publicly visible.
	const ModuleHeaderSyntax* header = syntax->header;
	auto portParameters = symbolPool.getAs<ParameterSymbol*>();
	stringSet.clear();

	bool overrideLocal = false;
	if (header->parameters) {
		bool lastLocal = false;
		for (const ParameterPortDeclarationSyntax* decl : header->parameters->declarations)
			lastLocal = makeParameters(decl, portParameters, lastLocal, false);
		overrideLocal = true;
	}

	// also find direct body parameters
	auto bodyParameters = symbolPool.getAs<ParameterSymbol*>();
	for (const MemberSyntax* member : syntax->members) {
		if (member->kind == SyntaxKind::ParameterDeclarationStatement)
			makeParameters(member->as<ParameterDeclarationStatementSyntax>()->parameter, bodyParameters, false, overrideLocal);
	}

	// Now evaluate initializers and finalize the type of each parameter.
	// Do ports separately from body parameters.
	auto scope = pushScope(portParameters.get());
	for (ParameterSymbol* param : portParameters.get())
		evaluateParameter(param);

	scope.reset();
	scope = pushScope(bodyParameters.get());
	for (ParameterSymbol* param : bodyParameters.get())
		evaluateParameter(param);

	return alloc.emplace<InstanceSymbol>(portParameters->copy(alloc), bodyParameters->copy(alloc));
}

bool SemanticModel::makeParameters(const ParameterPortDeclarationSyntax* syntax, Buffer<ParameterSymbol*>& buffer,
								   bool lastLocal, bool overrideLocal)
{
	bool local = false;
	if (syntax->kind == SyntaxKind::TypeParameterDeclaration) {
		// TODO: unsupported
	}
	else {
		// It's legal to leave off the parameter keyword in the parameter port list.
		// If you do so, we "inherit" the parameter or localparam keyword from the previous entry.
		// This isn't allowed in a module body, but the parser will take care of the error for us.
		auto p = syntax->as<ParameterDeclarationSyntax>();
		if (!p->keyword)
			local = lastLocal;
		else {
			// In the body of a module that has a parameter port list in its header, parameters are
			// actually just localparams. overrideLocal will be true in this case.
			local = p->keyword.kind == TokenKind::LocalParamKeyword || overrideLocal;
		}

		for (const VariableDeclaratorSyntax* declarator : p->declarators) {
			auto name = declarator->name.valueText();
			if (!name)
				continue;

			// ensure uniqueness of parameter names
			if (!stringSet.insert(name).second)
				// TODO: note previous location
				diagnostics.add(DiagCode::DuplicateParameter, declarator->name.location()) << name;
			else {
				ExpressionSyntax* init = nullptr;
				if (declarator->initializer)
					init = declarator->initializer->expr;
				else if (local) {
					// localparams without initializers are not allowed
					diagnostics.add(DiagCode::LocalParamNoInitializer, declarator->name.location());
				}
				buffer.append(alloc.emplace<ParameterSymbol>(name, declarator->name.location(), p, init, local));
			}
		}
	}
	return local;
}

void SemanticModel::evaluateParameter(ParameterSymbol* parameter) {
	// If no type is given, infer the type from the initializer
	DataTypeSyntax* typeSyntax = parameter->syntax->type;
	if (!typeSyntax) {
		BoundExpression* expr = bindSelfDeterminedExpression(parameter->initializer);
		parameter->type = expr->type;
		parameter->value = expr->constantValue;
	}
	else {
		// TODO
	}
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

BoundExpression* SemanticModel::bindSelfDeterminedExpression(const ExpressionSyntax* syntax) {
    BoundExpression* expr = bindExpression(syntax);
	propagateAndFold(expr, expr->type);
    return expr;
}

BoundExpression* SemanticModel::bindLiteral(const LiteralExpressionSyntax* syntax) {
    switch (syntax->kind) {
        case SyntaxKind::IntegerLiteralExpression: {
            return alloc.emplace<BoundLiteral>(syntax, getSpecialType(SpecialType::Int), false);
        }
        default:
            return nullptr;
    }
}

BoundExpression* SemanticModel::bindSimpleName(const IdentifierNameSyntax* syntax) {
	// if we have an invalid name token just give up now, the error has already been reported
	StringRef identifier = syntax->identifier.valueText();
	if (!identifier)
		return alloc.emplace<BadBoundExpression>();

	const Symbol* symbol = lookupSymbol(identifier);
	ASSERT(symbol && symbol->kind == SymbolKind::Parameter);

	return alloc.emplace<BoundParameter>(syntax, symbol->as<ParameterSymbol>(), false);
}

BoundExpression* SemanticModel::bindLiteral(const IntegerVectorExpressionSyntax* syntax) {
    return alloc.emplace<BoundLiteral>(syntax, getSpecialType(SpecialType::Int), false);
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

void SemanticModel::propagateAndFoldLiteral(BoundLiteral* expression, const TypeSymbol* type) {
	switch (expression->syntax->kind) {
		case SyntaxKind::IntegerLiteralExpression: {
			const SVInt& v = get<SVInt>(expression->syntax->as<LiteralExpressionSyntax>()->literal.numericValue());
			if (v.getBitWidth() < type->integral().width)
				expression->constantValue = extend(v, (uint16_t)type->integral().width, type->integral().isSigned);
			else
				expression->constantValue = v;
		}
	}
}

void SemanticModel::propagateAndFoldParameter(BoundParameter* expression, const TypeSymbol* type) {
	expression->constantValue = expression->symbol->value;
}

void SemanticModel::propagateAndFoldUnaryArithmeticOperator(BoundUnaryExpression* expression, const TypeSymbol* type) {
	expression->type = type;
	propagateAndFold(expression->operand, type);

	ConstantValue cv;
	SVInt& v = get<SVInt>(expression->operand->constantValue);

	switch (expression->syntax->kind) {
		case SyntaxKind::UnaryPlusExpression: cv = v; break;
		case SyntaxKind::UnaryMinusExpression: cv = -v; break;
		case SyntaxKind::UnaryBitwiseNotExpression: cv = ~v; break;
			DEFAULT_UNREACHABLE;
	}
	expression->constantValue = cv;
}

void SemanticModel::propagateAndFoldUnaryReductionOperator(BoundUnaryExpression* expression, const TypeSymbol* type) {
	// operands are self-determined and result type is always 1 bit
	ConstantValue cv;
	SVInt& v = get<SVInt>(expression->operand->constantValue);

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

SemanticModel::ScopePtr SemanticModel::pushScope() {
	scopeStack.emplace_back();
	return ScopePtr(&scopeStack.back(), [this](Scope* s) { popScope(s); });
}

template<typename TContainer>
SemanticModel::ScopePtr SemanticModel::pushScope(const TContainer& range) {
	auto scope = pushScope();
	scope->addRange(range);
	return scope;
}

void SemanticModel::popScope(const Scope* scope) {
	ASSERT(!scopeStack.empty());
	ASSERT(&scopeStack.back() == scope);
	scopeStack.pop_back();
}

const Symbol* SemanticModel::lookupSymbol(StringRef name) {
	// TODO: soooo many things here...
	for (auto it = scopeStack.rbegin(); it != scopeStack.rend(); ++it) {
		const Symbol* result = it->lookup(name);
		if (result)
			return result;
	}
	return nullptr;
}

}