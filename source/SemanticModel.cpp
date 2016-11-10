//------------------------------------------------------------------------------
// SemanticModel.cpp
// Symbol binding and semantic analysis.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#include "SemanticModel.h"

#include "Scope.h"
#include "SyntaxTree.h"

namespace slang {

SemanticModel::SemanticModel(BumpAllocator& alloc, Diagnostics& diagnostics) :
	alloc(alloc), diagnostics(diagnostics), binder(*this)
{
    knownTypes[SyntaxKind::ShortIntType] = getIntegralType(16, true, false);
    knownTypes[SyntaxKind::IntType] = getIntegralType(32, true, false);
    knownTypes[SyntaxKind::LongIntType] = getIntegralType(64, true, false);
    knownTypes[SyntaxKind::ByteType] = getIntegralType(8, true, false);
    knownTypes[SyntaxKind::BitType] = getIntegralType(1, false, false);
    knownTypes[SyntaxKind::LogicType] = getIntegralType(1, false, true);
    knownTypes[SyntaxKind::RegType] = getIntegralType(1, false, true);
    knownTypes[SyntaxKind::IntegerType] = getIntegralType(32, true, true);
    knownTypes[SyntaxKind::TimeType] = getIntegralType(64, false, true);
    knownTypes[SyntaxKind::Unknown] = alloc.emplace<ErrorTypeSymbol>();
}

InstanceSymbol* SemanticModel::makeImplicitInstance(const ModuleDeclarationSyntax* syntax) {
	ASSERT(syntax);

	// TODO: check that this can actually be implicit (i.e. no parameters without initializers)
	
	// Discover all of the element's parameters. If we have a parameter port list, the only
	// publicly visible parameters are the ones in that list. Otherwise, parameters declared
	// in the module body are publicly visible.
	const ModuleHeaderSyntax* header = syntax->header;
	auto portParameters = symbolPool.getAs<ParameterSymbol*>();
	nameDupMap.clear();

	bool overrideLocal = false;
	if (header->parameters) {
		bool lastLocal = false;
		for (const ParameterDeclarationSyntax* decl : header->parameters->declarations)
			lastLocal = makeParameters(decl, portParameters, lastLocal, false, false);
		overrideLocal = true;
	}

	// also find direct body parameters
	auto bodyParameters = symbolPool.getAs<ParameterSymbol*>();
	for (const MemberSyntax* member : syntax->members) {
		if (member->kind == SyntaxKind::ParameterDeclarationStatement)
			makeParameters(member->as<ParameterDeclarationStatementSyntax>()->parameter, bodyParameters,
						   false, overrideLocal, true);
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

const TypeSymbol* SemanticModel::makeTypeSymbol(const DataTypeSyntax* syntax) {
	ASSERT(syntax);

	switch (syntax->kind) {
		case SyntaxKind::BitType:
		case SyntaxKind::LogicType:
		case SyntaxKind::RegType: {
			// bit vector (possibly of just one element)
			auto its = syntax->as<IntegerTypeSyntax>();
			bool isSigned = its->signing.kind == TokenKind::SignedKeyword;

			break;
		}
	}

	return nullptr;
}

bool SemanticModel::evaluateConstantDims(const SyntaxList<VariableDimensionSyntax>& dimensions, Buffer<ConstantRange>& results) {
	for (const VariableDimensionSyntax* dim : dimensions) {
		const SelectorSyntax* selector;
		if (!dim->specifier || dim->specifier->kind != SyntaxKind::RangeDimensionSpecifier ||
			(selector = dim->specifier->as<RangeDimensionSpecifierSyntax>()->selector)->kind != SyntaxKind::SimpleRangeSelect) {

			auto& diag = diagnostics.add(DiagCode::PackedDimRequiresConstantRange, dim->closeBracket.location());
			// TODO: source range
			return false;
		}

		const RangeSelectSyntax* range = selector->as<RangeSelectSyntax>();
		auto msbExpr = binder.bindConstantExpression(range->left);
		auto lsbExpr = binder.bindConstantExpression(range->right);
		if (msbExpr->bad || lsbExpr->bad)
			return false;

		// TODO: ensure integer here
		results.emplace(ConstantRange {get<SVInt>(msbExpr->constantValue), get<SVInt>(lsbExpr->constantValue)});
	}
	return true;
}

bool SemanticModel::makeParameters(const ParameterDeclarationSyntax* syntax, Buffer<ParameterSymbol*>& buffer,
								   bool lastLocal, bool overrideLocal, bool bodyParam)
{
	// It's legal to leave off the parameter keyword in the parameter port list.
	// If you do so, we "inherit" the parameter or localparam keyword from the previous entry.
	// This isn't allowed in a module body, but the parser will take care of the error for us.
	bool local = false;
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

		auto location = declarator->name.location();
		auto pair = nameDupMap.try_emplace(name, location);
		if (!pair.second) {
			diagnostics.add(DiagCode::DuplicateParameter, location) << name;
			diagnostics.add(DiagCode::NotePreviousDefinition, pair.first->second);
		}
		else {
			ExpressionSyntax* init = nullptr;
			if (declarator->initializer)
				init = declarator->initializer->expr;
			else if (local)
				diagnostics.add(DiagCode::LocalParamNoInitializer, location);
			else if (bodyParam)
				diagnostics.add(DiagCode::BodyParamNoInitializer, location);
			buffer.append(alloc.emplace<ParameterSymbol>(name, location, p, init, local));
		}
	}
	return local;
}

void SemanticModel::evaluateParameter(ParameterSymbol* parameter) {
	// If no type is given, infer the type from the initializer
	DataTypeSyntax* typeSyntax = parameter->syntax->type;
	if (!typeSyntax) {
		BoundExpression* expr = binder.bindSelfDeterminedExpression(parameter->initializer);
		parameter->type = expr->type;
		parameter->value = expr->constantValue;
	}
	else {
		// TODO
	}
}

const TypeSymbol* SemanticModel::getKnownType(SyntaxKind kind) const {
	auto it = knownTypes.find(kind);
	if (it == knownTypes.end())
		return getErrorType();
	return it->second;
}

const TypeSymbol* SemanticModel::getIntegralType(int width, bool isSigned, bool isFourState) {
	std::unordered_map<int, const TypeSymbol*>& cache = integralTypeCache[isFourState][isSigned]; // always use the 4-state cache

	auto it = cache.find(width);
	if (it != cache.end())
		return it->second;

	it = cache.emplace_hint(it, width, alloc.emplace<IntegralTypeSymbol>(width, isSigned, true));
	return it->second;
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