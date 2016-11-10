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
			// TODO: body parameters must alawys have initializers
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
		BoundExpression* expr = binder.bindSelfDeterminedExpression(parameter->initializer);
		parameter->type = expr->type;
		parameter->value = expr->constantValue;
	}
	else {
		// TODO
	}
}

const TypeSymbol* SemanticModel::getIntegralType(int width, bool isSigned) {
	std::unordered_map<int, const TypeSymbol*>& cache = integralTypeCache[true][isSigned]; // always use the 4-state cache

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