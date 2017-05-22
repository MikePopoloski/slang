#include "Symbol.h"

#include "analysis/SemanticModel.h"
#include "diagnostics/Diagnostics.h"

namespace slang {

static int zero = 0;
ArrayRef<int> IntegralTypeSymbol::EmptyLowerBound { &zero, 1 };

bool isDefaultSigned(TokenKind kind) {
    return false;
}

bool TypeSymbol::isMatching(const TypeSymbol& rhs) const {
    return true;
}

bool TypeSymbol::isEquivalent(const TypeSymbol& rhs) const {
    if (isMatching(rhs))
        return true;

    return true;
}

bool TypeSymbol::isAssignmentCompatible(const TypeSymbol& rhs) const {
    if (isEquivalent(rhs))
        return true;

    return true;
}

bool TypeSymbol::isCastCompatible(const TypeSymbol& rhs) const {
    if (isAssignmentCompatible(rhs))
        return true;

    return true;
}

std::string TypeSymbol::toString() const {
    std::string result;
    switch (kind) {
        case SymbolKind::IntegralType: {
            const auto& s = as<IntegralTypeSymbol>();
            result = name.toString();
            if (isDefaultSigned(s.keywordType) != s.isSigned)
                result += s.isSigned ? " signed" : " unsigned";
            break;
        }
        case SymbolKind::RealType:
            result = name.toString();
            break;
        /*case SymbolKind::Instance: {
            result = name.toString();
            auto ia = as<InstanceSymbol>();
            for (auto r : ia.dimensions)
                result += "[" + r.left.toString(LiteralBase::Decimal) +
                          ":" + r.right.toString(LiteralBase::Decimal) + "]";
            break;
        }*/
        default:
            break;
    }
    return "'" + result + "'";
}

bool TypeSymbol::isSigned() const {
    switch (kind) {
        case SymbolKind::IntegralType: return as<IntegralTypeSymbol>().isSigned;
        case SymbolKind::RealType: return true;
        default: return false;
    }
}

bool TypeSymbol::isFourState() const {
    switch (kind) {
        case SymbolKind::IntegralType: return as<IntegralTypeSymbol>().isFourState;
        case SymbolKind::RealType: return false;
        default: return false;
    }
}

bool TypeSymbol::isReal() const {
    switch (kind) {
        case SymbolKind::IntegralType: return false;
        case SymbolKind::RealType: return true;
        default: return false;
    }
}

int TypeSymbol::width() const {
    switch (kind) {
        case SymbolKind::IntegralType: return as<IntegralTypeSymbol>().width;
        case SymbolKind::RealType: return as<RealTypeSymbol>().width;
        default: return 0;
    }
}

ModuleSymbol::ModuleSymbol(const ModuleDeclarationSyntax& decl, const Symbol& parent) :
	Symbol(SymbolKind::Module, decl.header.name, &parent), decl(decl)
{
}

const ParameterizedModuleSymbol& ModuleSymbol::parameterize(const ParameterValueAssignmentSyntax* assignments, const ScopeSymbol* instanceScope) const {
	ASSERT(!assignments || instanceScope);

	// If we were given a set of parameter assignments, build up some data structures to
	// allow us to easily index them. We need to handle both ordered assignment as well as
	// named assignment (though a specific instance can only use one method or the other).
	bool hasParamAssignments = false;
	bool orderedAssignments = true;
	SmallVectorSized<const OrderedArgumentSyntax*, 8> orderedParams;
	SmallHashMap<StringRef, std::pair<const NamedArgumentSyntax*, bool>, 8> namedParams;

	if (assignments) {
		for (auto paramBase : assignments->parameters.parameters) {
			bool isOrdered = paramBase->kind == SyntaxKind::OrderedArgument;
			if (!hasParamAssignments) {
				hasParamAssignments = true;
				orderedAssignments = isOrdered;
			}
			else if (isOrdered != orderedAssignments) {
				addError(DiagCode::MixingOrderedAndNamedParams, paramBase->getFirstToken().location());
				break;
			}

			if (isOrdered)
				orderedParams.append(&paramBase->as<OrderedArgumentSyntax>());
			else {
				const NamedArgumentSyntax& nas = paramBase->as<NamedArgumentSyntax>();
				auto pair = namedParams.emplace(nas.name.valueText(), std::make_pair(&nas, false));
				if (!pair.second) {
					addError(DiagCode::DuplicateParamAssignment, nas.name.location()) << nas.name.valueText();
					addError(DiagCode::NotePreviousUsage, pair.first->second.first->name.location());
				}
			}
		}
	}

	// For each parameter assignment we have, match it up to a real parameter and evaluate its initializer.
	SmallHashMap<StringRef, ConstantValue, 8> paramMap;
	if (orderedAssignments) {
		// We take this branch if we had ordered parameter assignments,
		// or if we didn't have any parameter assignments at all.
		uint32_t orderedIndex = 0;
		for (const auto& info : getDeclaredParams()) {
			if (orderedIndex >= orderedParams.count())
				break;

			if (info.local)
				continue;

			paramMap[info.name] = evaluate(info.paramDecl, *instanceScope, orderedParams[orderedIndex++]->expr);
		}

		// Make sure there aren't extra param assignments for non-existent params.
		if (orderedIndex < orderedParams.count()) {
			auto& diag = addError(DiagCode::TooManyParamAssignments, orderedParams[orderedIndex]->getFirstToken().location());
			diag << decl.header.name.valueText();
			diag << orderedParams.count();
			diag << orderedIndex;
		}
	}
	else {
		// Otherwise handle named assignments.
		for (const auto& info : getDeclaredParams()) {
			auto it = namedParams.find(info.name);
			if (it == namedParams.end())
				continue;

			const NamedArgumentSyntax* arg = it->second.first;
			it->second.second = true;
			if (info.local) {
				// Can't assign to localparams, so this is an error.
				addError(info.bodyParam ? DiagCode::AssignedToLocalBodyParam : DiagCode::AssignedToLocalPortParam, arg->name.location());
				addError(DiagCode::NoteDeclarationHere, info.location) << StringRef("parameter");
				continue;
			}

			// It's allowed to have no initializer in the assignment; it means to just use the default
			if (!arg->expr)
				continue;

			paramMap[info.name] = evaluate(info.paramDecl, *instanceScope, *arg->expr);
		}

		for (const auto& pair : namedParams) {
			// We marked all the args that we used, so anything left over is a param assignment
			// for a non-existent parameter.
			if (!pair.second.second) {
				auto& diag = addError(DiagCode::ParameterDoesNotExist, pair.second.first->name.location());
				diag << pair.second.first->name.valueText();
				diag << decl.header.name.valueText();
			}
		}
	}

	return allocate<ParameterizedModuleSymbol>(*this, paramMap);
}

ConstantValue ModuleSymbol::evaluate(const ParameterDeclarationSyntax& paramDecl, const ScopeSymbol& scope, const ExpressionSyntax& expr) const {
	// If no type is given, infer the type from the initializer
	if (paramDecl.type.kind == SyntaxKind::ImplicitType)
		return scope.evaluateConstant(expr);
	else {
		const TypeSymbol& type = scope.getType(paramDecl.type);
		return scope.evaluateConstantAndConvert(expr, type);
	}
}

const std::vector<ModuleSymbol::ParameterInfo>& ModuleSymbol::getDeclaredParams() const {
    if (!paramInfoCache) {
        // Discover all of the element's parameters. If we have a parameter port list, the only
        // publicly visible parameters are the ones in that list. Otherwise, parameters declared
        // in the module body are publicly visible.
        const ModuleHeaderSyntax& header = decl.header;
        SmallHashMap<StringRef, SourceLocation, 16> nameDupMap;
        std::vector<ParameterInfo> buffer;

        bool overrideLocal = false;
        if (header.parameters) {
            bool lastLocal = false;
            for (const ParameterDeclarationSyntax* paramDecl : header.parameters->declarations)
                lastLocal = getParamDecls(*paramDecl, buffer, nameDupMap, lastLocal, false, false);
            overrideLocal = true;
        }

        // also find direct body parameters
        for (const MemberSyntax* member : decl.members) {
            if (member->kind == SyntaxKind::ParameterDeclarationStatement)
                getParamDecls(member->as<ParameterDeclarationStatementSyntax>().parameter, buffer,
                    nameDupMap, false, overrideLocal, true);
        }

		paramInfoCache = std::move(buffer);
    }
    return *paramInfoCache;
}

bool ModuleSymbol::getParamDecls(const ParameterDeclarationSyntax& syntax, std::vector<ParameterInfo>& buffer,
                                 HashMapBase<StringRef, SourceLocation>& nameDupMap,
                                 bool lastLocal, bool overrideLocal, bool bodyParam) const {
    // It's legal to leave off the parameter keyword in the parameter port list.
    // If you do so, we "inherit" the parameter or localparam keyword from the previous entry.
    // This isn't allowed in a module body, but the parser will take care of the error for us.
    bool local = false;
    if (!syntax.keyword)
        local = lastLocal;
    else {
        // In the body of a module that has a parameter port list in its header, parameters are
        // actually just localparams. overrideLocal will be true in this case.
        local = syntax.keyword.kind == TokenKind::LocalParamKeyword || overrideLocal;
    }

    for (const VariableDeclaratorSyntax* declarator : syntax.declarators) {
        auto name = declarator->name.valueText();
        if (!name)
            continue;

        auto location = declarator->name.location();
        auto pair = nameDupMap.emplace(name, location);
        if (!pair.second) {
            addError(DiagCode::DuplicateDefinition, location) << StringRef("parameter") << name;
			addError(DiagCode::NotePreviousDefinition, pair.first->second);
        }
        else {
            ExpressionSyntax* init = nullptr;
            if (declarator->initializer)
                init = &declarator->initializer->expr;
            else if (local)
				addError(DiagCode::LocalParamNoInitializer, location);
            else if (bodyParam)
				addError(DiagCode::BodyParamNoInitializer, location);
            buffer.push_back({ syntax, *declarator, name, location, init, local, bodyParam });
        }
    }
    return local;
}

SymbolList ParameterizedModuleSymbol::members() const {
	return nullptr;
}

}
