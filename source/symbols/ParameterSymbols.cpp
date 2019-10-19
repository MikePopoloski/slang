//------------------------------------------------------------------------------
// ParameterSymbols.cpp
// Contains parameter-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/ParameterSymbols.h"

#include <nlohmann/json.hpp>

#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/symbols/TypeSymbols.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

bool ParameterSymbolBase::hasDefault() const {
    if (symbol.kind == SymbolKind::Parameter)
        return symbol.as<ParameterSymbol>().getDeclaredType()->getInitializerSyntax();
    else
        return symbol.as<TypeParameterSymbol>().targetType.getTypeSyntax();
}

ParameterSymbol::ParameterSymbol(string_view name, SourceLocation loc, bool isLocal, bool isPort) :
    ValueSymbol(SymbolKind::Parameter, name, loc,
                DeclaredTypeFlags::InferImplicit | DeclaredTypeFlags::RequireConstant),
    ParameterSymbolBase(*this, isLocal, isPort) {
}

void ParameterSymbol::fromSyntax(const Scope& scope, const ParameterDeclarationSyntax& syntax,
                                 bool isLocal, bool isPort,
                                 SmallVector<ParameterSymbol*>& results) {
    for (auto decl : syntax.declarators) {
        auto loc = decl->name.location();
        auto param = scope.getCompilation().emplace<ParameterSymbol>(decl->name.valueText(), loc,
                                                                     isLocal, isPort);
        param->setDeclaredType(*syntax.type);
        param->setFromDeclarator(*decl);

        if (!decl->initializer) {
            if (!isPort)
                scope.addDiag(diag::BodyParamNoInitializer, loc);
            else if (isLocal)
                scope.addDiag(diag::LocalParamNoInitializer, loc);
        }

        results.append(param);
    }
}

ParameterSymbol& ParameterSymbol::clone(Compilation& compilation) const {
    auto result =
        compilation.emplace<ParameterSymbol>(name, location, isLocalParam(), isPortParam());

    if (auto syntax = getSyntax())
        result->setSyntax(*syntax);

    auto declared = getDeclaredType();
    result->getDeclaredType()->copyTypeFrom(*declared);

    if (auto init = declared->getInitializerSyntax())
        result->setInitializerSyntax(*init, declared->getInitializerLocation());

    if (declared->hasInitializer())
        result->setInitializer(*declared->getInitializer());

    result->overriden = overriden;
    return *result;
}

const ConstantValue& ParameterSymbol::getValue() const {
    return overriden ? *overriden : getConstantValue();
}

void ParameterSymbol::setValue(ConstantValue value) {
    auto scope = getParentScope();
    ASSERT(scope);
    overriden = scope->getCompilation().allocConstant(std::move(value));
}

void ParameterSymbol::toJson(json& j) const {
    j["value"] = getValue();
    j["isLocal"] = isLocalParam();
    j["isPort"] = isPortParam();
    j["isBody"] = isBodyParam();
}

TypeParameterSymbol::TypeParameterSymbol(string_view name, SourceLocation loc, bool isLocal,
                                         bool isPort) :
    Symbol(SymbolKind::TypeParameter, name, loc),
    ParameterSymbolBase(*this, isLocal, isPort), targetType(*this) {
}

void TypeParameterSymbol::fromSyntax(const Scope& scope,
                                     const TypeParameterDeclarationSyntax& syntax, bool isLocal,
                                     bool isPort, SmallVector<TypeParameterSymbol*>& results) {
    auto& comp = scope.getCompilation();
    for (auto decl : syntax.declarators) {
        auto name = decl->name.valueText();
        auto loc = decl->name.location();

        auto param = comp.emplace<TypeParameterSymbol>(name, loc, isLocal, isPort);
        param->setSyntax(*decl);

        if (!decl->assignment) {
            if (!isPort)
                scope.addDiag(diag::BodyParamNoInitializer, loc);
            else if (isLocal)
                scope.addDiag(diag::LocalParamNoInitializer, loc);
        }
        else {
            param->targetType.setTypeSyntax(*decl->assignment->type);
        }

        results.append(param);
    }
}

TypeParameterSymbol& TypeParameterSymbol::clone(Compilation& comp) const {
    auto result = comp.emplace<TypeParameterSymbol>(name, location, isLocalParam(), isPortParam());
    if (auto syntax = getSyntax())
        result->setSyntax(*syntax);

    auto declared = getDeclaredType();
    result->targetType.copyTypeFrom(*declared);

    return *result;
}

const Type& TypeParameterSymbol::getTypeAlias() const {
    if (typeAlias)
        return *typeAlias;

    auto scope = getParentScope();
    ASSERT(scope);

    auto alias = scope->getCompilation().emplace<TypeAliasType>(name, location);
    if (auto syntax = getSyntax())
        alias->setSyntax(*syntax);

    alias->targetType.copyTypeFrom(targetType);
    alias->setParent(*scope);

    typeAlias = alias;
    return *typeAlias;
}

void TypeParameterSymbol::toJson(json& j) const {
    j["type"] = targetType.getType();
    j["isLocal"] = isLocalParam();
    j["isPort"] = isPortParam();
    j["isBody"] = isBodyParam();
}

} // namespace slang