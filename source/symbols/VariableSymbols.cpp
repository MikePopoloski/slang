//------------------------------------------------------------------------------
// VariableSymbols.cpp
// Contains variable-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/VariableSymbols.h"

#include <nlohmann/json.hpp>

#include "slang/compilation/Compilation.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/TypeSymbols.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

void VariableSymbol::fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                                const Scope& scope, SmallVector<const ValueSymbol*>& results) {
    // TODO: check modifiers

    // This might actually be a net declaration with a user defined net type. That can only
    // be true if the data type syntax is a simple identifier, so if we see that it is,
    // perform a lookup and see what comes back.
    string_view simpleName = getSimpleTypeName(*syntax.type);
    if (!simpleName.empty()) {
        auto result = scope.lookupUnqualifiedName(simpleName, LookupLocation::max,
                                                  syntax.type->sourceRange());

        if (result && result->kind == SymbolKind::NetType) {
            const NetType& netType = result->as<NetType>();
            netType.getAliasTarget(); // force resolution of target

            auto& declaredType = *netType.getDeclaredType();
            for (auto declarator : syntax.declarators) {
                auto net = compilation.emplace<NetSymbol>(declarator->name.valueText(),
                                                          declarator->name.location(), netType);

                net->getDeclaredType()->copyTypeFrom(declaredType);
                net->setFromDeclarator(*declarator);
                results.append(net);
                compilation.addAttributes(*net, syntax.attributes);
            }
            return;
        }
    }

    for (auto declarator : syntax.declarators) {
        auto variable = compilation.emplace<VariableSymbol>(declarator->name.valueText(),
                                                            declarator->name.location());
        variable->setDeclaredType(*syntax.type);
        variable->setFromDeclarator(*declarator);
        results.append(variable);
    }
}

VariableSymbol& VariableSymbol::fromSyntax(Compilation& compilation,
                                           const ForVariableDeclarationSyntax& syntax,
                                           const VariableSymbol* lastVar) {
    auto var = compilation.emplace<VariableSymbol>(syntax.declarator->name.valueText(),
                                                   syntax.declarator->name.location());

    if (syntax.type)
        var->setDeclaredType(*syntax.type);
    else {
        ASSERT(lastVar);
        var->getDeclaredType()->copyTypeFrom(*lastVar->getDeclaredType());
    }

    var->setFromDeclarator(*syntax.declarator);
    return *var;
}

void VariableSymbol::toJson(json& j) const {
    j["lifetime"] = toString(lifetime);
    j["isConst"] = isConst;
}

void FormalArgumentSymbol::toJson(json& j) const {
    VariableSymbol::toJson(j);
    j["direction"] = toString(direction);
}

void FieldSymbol::toJson(json& j) const {
    VariableSymbol::toJson(j);
    j["offset"] = offset;
}

void NetSymbol::fromSyntax(Compilation& compilation, const NetDeclarationSyntax& syntax,
                           SmallVector<const NetSymbol*>& results) {

    // TODO: other net features
    const NetType& netType = compilation.getNetType(syntax.netType.kind);

    for (auto declarator : syntax.declarators) {
        auto net = compilation.emplace<NetSymbol>(declarator->name.valueText(),
                                                  declarator->name.location(), netType);

        net->setDeclaredType(*syntax.type, declarator->dimensions);
        net->setFromDeclarator(*declarator);
        results.append(net);
        compilation.addAttributes(*net, syntax.attributes);
    }
}

} // namespace slang