//------------------------------------------------------------------------------
// AttributeSymbol.cpp
// Symbol definition for source attributes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/AttributeSymbol.h"

#include <nlohmann/json.hpp>

#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/StackContainer.h"

namespace slang {

AttributeSymbol::AttributeSymbol(string_view name, SourceLocation loc, const Scope& scope,
                                 LookupLocation lookupLocation, const ExpressionSyntax& expr) :
    Symbol(SymbolKind::Attribute, name, loc),
    scope(&scope), expr(&expr), lookupLocation(lookupLocation) {
}

AttributeSymbol::AttributeSymbol(string_view name, SourceLocation loc, const ConstantValue& value) :
    Symbol(SymbolKind::Attribute, name, loc), value(&value) {
}

const ConstantValue& AttributeSymbol::getValue() const {
    if (!value) {
        ASSERT(expr);
        ASSERT(scope);

        BindContext context(*scope, lookupLocation, BindFlags::Constant | BindFlags::NoAttributes);
        auto& bound = Expression::bind(*expr, context);

        if (bound.constant)
            value = bound.constant;
        else
            value = scope->getCompilation().allocConstant(ConstantValue());
    }

    return *value;
}

void AttributeSymbol::toJson(json& j) const {
    j["value"] = getValue();
}

span<const AttributeSymbol* const> AttributeSymbol::fromSyntax(
    span<const AttributeInstanceSyntax* const> syntax, const Scope& scope,
    LookupLocation lookupLocation) {

    if (syntax.empty())
        return {};

    SmallMap<string_view, size_t, 4> nameMap;
    SmallVectorSized<const AttributeSymbol*, 8> attrs;

    auto& comp = scope.getCompilation();
    for (auto inst : syntax) {
        for (auto spec : inst->specs) {
            auto name = spec->name.valueText();
            if (name.empty())
                continue;

            AttributeSymbol* attr;
            if (!spec->value) {
                ConstantValue value = SVInt(1, 1, false);
                attr = comp.emplace<AttributeSymbol>(name, spec->name.location(),
                                                     *comp.allocConstant(std::move(value)));
            }
            else {
                attr = comp.emplace<AttributeSymbol>(name, spec->name.location(), scope,
                                                     lookupLocation, *spec->value->expr);
            }

            attr->setSyntax(*spec);

            if (auto it = nameMap.find(name); it != nameMap.end()) {
                scope.addDiag(diag::DuplicateAttribute, attr->location) << name;
                attrs[it->second] = attr;
            }
            else {
                attrs.append(attr);
                nameMap.emplace(name, attrs.size() - 1);
            }
        }
    }

    return attrs.copy(comp);
}

} // namespace slang