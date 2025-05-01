//------------------------------------------------------------------------------
// AttributeSymbol.cpp
// Symbol definition for source attributes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/AttributeSymbol.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/Expression.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace syntax;

AttributeSymbol::AttributeSymbol(std::string_view name, SourceLocation loc, const Symbol& symbol,
                                 const ExpressionSyntax& expr) :
    Symbol(SymbolKind::Attribute, name, loc), symbol(&symbol), expr(&expr) {
}

AttributeSymbol::AttributeSymbol(std::string_view name, SourceLocation loc, const Scope& scope,
                                 LookupLocation lookupLocation, const ExpressionSyntax& expr) :
    Symbol(SymbolKind::Attribute, name, loc), scope(&scope), expr(&expr),
    lookupLocation(lookupLocation) {
}

AttributeSymbol::AttributeSymbol(std::string_view name, SourceLocation loc,
                                 const ConstantValue& value) :
    Symbol(SymbolKind::Attribute, name, loc), value(&value) {
}

const ConstantValue& AttributeSymbol::getValue() const {
    if (!value) {
        LookupLocation loc = lookupLocation;
        auto bindScope = scope;
        if (symbol) {
            bindScope = symbol->getParentScope();
            loc = LookupLocation::before(*symbol);
        }

        SLANG_ASSERT(bindScope);
        SLANG_ASSERT(expr);

        ASTContext context(*bindScope, loc, ASTFlags::NonProcedural);
        auto& bound = Expression::bind(*expr, context);

        value = bindScope->getCompilation().allocConstant(context.eval(bound));
    }

    return *value;
}

void AttributeSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("value", getValue());
}

template<typename TFunc>
static std::span<const AttributeSymbol* const> createAttributes(
    std::span<const AttributeInstanceSyntax* const> syntax, const Scope& scope, TFunc&& factory) {

    SmallMap<std::string_view, size_t, 4> nameMap;
    SmallVector<const AttributeSymbol*> attrs;

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
                attr = factory(comp, name, spec->name.location(), *spec->value->expr);
            }

            attr->setSyntax(*spec);

            if (auto it = nameMap.find(name); it != nameMap.end()) {
                scope.addDiag(diag::DuplicateAttribute, attr->location) << name;
                attrs[it->second] = attr;
            }
            else {
                attrs.push_back(attr);
                nameMap.emplace(name, attrs.size() - 1);
            }
        }
    }

    return attrs.copy(comp);
}

std::span<const AttributeSymbol* const> AttributeSymbol::fromSyntax(
    std::span<const AttributeInstanceSyntax* const> syntax, const Scope& scope,
    const Symbol& symbol) {

    if (syntax.empty())
        return {};

    return createAttributes(
        syntax, scope, [&symbol](auto& comp, auto name, auto loc, auto& exprSyntax) {
            return comp.template emplace<AttributeSymbol>(name, loc, symbol, exprSyntax);
        });
}

std::span<const AttributeSymbol* const> AttributeSymbol::fromSyntax(
    std::span<const AttributeInstanceSyntax* const> syntax, const Scope& scope,
    LookupLocation lookupLocation) {

    if (syntax.empty())
        return {};

    return createAttributes(
        syntax, scope,
        [&scope, &lookupLocation](auto& comp, auto name, auto loc, auto& exprSyntax) {
            return comp.template emplace<AttributeSymbol>(name, loc, scope, lookupLocation,
                                                          exprSyntax);
        });
}

} // namespace slang::ast
