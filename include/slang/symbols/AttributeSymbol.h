//------------------------------------------------------------------------------
// AttributeSymbol.h
// Symbol definition for source attributes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/Scope.h"
#include "slang/symbols/Symbol.h"

namespace slang {

struct AttributeInstanceSyntax;

class AttributeSymbol : public Symbol {
public:
    AttributeSymbol(string_view name, SourceLocation loc, const Scope& scope,
                    LookupLocation lookupLocation, const ExpressionSyntax& expr);

    AttributeSymbol(string_view name, SourceLocation loc, const ConstantValue& value);

    const ConstantValue& getValue() const;

    void toJson(json& j) const;

    static span<const AttributeSymbol* const> fromSyntax(
        span<const AttributeInstanceSyntax* const> syntax, const Scope& scope,
        LookupLocation lookupLocation);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Attribute; }

private:
    const Scope* scope = nullptr;
    const ExpressionSyntax* expr = nullptr;
    mutable const ConstantValue* value = nullptr;
    LookupLocation lookupLocation;
};

} // namespace slang