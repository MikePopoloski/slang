//------------------------------------------------------------------------------
//! @file AttributeSymbol.h
//! @brief Symbol definition for source attributes
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/Scope.h"
#include "slang/symbols/Symbol.h"
#include "slang/text/SourceLocation.h"

namespace slang {

struct AttributeInstanceSyntax;
struct ExpressionSyntax;

class AttributeSymbol : public Symbol {
public:
    AttributeSymbol(string_view name, SourceLocation loc, const Symbol& symbol,
                    const ExpressionSyntax& expr);

    AttributeSymbol(string_view name, SourceLocation loc, const Scope& scope,
                    LookupLocation lookupLocation, const ExpressionSyntax& expr);

    AttributeSymbol(string_view name, SourceLocation loc, const ConstantValue& value);

    const ConstantValue& getValue() const;

    void serializeTo(ASTSerializer& serializer) const;

    static span<const AttributeSymbol* const> fromSyntax(
        span<const AttributeInstanceSyntax* const> syntax, const Scope& scope,
        const Symbol& symbol);

    static span<const AttributeSymbol* const> fromSyntax(
        span<const AttributeInstanceSyntax* const> syntax, const Scope& scope,
        LookupLocation lookupLocation);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Attribute; }

private:
    const Symbol* symbol = nullptr;
    const Scope* scope = nullptr;
    const ExpressionSyntax* expr = nullptr;
    mutable const ConstantValue* value = nullptr;
    LookupLocation lookupLocation;
};

} // namespace slang
