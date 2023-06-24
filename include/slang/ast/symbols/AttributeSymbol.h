//------------------------------------------------------------------------------
//! @file AttributeSymbol.h
//! @brief Symbol definition for source attributes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Symbol.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/text/SourceLocation.h"

namespace slang::ast {

class ASTSerializer;
class Scope;

class SLANG_EXPORT AttributeSymbol : public Symbol {
public:
    AttributeSymbol(std::string_view name, SourceLocation loc, const Symbol& symbol,
                    const syntax::ExpressionSyntax& expr);

    AttributeSymbol(std::string_view name, SourceLocation loc, const Scope& scope,
                    LookupLocation lookupLocation, const syntax::ExpressionSyntax& expr);

    AttributeSymbol(std::string_view name, SourceLocation loc, const ConstantValue& value);

    const ConstantValue& getValue() const;

    void serializeTo(ASTSerializer& serializer) const;

    static std::span<const AttributeSymbol* const> fromSyntax(
        std::span<const syntax::AttributeInstanceSyntax* const> syntax, const Scope& scope,
        const Symbol& symbol);

    static std::span<const AttributeSymbol* const> fromSyntax(
        std::span<const syntax::AttributeInstanceSyntax* const> syntax, const Scope& scope,
        LookupLocation lookupLocation);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Attribute; }

private:
    const Symbol* symbol = nullptr;
    const Scope* scope = nullptr;
    const syntax::ExpressionSyntax* expr = nullptr;
    mutable const ConstantValue* value = nullptr;
    LookupLocation lookupLocation;
};

} // namespace slang::ast
