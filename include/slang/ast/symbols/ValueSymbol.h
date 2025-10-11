//------------------------------------------------------------------------------
//! @file ValueSymbol.h
//! @brief Base class for all value symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Symbol.h"
#include "slang/ast/types/DeclaredType.h"

namespace slang::ast {

class PortSymbol;

/// A base class for symbols that represent a value (for example a variable or a parameter).
/// The common functionality is that they all have a type.
class SLANG_EXPORT ValueSymbol : public Symbol {
public:
    /// Gets the type of the value.
    const Type& getType() const { return declaredType.getType(); }

    /// Sets the type of the value.
    void setType(const Type& type) { declaredType.setType(type); }

    /// Gets access to the symbol's declared type.
    not_null<const DeclaredType*> getDeclaredType() const { return &declaredType; }
    not_null<DeclaredType*> getDeclaredType() { return &declaredType; }

    /// Sets the symbol's declared type.
    void setDeclaredType(const syntax::DataTypeSyntax& newType) {
        declaredType.setTypeSyntax(newType);
    }
    void setDeclaredType(const syntax::DataTypeSyntax& newType,
                         const syntax::SyntaxList<syntax::VariableDimensionSyntax>& newDimensions) {
        declaredType.setTypeSyntax(newType);
        declaredType.setDimensionSyntax(newDimensions);
    }

    /// Gets the initializer for this value, if it has one.
    const Expression* getInitializer() const { return declaredType.getInitializer(); }

    /// Sets the initializer for this value.
    void setInitializer(const Expression& expr) { declaredType.setInitializer(expr); }

    /// Sets the expression tree used to initialize this value.
    void setInitializerSyntax(const syntax::ExpressionSyntax& syntax, SourceLocation initLocation) {
        declaredType.setInitializerSyntax(syntax, initLocation);
    }

    /// Initializes the value's dimension and initializer syntax from the given declarator.
    void setFromDeclarator(const syntax::DeclaratorSyntax& decl);

    static bool isKind(SymbolKind kind);

    class PortBackref {
    public:
        not_null<const PortSymbol*> port;

        PortBackref(const PortSymbol& port, const PortBackref* next) : port(&port), next(next) {}

        const PortBackref* getNextBackreference() const { return next; }

    private:
        const PortBackref* next;
    };

    void addPortBackref(const PortSymbol& port) const;
    const PortBackref* getFirstPortBackref() const { return firstPortBackref; }

    bool isConnectedToRefPort() const;

protected:
    ValueSymbol(SymbolKind kind, std::string_view name, SourceLocation location,
                bitmask<DeclaredTypeFlags> flags = DeclaredTypeFlags::None);

private:
    DeclaredType declaredType;
    mutable const PortBackref* firstPortBackref = nullptr;
};

} // namespace slang::ast
