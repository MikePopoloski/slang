//------------------------------------------------------------------------------
//! @file ParameterSymbols.h
//! @brief Contains parameter-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/symbols/ValueSymbol.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

class SLANG_EXPORT ParameterSymbolBase {
public:
    const Symbol& symbol;

    bool isLocalParam() const { return isLocal; }
    bool isPortParam() const { return isPort; }
    bool isBodyParam() const { return !isPortParam(); }
    bool hasDefault() const;

    static void fromLocalSyntax(const Scope& scope,
                                const syntax::ParameterDeclarationStatementSyntax& syntax,
                                SmallVectorBase<Symbol*>& results);

protected:
    ParameterSymbolBase(const Symbol& symbol, bool isLocal, bool isPort) :
        symbol(symbol), isLocal(isLocal), isPort(isPort) {}

private:
    bool isLocal = false;
    bool isPort = false;
};

/// Represents a parameter value.
class SLANG_EXPORT ParameterSymbol : public ValueSymbol, public ParameterSymbolBase {
public:
    ParameterSymbol(string_view name, SourceLocation loc, bool isLocal, bool isPort);

    static void fromSyntax(const Scope& scope, const syntax::ParameterDeclarationSyntax& syntax,
                           bool isLocal, bool isPort, SmallVectorBase<ParameterSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Parameter; }

    const ConstantValue& getValue(SourceRange referencingRange = {}) const;
    void setValue(Compilation& compilation, ConstantValue value, bool needsCoercion);

    bool isImplicitString(SourceRange referencingRange) const;

    void serializeTo(ASTSerializer& serializer) const;

private:
    mutable const ConstantValue* value = nullptr;
    mutable bool fromStringLit = false;
    mutable bool needsCoercion = false;
    mutable bool evaluating = false;
};

class SLANG_EXPORT TypeParameterSymbol : public Symbol, public ParameterSymbolBase {
public:
    DeclaredType targetType;

    TypeParameterSymbol(string_view name, SourceLocation loc, bool isLocal, bool isPort);

    static void fromSyntax(const Scope& scope, const syntax::TypeParameterDeclarationSyntax& syntax,
                           bool isLocal, bool isPort,
                           SmallVectorBase<TypeParameterSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::TypeParameter; }

    const Type& getTypeAlias() const;

    void serializeTo(ASTSerializer& serializer) const;

private:
    mutable const Type* typeAlias = nullptr;
};

/// Represents a defparam directive.
class SLANG_EXPORT DefParamSymbol : public Symbol {
public:
    explicit DefParamSymbol(SourceLocation loc) : Symbol(SymbolKind::DefParam, "", loc) {}

    const Symbol* getTarget() const;
    const Expression& getInitializer() const;
    const ConstantValue& getValue() const;

    static void fromSyntax(const Scope& scope, const syntax::DefParamSyntax& syntax,
                           SmallVectorBase<const DefParamSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::DefParam; }

    void serializeTo(ASTSerializer& serializer) const;

private:
    void resolve() const;

    mutable const Expression* initializer = nullptr;
    mutable const Symbol* target = nullptr;
};

/// Represents a specify parameter.
class SLANG_EXPORT SpecparamSymbol : public ValueSymbol {
public:
    SpecparamSymbol(string_view name, SourceLocation loc);

    const ConstantValue& getValue(SourceRange referencingRange = {}) const;

    static void fromSyntax(const Scope& scope, const syntax::SpecparamDeclarationSyntax& syntax,
                           SmallVectorBase<const SpecparamSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Specparam; }

    void serializeTo(ASTSerializer& serializer) const;

private:
    mutable const ConstantValue* value = nullptr;
    mutable bool evaluating = false;
};

} // namespace slang::ast
