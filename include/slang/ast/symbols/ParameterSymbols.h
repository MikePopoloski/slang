//------------------------------------------------------------------------------
//! @file ParameterSymbols.h
//! @brief Contains parameter-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/SemanticFacts.h"
#include "slang/ast/symbols/ValueSymbol.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

class Compilation;

class SLANG_EXPORT ParameterSymbolBase {
public:
    const Symbol& symbol;
    const syntax::SyntaxNode* defaultValSyntax = nullptr;

    bool isLocalParam() const { return isLocal; }
    bool isPortParam() const { return isPort; }
    bool isBodyParam() const { return !isPortParam(); }

    void checkDefaultExpression() const;

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
    ParameterSymbol(std::string_view name, SourceLocation loc, bool isLocal, bool isPort);

    static void fromSyntax(const Scope& scope, const syntax::ParameterDeclarationSyntax& syntax,
                           bool isLocal, bool isPort, SmallVectorBase<ParameterSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Parameter; }

    const ConstantValue& getValue(SourceRange referencingRange = {}) const;
    void setValue(Compilation& compilation, ConstantValue value, bool needsCoercion);

    bool isImplicitString(SourceRange referencingRange) const;
    bool isOverridden() const;

    bool isFromConfig() const { return isFromConf; }
    void setIsFromConfig(bool newIsFromConf) { isFromConf = newIsFromConf; }

    bool isFromGenvar() const { return isFromGv; }
    void setIsFromGenvar(bool newIsFromGenvar) { isFromGv = newIsFromGenvar; }

    void serializeTo(ASTSerializer& serializer) const;

private:
    mutable const ConstantValue* value = nullptr;
    mutable bool fromStringLit = false;
    mutable bool needsCoercion = false;
    mutable bool evaluating = false;
    bool isFromConf = false;
    bool isFromGv = false;
};

class SLANG_EXPORT TypeParameterSymbol : public Symbol, public ParameterSymbolBase {
public:
    DeclaredType targetType;
    ForwardTypeRestriction typeRestriction;

    TypeParameterSymbol(const Scope& scope, std::string_view name, SourceLocation loc, bool isLocal,
                        bool isPort, ForwardTypeRestriction typeRestriction);

    static void fromSyntax(const Scope& scope, const syntax::TypeParameterDeclarationSyntax& syntax,
                           bool isLocal, bool isPort,
                           SmallVectorBase<TypeParameterSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::TypeParameter; }

    const Type& getTypeAlias() const { return *typeAlias; }
    bool isOverridden() const;
    void checkTypeRestriction() const;

    void serializeTo(ASTSerializer& serializer) const;

private:
    const Type* typeAlias;
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
    bool isPathPulse = false;

    SpecparamSymbol(std::string_view name, SourceLocation loc);

    const ConstantValue& getValue(SourceRange referencingRange = {}) const;

    const ConstantValue& getPulseRejectLimit() const;
    const ConstantValue& getPulseErrorLimit() const;

    const Symbol* getPathSource() const {
        if (!pathPulseResolved)
            resolvePathPulse();
        return pathSource;
    }

    const Symbol* getPathDest() const {
        if (!pathPulseResolved)
            resolvePathPulse();
        return pathDest;
    }

    static void fromSyntax(const Scope& scope, const syntax::SpecparamDeclarationSyntax& syntax,
                           SmallVectorBase<const SpecparamSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Specparam; }

    void serializeTo(ASTSerializer& serializer) const;

private:
    void resolvePathPulse() const;
    const Symbol* resolvePathTerminal(std::string_view terminalName, const Scope& parent,
                                      SourceLocation loc, bool isSource) const;

    mutable const ConstantValue* value1 = nullptr;
    mutable const ConstantValue* value2 = nullptr;
    mutable const Symbol* pathSource = nullptr;
    mutable const Symbol* pathDest = nullptr;
    mutable bool evaluating = false;
    mutable bool pathPulseResolved = false;
};

} // namespace slang::ast
