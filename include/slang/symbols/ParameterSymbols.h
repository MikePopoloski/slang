//------------------------------------------------------------------------------
//! @file ParameterSymbols.h
//! @brief Contains parameter-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/compilation/Definition.h"
#include "slang/symbols/ValueSymbol.h"

namespace slang {

struct ClassPropertyDeclarationSyntax;
struct ParameterDeclarationStatementSyntax;

class ParameterSymbolBase {
public:
    const Symbol& symbol;

    bool isLocalParam() const { return isLocal; }
    bool isPortParam() const { return isPort; }
    bool isBodyParam() const { return !isPortParam(); }
    bool hasDefault() const;

    static void fromLocalSyntax(const Scope& scope,
                                const ParameterDeclarationStatementSyntax& syntax,
                                SmallVector<Symbol*>& results);

protected:
    ParameterSymbolBase(const Symbol& symbol, bool isLocal, bool isPort) :
        symbol(symbol), isLocal(isLocal), isPort(isPort) {}

private:
    bool isLocal = false;
    bool isPort = false;
};

struct ParameterDeclarationSyntax;

/// Represents a parameter value.
class ParameterSymbol : public ValueSymbol, public ParameterSymbolBase {
public:
    ParameterSymbol(string_view name, SourceLocation loc, bool isLocal, bool isPort);

    static void fromSyntax(const Scope& scope, const ParameterDeclarationSyntax& syntax,
                           bool isLocal, bool isPort, SmallVector<ParameterSymbol*>& results);

    static ParameterSymbol& fromDecl(const Definition::ParameterDecl& decl, Scope& newScope,
                                     const BindContext& context,
                                     const ExpressionSyntax* newInitializer);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Parameter; }

    ParameterSymbol& clone(Compilation& compilation) const;

    const ConstantValue& getValue() const;
    void setValue(ConstantValue value);

    bool isImplicitString() const;

    void serializeTo(ASTSerializer& serializer) const;

private:
    mutable const ConstantValue* value = nullptr;
    mutable bool fromStringLit = false;
};

struct TypeParameterDeclarationSyntax;

class TypeParameterSymbol : public Symbol, public ParameterSymbolBase {
public:
    DeclaredType targetType;

    TypeParameterSymbol(string_view name, SourceLocation loc, bool isLocal, bool isPort);

    static void fromSyntax(const Scope& scope, const TypeParameterDeclarationSyntax& syntax,
                           bool isLocal, bool isPort, SmallVector<TypeParameterSymbol*>& results);

    static TypeParameterSymbol& fromDecl(const Definition::ParameterDecl& decl, Scope& newScope,
                                         const BindContext& context,
                                         const ExpressionSyntax* newInitializer);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::TypeParameter; }

    TypeParameterSymbol& clone(Compilation& compilation) const;

    const Type& getTypeAlias() const;

    void serializeTo(ASTSerializer& serializer) const;

private:
    mutable const Type* typeAlias = nullptr;
};

struct DefParamSyntax;

/// Represents a defparam directive.
class DefParamSymbol : public Symbol {
public:
    explicit DefParamSymbol(SourceLocation loc) : Symbol(SymbolKind::DefParam, "", loc) {}

    const Symbol* getTarget() const;
    const Expression& getInitializer() const;
    const ConstantValue& getValue() const;

    static void fromSyntax(const Scope& scope, const DefParamSyntax& syntax,
                           SmallVector<const DefParamSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::DefParam; }

    void serializeTo(ASTSerializer& serializer) const;

private:
    void resolve() const;

    mutable const Expression* initializer = nullptr;
    mutable const Symbol* target = nullptr;
};

struct SpecparamDeclarationSyntax;

/// Represents a specify parameter.
class SpecparamSymbol : public ValueSymbol {
public:
    SpecparamSymbol(string_view name, SourceLocation loc);

    const ConstantValue& getValue() const;

    static void fromSyntax(const Scope& scope, const SpecparamDeclarationSyntax& syntax,
                           SmallVector<const SpecparamSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Specparam; }

    void serializeTo(ASTSerializer& serializer) const;

private:
    mutable const ConstantValue* value = nullptr;
};

} // namespace slang
