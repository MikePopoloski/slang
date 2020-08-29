//------------------------------------------------------------------------------
//! @file ClassSymbols.h
//! @brief Class-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/Scope.h"
#include "slang/symbols/Type.h"
#include "slang/symbols/VariableSymbols.h"

namespace slang {

struct ClassPropertyDeclarationSyntax;

class ClassPropertySymbol : public VariableSymbol {
public:
    Visibility visibility;
    uint32_t index;

    ClassPropertySymbol(string_view name, SourceLocation loc, VariableLifetime lifetime,
                        Visibility visibility, uint32_t index);

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(const Scope& scope, const ClassPropertyDeclarationSyntax& syntax,
                           SmallVector<const ClassPropertySymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ClassProperty; }
};

struct ClassDeclarationSyntax;

/// Represents a class definition type.
class ClassType : public Type, public Scope {
public:
    ClassType(Compilation& compilation, string_view name, SourceLocation loc);

    static const Type& fromSyntax(const Scope& scope, const ClassDeclarationSyntax& syntax);

    void addForwardDecl(const ForwardingTypedefSymbol& decl) const;
    const ForwardingTypedefSymbol* getFirstForwardDecl() const { return firstForward; }

    /// Checks all forward declarations for validity when considering the target type
    /// of this alias. Any inconsistencies will issue diagnostics.
    void checkForwardDecls() const;

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ClassType; }

private:
    mutable const ForwardingTypedefSymbol* firstForward = nullptr;
};

} // namespace slang
