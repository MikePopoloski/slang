//------------------------------------------------------------------------------
//! @file NetType.h
//! @brief Type class for nettypes
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/Symbol.h"
#include "slang/types/DeclaredType.h"

namespace slang {

class SubroutineSymbol;
struct NetTypeDeclarationSyntax;

/// Base class for all net types in SystemVerilog.
///
/// There is a parallel type system for nets that exists independently from the data type
/// system. Most nets will be one of the built in types, but user defined net types can
/// exist too.
///
class NetType : public Symbol {
public:
    enum NetKind {
        Unknown,
        Wire,
        WAnd,
        WOr,
        Tri,
        TriAnd,
        TriOr,
        Tri0,
        Tri1,
        TriReg,
        Supply0,
        Supply1,
        UWire,
        UserDefined
    } netKind;

    NetType(NetKind netKind, string_view name, const Type& dataType);
    NetType(string_view name, SourceLocation location);

    /// If this net type is an alias, gets the target of the alias. Otherwise returns nullptr.
    const NetType* getAliasTarget() const;

    /// Gets the canonical net type for this net type, which involves unwrapping any aliases.
    const NetType& getCanonical() const;

    /// Gets the data type for nets of this particular net type.
    const Type& getDataType() const;

    /// Gets the custom resolution function for this net type, if it has one.
    const SubroutineSymbol* getResolutionFunction() const;

    bool isError() const { return netKind == Unknown; }
    bool isBuiltIn() const { return netKind != UserDefined; }

    void serializeTo(ASTSerializer& serializer) const;

    static NetType& fromSyntax(const Scope& scope, const NetTypeDeclarationSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::NetType; }

private:
    friend class Symbol;
    friend class NetSymbol;

    void resolve() const;

    mutable DeclaredType declaredType;

    mutable const NetType* alias = nullptr;
    mutable const SubroutineSymbol* resolver = nullptr;
    mutable bool isResolved = false;
};

} // namespace slang
