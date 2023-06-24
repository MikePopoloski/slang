//------------------------------------------------------------------------------
//! @file NetType.h
//! @brief Type class for nettypes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Symbol.h"
#include "slang/ast/types/DeclaredType.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

class ASTSerializer;
class SubroutineSymbol;

/// Base class for all net types in SystemVerilog.
///
/// There is a parallel type system for nets that exists independently from the data type
/// system. Most nets will be one of the built in types, but user defined net types can
/// exist too.
///
class SLANG_EXPORT NetType : public Symbol {
public:
    DeclaredType declaredType;

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
        Interconnect,
        UserDefined
    } netKind;

    NetType(NetKind netKind, std::string_view name, const Type& dataType);
    NetType(std::string_view name, SourceLocation location);

    /// Gets the data type for nets of this particular net type.
    const Type& getDataType() const { return declaredType.getType(); }

    /// Gets the custom resolution function for this net type, if it has one.
    const SubroutineSymbol* getResolutionFunction() const;

    bool isError() const { return netKind == Unknown; }
    bool isBuiltIn() const { return netKind != UserDefined; }

    void serializeTo(ASTSerializer& serializer) const;

    static NetType& fromSyntax(const Scope& scope, const syntax::NetTypeDeclarationSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::NetType; }

    static const NetType& getSimulatedNetType(const NetType& internal, const NetType& external,
                                              bool& shouldWarn);

private:
    mutable std::optional<const SubroutineSymbol*> resolver;
};

} // namespace slang::ast
