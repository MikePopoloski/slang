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

/// @brief Base class for all net types in SystemVerilog.
///
/// There is a parallel type system for nets that exists independently from the data type
/// system. Most nets will be one of the built in types, but user defined net types can
/// exist too.
///
class SLANG_EXPORT NetType : public Symbol {
public:
    /// The declared type of the net.
    DeclaredType declaredType;

    /// The specific kind of net.
    enum NetKind {
        /// Unknown (i.e. an error of some sort).
        Unknown,

        /// A wire.
        Wire,

        /// A wire that ANDs multiple drivers.
        WAnd,

        /// A wire that ORs multiple drivers.
        WOr,

        /// Same as 'wire'.
        Tri,

        /// Same as 'wand'.
        TriAnd,

        /// Same as 'wor'.
        TriOr,

        /// A wire that with a resistive pull down.
        Tri0,

        /// A wire that with a resistive pull up.
        Tri1,

        /// A net that stores a value and is used to model charge storage nodes.
        TriReg,

        /// A net that models a power supply with supply0 strength.
        Supply0,

        /// A net that models a power supply with supply1 strength.
        Supply1,

        /// A single-driver net that does not permit conflicts.
        UWire,

        /// A generic interconnect net.
        Interconnect,

        /// A user-defined nettype.
        UserDefined
    } netKind;

    NetType(NetKind netKind, std::string_view name, const Type& dataType);
    NetType(std::string_view name, SourceLocation location);

    /// Gets the data type for nets of this particular net type.
    const Type& getDataType() const { return declaredType.getType(); }

    /// Gets the custom resolution function for this net type, if it has one.
    const SubroutineSymbol* getResolutionFunction() const;

    /// @returns true if this is an error nettype.
    bool isError() const { return netKind == Unknown; }

    /// @returns true if this nettype is built-in (i.e. not user-defined).
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
