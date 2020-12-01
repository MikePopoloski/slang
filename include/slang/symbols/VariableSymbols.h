//------------------------------------------------------------------------------
//! @file VariableSymbols.h
//! @brief Contains variable-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/ValueSymbol.h"

namespace slang {

class NetType;
class TimingControl;

struct IdentifierNameSyntax;
struct DataDeclarationSyntax;
struct ForVariableDeclarationSyntax;

/// Represents a variable declaration.
class VariableSymbol : public ValueSymbol {
public:
    VariableLifetime lifetime;

    /// The variable is marked constant and can't be modified.
    bool isConstant = false;

    /// The compiler created this variable, as opposed to
    /// it being declared in the user's source code.
    bool isCompilerGenerated = false;

    /// If this is a foreach loop variable, specifies a 1-based dimension index
    /// that this variable loops over. Otherwise this is zero.
    int32_t foreachIndex = 0;

    VariableSymbol(string_view name, SourceLocation loc, VariableLifetime lifetime);

    void serializeTo(ASTSerializer& serializer) const;

    /// Constructs all variable symbols specified by the given syntax node. Note that
    /// this might actually construct net symbols if the data type syntax refers to
    /// a user defined net type or alias.
    static void fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                           const Scope& scope, SmallVector<const ValueSymbol*>& results);

    static VariableSymbol& fromSyntax(Compilation& compilation,
                                      const ForVariableDeclarationSyntax& syntax,
                                      const VariableSymbol* lastVar);

    static VariableSymbol& fromForeachVar(Compilation& compilation,
                                          const IdentifierNameSyntax& syntax, int32_t foreachIndex);

    static bool isKind(SymbolKind kind) {
        return kind == SymbolKind::Variable || kind == SymbolKind::FormalArgument ||
               kind == SymbolKind::Field || kind == SymbolKind::ClassProperty;
    }

protected:
    VariableSymbol(SymbolKind childKind, string_view name, SourceLocation loc,
                   VariableLifetime lifetime) :
        ValueSymbol(childKind, name, loc),
        lifetime(lifetime) {}
};

/// Represents a formal argument in subroutine (task or function).
class FormalArgumentSymbol : public VariableSymbol {
public:
    ArgumentDirection direction = ArgumentDirection::In;

    FormalArgumentSymbol(string_view name, SourceLocation loc, ArgumentDirection direction,
                         VariableLifetime lifetime);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::FormalArgument; }
};

/// Represents a field member of a struct or union.
class FieldSymbol : public VariableSymbol {
public:
    /// The offset of the field within its parent structure or union. If the parent type is
    /// packed, this is an offset in bits. Otherwise it's an index into the list of fields.
    uint32_t offset;

    FieldSymbol(string_view name, SourceLocation loc, uint32_t offset) :
        VariableSymbol(SymbolKind::Field, name, loc, VariableLifetime::Automatic), offset(offset) {}

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Field; }
};

struct NetDeclarationSyntax;
struct UserDefinedNetDeclarationSyntax;

/// Represents a net declaration.
class NetSymbol : public ValueSymbol {
public:
    const NetType& netType;
    enum ExpansionHint { None, Vectored, Scalared } expansionHint = None;

    NetSymbol(string_view name, SourceLocation loc, const NetType& netType) :
        ValueSymbol(SymbolKind::Net, name, loc, DeclaredTypeFlags::NetType), netType(netType) {}

    const TimingControl* getDelay() const;

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(const Scope& scope, const NetDeclarationSyntax& syntax,
                           SmallVector<const NetSymbol*>& results);

    static void fromSyntax(const Scope& scope, const UserDefinedNetDeclarationSyntax& syntax,
                           LookupLocation location, SmallVector<const NetSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Net; }

private:
    mutable optional<const TimingControl*> delay;
};

} // namespace slang
