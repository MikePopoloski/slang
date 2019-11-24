//------------------------------------------------------------------------------
// VariableSymbols.h
// Contains variable-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/Symbol.h"

namespace slang {

class NetType;

struct IdentifierNameSyntax;
struct DataDeclarationSyntax;
struct ForVariableDeclarationSyntax;

/// Represents a variable declaration.
class VariableSymbol : public ValueSymbol {
public:
    VariableLifetime lifetime;
    bool isConst;
    bool isCompilerGenerated = false;

    VariableSymbol(string_view name, SourceLocation loc,
                   VariableLifetime lifetime = VariableLifetime::Automatic, bool isConst = false) :
        VariableSymbol(SymbolKind::Variable, name, loc, lifetime, isConst) {}

    void toJson(json& j) const;

    /// Constructs all variable symbols specified by the given syntax node. Note that
    /// this might actually construct net symbols if the data type syntax refers to
    /// a user defined net type or alias.
    static void fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                           const Scope& scope, SmallVector<const ValueSymbol*>& results);

    static VariableSymbol& fromSyntax(Compilation& compilation,
                                      const ForVariableDeclarationSyntax& syntax,
                                      const VariableSymbol* lastVar);

    static VariableSymbol& fromForeachVar(Compilation& compilation,
                                          const IdentifierNameSyntax& syntax);

    static bool isKind(SymbolKind kind) {
        return kind == SymbolKind::Variable || kind == SymbolKind::FormalArgument ||
               kind == SymbolKind::Field;
    }

protected:
    VariableSymbol(SymbolKind childKind, string_view name, SourceLocation loc,
                   VariableLifetime lifetime = VariableLifetime::Automatic, bool isConst = false) :
        ValueSymbol(childKind, name, loc),
        lifetime(lifetime), isConst(isConst) {}
};

/// Represents a formal argument in subroutine (task or function).
class FormalArgumentSymbol : public VariableSymbol {
public:
    FormalArgumentDirection direction = FormalArgumentDirection::In;

    FormalArgumentSymbol() : VariableSymbol(SymbolKind::FormalArgument, "", SourceLocation()) {}

    FormalArgumentSymbol(string_view name, SourceLocation loc,
                         FormalArgumentDirection direction = FormalArgumentDirection::In) :
        VariableSymbol(SymbolKind::FormalArgument, name, loc, VariableLifetime::Automatic,
                       direction == FormalArgumentDirection::ConstRef),
        direction(direction) {}

    void toJson(json& j) const;

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

    void toJson(json& j) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Field; }
};

struct NetDeclarationSyntax;

/// Represents a net declaration.
class NetSymbol : public ValueSymbol {
public:
    const NetType& netType;

    NetSymbol(string_view name, SourceLocation loc, const NetType& netType) :
        ValueSymbol(SymbolKind::Net, name, loc), netType(netType) {}

    void toJson(json&) const {}

    static void fromSyntax(Compilation& compilation, const NetDeclarationSyntax& syntax,
                           SmallVector<const NetSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Net; }
};

} // namespace slang