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

    static bool isKind(SymbolKind kind) {
        switch (kind) {
            case SymbolKind::Variable:
            case SymbolKind::FormalArgument:
            case SymbolKind::Field:
            case SymbolKind::ClassProperty:
            case SymbolKind::Iterator:
            case SymbolKind::ClockVar:
            case SymbolKind::LocalAssertionVar:
                return true;
            default:
                return false;
        }
    }

protected:
    VariableSymbol(SymbolKind childKind, string_view name, SourceLocation loc,
                   VariableLifetime lifetime);
};

struct PortDeclarationSyntax;

/// Represents a formal argument in subroutine (task or function).
class FormalArgumentSymbol : public VariableSymbol {
public:
    ArgumentDirection direction = ArgumentDirection::In;

    FormalArgumentSymbol(string_view name, SourceLocation loc, ArgumentDirection direction,
                         VariableLifetime lifetime);

    bool mergeVariable(const VariableSymbol& variable);
    const VariableSymbol* getMergedVariable() const { return mergedVar; }

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(const Scope& scope, const PortDeclarationSyntax& syntax,
                           SmallVector<const FormalArgumentSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::FormalArgument; }

private:
    const VariableSymbol* mergedVar = nullptr;
};

/// Represents a field member of a struct or union.
class FieldSymbol : public VariableSymbol {
public:
    /// The offset of the field within its parent structure or union. If the parent type is
    /// packed, this is an offset in bits. Otherwise it's an index into the list of fields.
    uint32_t offset;

    /// If this field was marked with random qualifier, the mode indicated by that qualifier.
    RandMode randMode = RandMode::None;

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

    /// If the net has an initializer, checks it for correctness and issues a
    /// diagnostic if there are problems. Currently this only checks that the
    /// net isn't within a package, as initializers are disallowed there.
    void checkInitializer() const;

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(const Scope& scope, const NetDeclarationSyntax& syntax,
                           SmallVector<const NetSymbol*>& results);

    static void fromSyntax(const BindContext& context,
                           const UserDefinedNetDeclarationSyntax& syntax,
                           SmallVector<const NetSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Net; }

private:
    mutable optional<const TimingControl*> delay;
};

/// Represents an iterator variable created for array manipulation methods.
class IteratorSymbol : public VariableSymbol {
public:
    /// For efficiency purposes, each iterator symbol can form a linked list
    /// so that when binding nested iteration expressions we don't need to
    /// manage memory separately for list nodes. This member is otherwise
    /// not useful to other consumers.
    const IteratorSymbol* nextIterator = nullptr;

    /// The type of the array that this iterator traverses.
    const Type& arrayType;

    IteratorSymbol(const Scope& scope, string_view name, SourceLocation loc, const Type& arrayType);
    IteratorSymbol(string_view name, SourceLocation loc, const Type& arrayType,
                   const Type& indexType);

    void serializeTo(ASTSerializer&) const {};

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Iterator; }
};

struct ClockingItemSyntax;

/// Represents a clocking block signal.
class ClockVarSymbol : public VariableSymbol {
public:
    ArgumentDirection direction;
    ClockingSkew inputSkew;
    ClockingSkew outputSkew;

    ClockVarSymbol(string_view name, SourceLocation loc, ArgumentDirection direction,
                   ClockingSkew inputSkew, ClockingSkew outputSkew);

    static void fromSyntax(const Scope& scope, const ClockingItemSyntax& syntax,
                           SmallVector<const ClockVarSymbol*>& results);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ClockVar; }
};

struct LocalVariableDeclarationSyntax;

/// Represents a local variable declared inside an assertion item,
/// such as a sequence or property.
class LocalAssertionVarSymbol : public VariableSymbol {
public:
    LocalAssertionVarSymbol(string_view name, SourceLocation loc);

    static void fromSyntax(const Scope& scope, const LocalVariableDeclarationSyntax& syntax,
                           SmallVector<const LocalAssertionVarSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::LocalAssertionVar; }
};

} // namespace slang
