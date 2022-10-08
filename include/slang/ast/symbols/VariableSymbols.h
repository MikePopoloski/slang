//------------------------------------------------------------------------------
//! @file VariableSymbols.h
//! @brief Contains variable-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/SemanticFacts.h"
#include "slang/ast/symbols/ValueSymbol.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

class NetType;
class TimingControl;

/// Specifies various flags that can apply to variables.
enum class SLANG_EXPORT VariableFlags : uint16_t {
    /// No specific flags specified.
    None = 0,

    /// The variable is a constant, i.e. not modifiable after initialization.
    Const = 1 << 0,

    /// The variable was not declared by the user but created during compilation.
    CompilerGenerated = 1 << 1,

    /// The variable is a coverage option that is not modifiable outside of
    /// the covergroup declaration.
    ImmutableCoverageOption = 1 << 2,

    /// The variable is a formal argument of an overridden sample method in a covergroup.
    CoverageSampleFormal = 1 << 3
};
BITMASK(VariableFlags, CoverageSampleFormal)

/// Represents a variable declaration.
class SLANG_EXPORT VariableSymbol : public ValueSymbol {
public:
    VariableLifetime lifetime;
    bitmask<VariableFlags> flags;

    VariableSymbol(string_view name, SourceLocation loc, VariableLifetime lifetime);

    void serializeTo(ASTSerializer& serializer) const;

    /// Constructs all variable symbols specified by the given syntax node. Note that
    /// this might actually construct net symbols if the data type syntax refers to
    /// a user defined net type or alias.
    static void fromSyntax(Compilation& compilation, const syntax::DataDeclarationSyntax& syntax,
                           const Scope& scope, SmallVectorBase<const ValueSymbol*>& results);

    static VariableSymbol& fromSyntax(Compilation& compilation,
                                      const syntax::ForVariableDeclarationSyntax& syntax,
                                      const VariableSymbol* lastVar);

    static bool isKind(SymbolKind kind) {
        switch (kind) {
            case SymbolKind::Variable:
            case SymbolKind::FormalArgument:
            case SymbolKind::Field:
            case SymbolKind::ClassProperty:
            case SymbolKind::Iterator:
            case SymbolKind::PatternVar:
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

/// Represents a formal argument in subroutine (task or function).
class SLANG_EXPORT FormalArgumentSymbol : public VariableSymbol {
public:
    ArgumentDirection direction = ArgumentDirection::In;

    FormalArgumentSymbol(string_view name, SourceLocation loc, ArgumentDirection direction,
                         VariableLifetime lifetime);

    bool mergeVariable(const VariableSymbol& variable);
    const VariableSymbol* getMergedVariable() const { return mergedVar; }

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(const Scope& scope, const syntax::PortDeclarationSyntax& syntax,
                           SmallVectorBase<const FormalArgumentSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::FormalArgument; }

private:
    const VariableSymbol* mergedVar = nullptr;
};

/// Represents a field member of a struct or union.
class SLANG_EXPORT FieldSymbol : public VariableSymbol {
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

/// Represents a net declaration.
class SLANG_EXPORT NetSymbol : public ValueSymbol {
public:
    const NetType& netType;
    enum ExpansionHint { None, Vectored, Scalared } expansionHint = None;

    NetSymbol(string_view name, SourceLocation loc, const NetType& netType);

    const TimingControl* getDelay() const;

    /// If the net has an initializer, checks it for correctness and issues a
    /// diagnostic if there are problems. Currently this only checks that the
    /// net isn't within a package, as initializers are disallowed there.
    void checkInitializer() const;

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(const Scope& scope, const syntax::NetDeclarationSyntax& syntax,
                           SmallVectorBase<const NetSymbol*>& results);

    static void fromSyntax(const Scope& scope,
                           const syntax::UserDefinedNetDeclarationSyntax& syntax,
                           const Symbol* netTypeSym, SmallVectorBase<const NetSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Net; }

private:
    mutable std::optional<const TimingControl*> delay;
};

/// Represents a temporary variable materialized within a limited scope
/// such as a single expression. Used for things like iterators used in
/// array manipulation methods and for pattern identifiers.
class SLANG_EXPORT TempVarSymbol : public VariableSymbol {
public:
    /// For efficiency purposes, each temp var symbol can form a linked list so
    /// that when creating nested expressions we don't need to manage memory separately
    /// for list nodes. This member is otherwise not useful to other consumers.
    const TempVarSymbol* nextTemp = nullptr;

    using VariableSymbol::setParent;

    static bool isKind(SymbolKind kind) {
        switch (kind) {
            case SymbolKind::Iterator:
                return true;
            default:
                return false;
        }
    }

protected:
    TempVarSymbol(SymbolKind childKind, string_view name, SourceLocation loc,
                  VariableLifetime lifetime) :
        VariableSymbol(childKind, name, loc, lifetime) {}
};

/// Represents an iterator variable created for array manipulation methods.
class SLANG_EXPORT IteratorSymbol : public TempVarSymbol {
public:
    /// The type of the array that this iterator traverses.
    const Type& arrayType;

    IteratorSymbol(const Scope& scope, string_view name, SourceLocation loc, const Type& arrayType);
    IteratorSymbol(string_view name, SourceLocation loc, const Type& arrayType,
                   const Type& indexType);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Iterator; }
};

/// Represents a pattern variable materialized for a pattern matching expression.
class SLANG_EXPORT PatternVarSymbol : public TempVarSymbol {
public:
    PatternVarSymbol(string_view name, SourceLocation loc, const Type& type);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PatternVar; }
};

/// Represents a clocking block signal.
class SLANG_EXPORT ClockVarSymbol : public VariableSymbol {
public:
    ArgumentDirection direction;
    ClockingSkew inputSkew;
    ClockingSkew outputSkew;

    ClockVarSymbol(string_view name, SourceLocation loc, ArgumentDirection direction,
                   ClockingSkew inputSkew, ClockingSkew outputSkew);

    static void fromSyntax(const Scope& scope, const syntax::ClockingItemSyntax& syntax,
                           SmallVectorBase<const ClockVarSymbol*>& results);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ClockVar; }
};

/// Represents a local variable declared inside an assertion item,
/// such as a sequence or property.
class SLANG_EXPORT LocalAssertionVarSymbol : public VariableSymbol {
public:
    LocalAssertionVarSymbol(string_view name, SourceLocation loc);

    static void fromSyntax(const Scope& scope, const syntax::LocalVariableDeclarationSyntax& syntax,
                           SmallVectorBase<const LocalAssertionVarSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::LocalAssertionVar; }
};

} // namespace slang::ast
