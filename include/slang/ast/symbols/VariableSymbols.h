//------------------------------------------------------------------------------
//! @file VariableSymbols.h
//! @brief Contains variable-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Expression.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/ast/TimingControl.h"
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
    CoverageSampleFormal = 1 << 3,

    /// This is a checker "free variable", which may behave nondeterministically
    /// in simulation and participate differently in formal verification.
    CheckerFreeVariable = 1 << 4,

    /// The variable is a function port with direction 'ref static'.
    RefStatic = 1 << 5
};
SLANG_BITMASK(VariableFlags, RefStatic)

/// Represents a variable declaration.
class SLANG_EXPORT VariableSymbol : public ValueSymbol {
public:
    VariableLifetime lifetime;
    bitmask<VariableFlags> flags;

    VariableSymbol(std::string_view name, SourceLocation loc, VariableLifetime lifetime);

    void checkInitializer() const;

    void serializeTo(ASTSerializer& serializer) const;

    /// Constructs all variable symbols specified by the given syntax node. Note that
    /// this might actually construct net symbols if the data type syntax refers to
    /// a user defined net type or alias.
    static void fromSyntax(Compilation& compilation, const syntax::DataDeclarationSyntax& syntax,
                           const Scope& scope, bool isCheckerFreeVar,
                           SmallVectorBase<VariableSymbol*>& results);

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
    VariableSymbol(SymbolKind childKind, std::string_view name, SourceLocation loc,
                   VariableLifetime lifetime);
};

/// Represents a formal argument in subroutine (task or function).
class SLANG_EXPORT FormalArgumentSymbol : public VariableSymbol {
public:
    ArgumentDirection direction = ArgumentDirection::In;

    FormalArgumentSymbol(std::string_view name, SourceLocation loc, ArgumentDirection direction,
                         VariableLifetime lifetime);

    bool mergeVariable(const VariableSymbol& variable);
    const VariableSymbol* getMergedVariable() const { return mergedVar; }

    void setDefaultValueSyntax(const syntax::ExpressionSyntax& syntax) {
        defaultValSyntax = &syntax;
        defaultVal = nullptr;
    }

    void setDefaultValue(const Expression* expr) {
        defaultVal = expr;
        defaultValSyntax = nullptr;
    }

    const syntax::ExpressionSyntax* getDefaultValueSyntax() const { return defaultValSyntax; }
    const Expression* getDefaultValue() const;

    FormalArgumentSymbol& clone(Compilation& compilation) const;

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(const Scope& scope, const syntax::PortDeclarationSyntax& syntax,
                           SmallVectorBase<const FormalArgumentSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::FormalArgument; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        if (auto expr = getDefaultValue())
            expr->visit(visitor);
    }

private:
    const VariableSymbol* mergedVar = nullptr;
    const syntax::ExpressionSyntax* defaultValSyntax = nullptr;
    mutable const Expression* defaultVal = nullptr;
};

/// Represents a field member of a struct or union.
class SLANG_EXPORT FieldSymbol : public VariableSymbol {
public:
    /// The offset of the field within its parent structure or union, in bits.
    /// For unpacked types this offset is in "selectable bits" which is how overlapping
    /// drivers to a given field are expressed, but don't necessarily correspond to
    /// how many bits would be used if the entire type were serialized.
    uint64_t bitOffset;

    /// The index of the field within its parent structure.
    uint32_t fieldIndex;

    /// If this field was marked with random qualifier, the mode indicated by that qualifier.
    RandMode randMode = RandMode::None;

    FieldSymbol(std::string_view name, SourceLocation loc, uint64_t bitOffset,
                uint32_t fieldIndex) :
        VariableSymbol(SymbolKind::Field, name, loc, VariableLifetime::Automatic),
        bitOffset(bitOffset), fieldIndex(fieldIndex) {}

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Field; }
};

/// Represents a net declaration.
class SLANG_EXPORT NetSymbol : public ValueSymbol {
public:
    const NetType& netType;
    enum ExpansionHint { None, Vectored, Scalared } expansionHint = None;
    bool isImplicit = false;

    NetSymbol(std::string_view name, SourceLocation loc, const NetType& netType);

    const TimingControl* getDelay() const;
    std::optional<ChargeStrength> getChargeStrength() const;
    std::pair<std::optional<DriveStrength>, std::optional<DriveStrength>> getDriveStrength() const;

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

    static NetSymbol& createImplicit(Compilation& compilation,
                                     const syntax::IdentifierNameSyntax& syntax,
                                     const NetType& netType);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Net; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        if (auto d = getDelay())
            d->visit(visitor);
    }

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
    TempVarSymbol(SymbolKind childKind, std::string_view name, SourceLocation loc,
                  VariableLifetime lifetime) : VariableSymbol(childKind, name, loc, lifetime) {}
};

/// Represents an iterator variable created for array manipulation methods.
class SLANG_EXPORT IteratorSymbol : public TempVarSymbol {
public:
    /// The type of the array that this iterator traverses.
    const Type& arrayType;

    /// The name of the built-in "index" method, which can be customized
    /// by the user. Some uses of IteratorSymbol don't allow an index method
    /// and set this value to the empty string.
    std::string_view indexMethodName;

    IteratorSymbol(const Scope& scope, std::string_view name, SourceLocation loc,
                   const Type& arrayType, std::string_view indexMethodName);
    IteratorSymbol(std::string_view name, SourceLocation loc, const Type& arrayType,
                   const Type& indexType);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Iterator; }
};

/// Represents a pattern variable materialized for a pattern matching expression.
class SLANG_EXPORT PatternVarSymbol : public TempVarSymbol {
public:
    PatternVarSymbol(std::string_view name, SourceLocation loc, const Type& type);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PatternVar; }
};

/// Represents a clocking block signal.
class SLANG_EXPORT ClockVarSymbol : public VariableSymbol {
public:
    ArgumentDirection direction;
    ClockingSkew inputSkew;
    ClockingSkew outputSkew;

    ClockVarSymbol(std::string_view name, SourceLocation loc, ArgumentDirection direction,
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
    LocalAssertionVarSymbol(std::string_view name, SourceLocation loc);

    static void fromSyntax(const Scope& scope, const syntax::LocalVariableDeclarationSyntax& syntax,
                           SmallVectorBase<const LocalAssertionVarSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::LocalAssertionVar; }
};

} // namespace slang::ast
