//------------------------------------------------------------------------------
//! @file MemberSymbols.h
//! @brief Contains member-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/ValueSymbol.h"

namespace slang {

class AssertionExpr;
class PackageSymbol;
class TimingControl;

struct EmptyMemberSyntax;

/// Represents an empty member, i.e. a standalone semicolon.
/// This exists as a symbol mostly to provide a place to attach attributes.
class EmptyMemberSymbol : public Symbol {
public:
    explicit EmptyMemberSymbol(SourceLocation location) :
        Symbol(SymbolKind::EmptyMember, "", location) {}

    void serializeTo(ASTSerializer&) const {}

    static EmptyMemberSymbol& fromSyntax(Compilation& compilation, const Scope& scope,
                                         const EmptyMemberSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::EmptyMember; }
};

/// A class that wraps a hoisted transparent type member, such as an enum value
/// or a symbol inherited from a base class, into a scope. Whenever lookup finds
/// one of these symbols, it will be unwrapped into the underlying symbol instead.
class TransparentMemberSymbol : public Symbol {
public:
    const Symbol& wrapped;

    TransparentMemberSymbol(const Symbol& wrapped_) :
        Symbol(SymbolKind::TransparentMember, wrapped_.name, wrapped_.location), wrapped(wrapped_) {
    }

    // Wrapped symbols will be exposed in their containing scope.
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::TransparentMember; }
};

/// Represents an explicit import from a package.
class ExplicitImportSymbol : public Symbol {
public:
    string_view packageName;
    string_view importName;

    ExplicitImportSymbol(string_view packageName, string_view importName, SourceLocation location) :
        Symbol(SymbolKind::ExplicitImport, importName, location), packageName(packageName),
        importName(importName) {}

    const PackageSymbol* package() const;
    const Symbol* importedSymbol() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ExplicitImport; }

private:
    mutable const PackageSymbol* package_ = nullptr;
    mutable const Symbol* import = nullptr;
    mutable bool initialized = false;
};

/// Represents a wildcard import declaration. This symbol is special in
/// that it won't be returned by a lookup, and won't even be in the name
/// map of a symbol at all. Instead there is a sideband list used to
/// resolve names via wildcard.
class WildcardImportSymbol : public Symbol {
public:
    string_view packageName;

    WildcardImportSymbol(string_view packageName, SourceLocation location) :
        Symbol(SymbolKind::WildcardImport, "", location), packageName(packageName) {}

    void setPackage(const PackageSymbol& package);
    const PackageSymbol* getPackage() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::WildcardImport; }

private:
    mutable optional<const PackageSymbol*> package;
};

struct ModportNamedPortSyntax;

/// Represents a single port specifier in a modport declaration.
class ModportPortSymbol : public ValueSymbol {
public:
    /// The direction of data flowing across the port.
    ArgumentDirection direction = ArgumentDirection::InOut;

    /// An instance-internal symbol that this port connects to, if any.
    /// Ports that do not connect directly to an internal symbol will have
    /// this set to nullptr.
    const Symbol* internalSymbol = nullptr;

    ModportPortSymbol(string_view name, SourceLocation loc, ArgumentDirection direction);

    void serializeTo(ASTSerializer& serializer) const;

    static ModportPortSymbol& fromSyntax(const Scope& parent, LookupLocation lookupLocation,
                                         ArgumentDirection direction,
                                         const ModportNamedPortSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ModportPort; }
};

struct ModportDeclarationSyntax;

/// Represents a modport within an interface definition.
class ModportSymbol : public Symbol, public Scope {
public:
    ModportSymbol(Compilation& compilation, string_view name, SourceLocation loc);

    void serializeTo(ASTSerializer&) const {}

    static void fromSyntax(const Scope& parent, const ModportDeclarationSyntax& syntax,
                           LookupLocation lookupLocation,
                           SmallVector<const ModportSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Modport; }
};

struct ContinuousAssignSyntax;

/// Represents a continuous assignment statement.
class ContinuousAssignSymbol : public Symbol {
public:
    explicit ContinuousAssignSymbol(const ExpressionSyntax& syntax);
    ContinuousAssignSymbol(SourceLocation loc, const Expression& assignment);

    const Expression& getAssignment() const;
    const TimingControl* getDelay() const;

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(Compilation& compilation, const ContinuousAssignSyntax& syntax,
                           const Scope& scope, LookupLocation location,
                           SmallVector<const Symbol*>& results,
                           SmallVector<const Symbol*>& implicitNets);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ContinuousAssign; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        getAssignment().visit(visitor);
    }

private:
    mutable const Expression* assign = nullptr;
    mutable optional<const TimingControl*> delay;
};

struct GenvarDeclarationSyntax;

/// Represents a genvar declaration.
class GenvarSymbol : public Symbol {
public:
    GenvarSymbol(string_view name, SourceLocation loc);

    void serializeTo(ASTSerializer&) const {}

    static void fromSyntax(const Scope& parent, const GenvarDeclarationSyntax& syntax,
                           SmallVector<const GenvarSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Genvar; }
};

struct ElabSystemTaskSyntax;

/// Represents an elaboration system task, such as $error or $warning.
class ElabSystemTaskSymbol : public Symbol {
public:
    ElabSystemTaskKind taskKind;

    ElabSystemTaskSymbol(ElabSystemTaskKind taskKind, SourceLocation loc);

    string_view getMessage() const;
    void issueDiagnostic() const;

    void serializeTo(ASTSerializer& serializer) const;

    static ElabSystemTaskSymbol& fromSyntax(Compilation& compilation,
                                            const ElabSystemTaskSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ElabSystemTask; }

private:
    mutable optional<string_view> message;
};

class PrimitivePortSymbol : public ValueSymbol {
public:
    PrimitivePortDirection direction;

    PrimitivePortSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                        PrimitivePortDirection direction);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PrimitivePort; }
};

struct UdpDeclarationSyntax;

class PrimitiveSymbol : public Symbol, public Scope {
public:
    span<const PrimitivePortSymbol* const> ports;
    const ConstantValue* initVal = nullptr;
    bool isSequential = false;
    enum PrimitiveKind { UserDefined, Fixed, NInput, NOutput } primitiveKind;

    PrimitiveSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                    PrimitiveKind primitiveKind) :
        Symbol(SymbolKind::Primitive, name, loc),
        Scope(compilation, this), primitiveKind(primitiveKind) {}

    static PrimitiveSymbol& fromSyntax(const Scope& scope, const UdpDeclarationSyntax& syntax);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Primitive; }
};

struct SpecifyBlockSyntax;

class SpecifyBlockSymbol : public Symbol, public Scope {
public:
    SpecifyBlockSymbol(Compilation& compilation, SourceLocation loc);

    static SpecifyBlockSymbol& fromSyntax(Scope& scope, const SpecifyBlockSyntax& syntax);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::SpecifyBlock; }
};

struct AssertionItemPortListSyntax;
struct PropertyExprSyntax;

/// Represents a formal argument / port of an assertion construct, such
/// as a sequence, property, or let construct.
class AssertionPortSymbol : public Symbol {
public:
    DeclaredType declaredType;
    const PropertyExprSyntax* defaultValueSyntax = nullptr;

    AssertionPortSymbol(string_view name, SourceLocation loc);

    static void buildPorts(Scope& scope, const AssertionItemPortListSyntax& syntax,
                           SmallVector<const AssertionPortSymbol*>& results);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::AssertionPort; }
};

struct SequenceDeclarationSyntax;

/// Represents a named sequence object.
class SequenceSymbol : public Symbol, public Scope {
public:
    span<const AssertionPortSymbol* const> ports;

    SequenceSymbol(Compilation& compilation, string_view name, SourceLocation loc);

    static SequenceSymbol& fromSyntax(const Scope& scope, const SequenceDeclarationSyntax& syntax);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Sequence; }
};

struct PropertyDeclarationSyntax;

/// Represents a named property object.
class PropertySymbol : public Symbol, public Scope {
public:
    span<const AssertionPortSymbol* const> ports;

    PropertySymbol(Compilation& compilation, string_view name, SourceLocation loc);

    static PropertySymbol& fromSyntax(const Scope& scope, const PropertyDeclarationSyntax& syntax);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Property; }
};

struct ClockingDeclarationSyntax;
struct ClockingSkewSyntax;

/// Represents a clocking block.
class ClockingBlockSymbol : public Symbol, public Scope {
public:
    ClockingBlockSymbol(Compilation& compilation, string_view name, SourceLocation loc);

    const TimingControl& getEvent() const;
    ClockingSkew getDefaultInputSkew() const;
    ClockingSkew getDefaultOutputSkew() const;

    static ClockingBlockSymbol& fromSyntax(const Scope& scope,
                                           const ClockingDeclarationSyntax& syntax);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ClockingBlock; }

private:
    mutable const TimingControl* event = nullptr;
    mutable optional<ClockingSkew> defaultInputSkew;
    mutable optional<ClockingSkew> defaultOutputSkew;
    const ClockingSkewSyntax* inputSkewSyntax = nullptr;
    const ClockingSkewSyntax* outputSkewSyntax = nullptr;
};

} // namespace slang
