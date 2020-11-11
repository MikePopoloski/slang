//------------------------------------------------------------------------------
//! @file MemberSymbols.h
//! @brief Contains member-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Statements.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/Symbol.h"
#include "slang/util/Enum.h"

namespace slang {

class FormalArgumentSymbol;
class PackageSymbol;

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

    const PackageSymbol* getPackage() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::WildcardImport; }

private:
    mutable optional<const PackageSymbol*> package;
};

enum class MethodFlags : uint8_t {
    None = 0,
    Virtual = 1,
    Pure = 2,
    Static = 4,
    Constructor = 8,
    InterfaceImport = 16
};
BITMASK(MethodFlags, InterfaceImport);

class MethodPrototypeSymbol;
struct ClassMethodDeclarationSyntax;
struct FunctionDeclarationSyntax;
struct FunctionPortListSyntax;

/// Represents a subroutine (task or function).
class SubroutineSymbol : public Symbol, public Scope {
public:
    using ArgList = span<const FormalArgumentSymbol* const>;

    DeclaredType declaredReturnType;
    ArgList arguments;
    VariableLifetime defaultLifetime;
    SubroutineKind subroutineKind;
    Visibility visibility = Visibility::Public;
    bitmask<MethodFlags> flags = MethodFlags::None;
    SymbolIndex outOfBlockIndex{ 0 };

    const VariableSymbol* returnValVar = nullptr;
    const VariableSymbol* thisVar = nullptr;

    SubroutineSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                     VariableLifetime defaultLifetime, SubroutineKind subroutineKind) :
        Symbol(SymbolKind::Subroutine, name, loc),
        Scope(compilation, this), declaredReturnType(*this), defaultLifetime(defaultLifetime),
        subroutineKind(subroutineKind) {}

    const Statement& getBody(EvalContext* evalContext = nullptr) const;
    const Type& getReturnType() const { return declaredReturnType.getType(); }

    void setOverride(const SubroutineSymbol& parentMethod) const;
    const SubroutineSymbol* getOverride() const { return overrides; }

    void serializeTo(ASTSerializer& serializer) const;

    static SubroutineSymbol* fromSyntax(Compilation& compilation,
                                        const FunctionDeclarationSyntax& syntax,
                                        const Scope& parent, bool outOfBlock);

    static SubroutineSymbol* fromSyntax(Compilation& compilation,
                                        const ClassMethodDeclarationSyntax& syntax,
                                        const Scope& parent);

    static SubroutineSymbol& createOutOfBlock(Compilation& compilation,
                                              const FunctionDeclarationSyntax& syntax,
                                              const MethodPrototypeSymbol& prototype,
                                              const Scope& newParent, const Scope& definitionScope,
                                              SymbolIndex outOfBlockIndex);

    static SubroutineSymbol& createFromPrototype(Compilation& compilation,
                                                 const MethodPrototypeSymbol& prototype,
                                                 const Scope& parent);

    static void buildArguments(Scope& scope, const FunctionPortListSyntax& syntax,
                               VariableLifetime defaultLifetime,
                               SmallVector<const FormalArgumentSymbol*>& arguments);

    static void checkVirtualMethodMatch(const Scope& scope, const SubroutineSymbol& parentMethod,
                                        const SubroutineSymbol& derivedMethod,
                                        bool allowDerivedReturn);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Subroutine; }

    template<typename TVisitor>
    void visitStmts(TVisitor&& visitor) const {
        getBody().visit(visitor);
    }

private:
    void addThisVar(const Type& type);

    StatementBinder binder;
    mutable const SubroutineSymbol* overrides = nullptr;
};

struct ClassMethodPrototypeSyntax;
struct ModportNamedPortSyntax;
struct ModportSubroutinePortSyntax;

class MethodPrototypeSymbol : public Symbol, public Scope {
public:
    DeclaredType declaredReturnType;
    span<const FormalArgumentSymbol* const> arguments;
    SubroutineKind subroutineKind;
    Visibility visibility;
    bitmask<MethodFlags> flags;

    MethodPrototypeSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                          SubroutineKind subroutineKind, Visibility visibility,
                          bitmask<MethodFlags> flags);

    const Type& getReturnType() const { return declaredReturnType.getType(); }
    const SubroutineSymbol* getSubroutine() const;

    void setOverrides(const MethodPrototypeSymbol& overrideTarget) const {
        overrides = &overrideTarget;
    }
    const MethodPrototypeSymbol* getOverrides() const { return overrides; }

    bool checkMethodMatch(const Scope& scope, const SubroutineSymbol& method) const;

    void serializeTo(ASTSerializer& serializer) const;

    static MethodPrototypeSymbol& fromSyntax(const Scope& scope,
                                             const ClassMethodPrototypeSyntax& syntax);
    static MethodPrototypeSymbol& fromSyntax(const Scope& scope,
                                             const ModportSubroutinePortSyntax& syntax);
    static MethodPrototypeSymbol& fromSyntax(const Scope& scope, LookupLocation lookupLocation,
                                             const ModportNamedPortSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::MethodPrototype; }

private:
    mutable optional<const SubroutineSymbol*> subroutine;
    mutable const MethodPrototypeSymbol* overrides = nullptr;
};

/// Represents a single port specifier in a modport declaration.
class ModportPortSymbol : public ValueSymbol {
public:
    /// The direction of data flowing across the port.
    PortDirection direction = PortDirection::InOut;

    /// An instance-internal symbol that this port connects to, if any.
    /// Ports that do not connect directly to an internal symbol will have
    /// this set to nullptr.
    const Symbol* internalSymbol = nullptr;

    ModportPortSymbol(string_view name, SourceLocation loc, PortDirection direction);

    void serializeTo(ASTSerializer& serializer) const;

    static ModportPortSymbol& fromSyntax(const Scope& parent, LookupLocation lookupLocation,
                                         PortDirection direction,
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

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(Compilation& compilation, const ContinuousAssignSyntax& syntax,
                           const Scope& scope, LookupLocation location,
                           SmallVector<const Symbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ContinuousAssign; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        getAssignment().visit(visitor);
    }

private:
    mutable const Expression* assign = nullptr;
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

struct GateInstantiationSyntax;

class GateSymbol : public Symbol {
public:
    GateType gateType;

    GateSymbol(string_view name, SourceLocation loc, GateType gateType) :
        Symbol(SymbolKind::Gate, name, loc), gateType(gateType) {}

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(Compilation& compilation, const GateInstantiationSyntax& syntax,
                           LookupLocation location, const Scope& scope,
                           SmallVector<const Symbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Gate; }
};

class GateArraySymbol : public Symbol, public Scope {
public:
    span<const Symbol* const> elements;
    ConstantRange range;

    GateArraySymbol(Compilation& compilation, string_view name, SourceLocation loc,
                    span<const Symbol* const> elements, ConstantRange range) :
        Symbol(SymbolKind::GateArray, name, loc),
        Scope(compilation, this), elements(elements), range(range) {}

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::GateArray; }
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

} // namespace slang
