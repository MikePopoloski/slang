//------------------------------------------------------------------------------
// MemberSymbols.h
// Contains member-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <tuple>

#include "slang/binding/ConstantValue.h"
#include "slang/binding/Statements.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/Symbol.h"

namespace slang {

class DefinitionSymbol;
class InterfaceInstanceSymbol;
class ModportSymbol;
class PackageSymbol;

/// A class that wraps a hoisted transparent type member (such as an enum value)
/// into a parent scope. Whenever lookup finds one of these symbols, it will be
/// unwrapped into the underlying symbol instead.
class TransparentMemberSymbol : public Symbol {
public:
    const Symbol& wrapped;

    TransparentMemberSymbol(const Symbol& wrapped_) :
        Symbol(SymbolKind::TransparentMember, wrapped_.name, wrapped_.location), wrapped(wrapped_) {
    }

    // enum members will be exposed in their containing enum
    void toJson(json&) const {}

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

    void toJson(json& j) const;

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

    void toJson(json& j) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::WildcardImport; }

private:
    mutable optional<const PackageSymbol*> package;
};

/// Represents a parameter value.
class ParameterSymbol : public ValueSymbol {
public:
    ParameterSymbol(string_view name, SourceLocation loc, bool isLocal, bool isPort);

    static void fromSyntax(const Scope& scope, const ParameterDeclarationSyntax& syntax,
                           bool isLocal, bool isPort, SmallVector<ParameterSymbol*>& results);
    static void fromSyntax(const Scope& scope, const ParameterDeclarationStatementSyntax& syntax,
                           SmallVector<ParameterSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Parameter; }

    ParameterSymbol& createOverride(Compilation& compilation,
                                    const Expression* newInitializer) const;

    const ConstantValue& getValue() const;
    void setValue(ConstantValue value);

    bool isLocalParam() const { return isLocal; }
    bool isPortParam() const { return isPort; }
    bool isBodyParam() const { return !isPortParam(); }

    void toJson(json& j) const;

private:
    const ConstantValue* overriden = nullptr;
    bool isLocal = false;
    bool isPort = false;
};

/// Represents the public-facing side of a module / program / interface port.
/// The port symbol itself is not directly referenceable from within the instance;
/// it can however connect directly to a symbol that is.
class PortSymbol : public ValueSymbol {
public:
    /// The direction of data flowing across the port.
    PortDirection direction = PortDirection::InOut;

    /// An instance-internal symbol that this port connects to, if any.
    /// Ports that do not connect directly to an internal symbol will have
    /// this set to nullptr.
    const Symbol* internalSymbol = nullptr;

    /// An optional default value that is used for the port when no connection is provided.
    const Expression* defaultValue = nullptr;

    PortSymbol(string_view name, SourceLocation loc,
               bitmask<DeclaredTypeFlags> flags = DeclaredTypeFlags::None);

    /// If the port is connected during instantiation, gets the expression that
    /// indicates how it connects to the outside world. Otherwise returns nullptr.
    const Expression* getConnection() const;

    void setConnection(const Expression* expr);
    void setConnection(const ExpressionSyntax& syntax);

    void toJson(json& j) const;

    static void fromSyntax(const PortListSyntax& syntax, const Scope& scope,
                           SmallVector<Symbol*>& results,
                           span<const PortDeclarationSyntax* const> portDeclarations);

    static void makeConnections(const Scope& scope, span<Symbol* const> ports,
                                const SeparatedSyntaxList<PortConnectionSyntax>& portConnections);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Port; }

private:
    mutable optional<const Expression*> conn;
    const ExpressionSyntax* connSyntax = nullptr;
};

/// Represents the public-facing side of a module / program / interface port
/// that is also a connection to an interface instance (optionally with a modport restriction).
class InterfacePortSymbol : public Symbol {
public:
    /// A pointer to the definition for the interface.
    const DefinitionSymbol* interfaceDef = nullptr;

    /// A pointer to an optional modport that restricts which interface signals are accessible.
    const ModportSymbol* modport = nullptr;

    /// If the port is connected during instantiation, this is the external instance to which it
    /// connects.
    const Symbol* connection = nullptr;

    /// Gets the set of dimensions for specifying interface arrays, if applicable.
    span<const ConstantRange> getDeclaredRange() const;

    InterfacePortSymbol(string_view name, SourceLocation loc) :
        Symbol(SymbolKind::InterfacePort, name, loc) {}

    void toJson(json& j) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InterfacePort; }

private:
    mutable optional<span<const ConstantRange>> range;
};

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
                                      const ForVariableDeclarationSyntax& syntax);

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

/// Represents a subroutine (task or function).
class SubroutineSymbol : public Symbol, public Scope {
public:
    using ArgList = span<const FormalArgumentSymbol* const>;

    DeclaredType declaredReturnType;
    const VariableSymbol* returnValVar = nullptr;
    ArgList arguments;
    VariableLifetime defaultLifetime = VariableLifetime::Automatic;
    SubroutineKind subroutineKind;

    SubroutineSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                     VariableLifetime defaultLifetime, SubroutineKind subroutineKind,
                     const Scope&) :
        Symbol(SymbolKind::Subroutine, name, loc),
        Scope(compilation, this), declaredReturnType(*this), defaultLifetime(defaultLifetime),
        subroutineKind(subroutineKind) {}

    const Statement& getBody() const { return binder.getStatement(*this, LookupLocation::max); }
    const Type& getReturnType() const { return declaredReturnType.getType(); }

    void toJson(json& j) const;

    static SubroutineSymbol& fromSyntax(Compilation& compilation,
                                        const FunctionDeclarationSyntax& syntax,
                                        const Scope& parent);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Subroutine; }

private:
    StatementBinder binder;
};

/// Represents a modport within an interface definition.
class ModportSymbol : public Symbol, public Scope {
public:
    ModportSymbol(Compilation& compilation, string_view name, SourceLocation loc);

    void toJson(json&) const {}

    static void fromSyntax(Compilation& compilation, const ModportDeclarationSyntax& syntax,
                           SmallVector<const ModportSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Modport; }
};

/// Represents a continuous assignment statement.
class ContinuousAssignSymbol : public Symbol {
public:
    explicit ContinuousAssignSymbol(const ExpressionSyntax& syntax);
    ContinuousAssignSymbol(SourceLocation loc, const Expression& assignment);

    const Expression& getAssignment() const;

    void toJson(json& j) const;

    static void fromSyntax(Compilation& compilation, const ContinuousAssignSyntax& syntax,
                           SmallVector<const ContinuousAssignSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ContinuousAssign; }

private:
    mutable const Expression* assign = nullptr;
};

/// Represents a genvar declaration.
class GenvarSymbol : public Symbol {
public:
    GenvarSymbol(string_view name, SourceLocation loc);

    void toJson(json&) const {}

    static void fromSyntax(Compilation& compilation, const GenvarDeclarationSyntax& syntax,
                           SmallVector<const GenvarSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Genvar; }
};

} // namespace slang