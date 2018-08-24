//------------------------------------------------------------------------------
// HierarchySymbols.h
// Contains hierarchy-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/ConstantValue.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/StatementBodiedScope.h"
#include "slang/symbols/Symbol.h"

namespace slang {

class Expression;

/// The root of a single compilation unit.
class CompilationUnitSymbol : public Symbol, public Scope {
public:
    explicit CompilationUnitSymbol(Compilation& compilation) :
        Symbol(SymbolKind::CompilationUnit, "", SourceLocation()),
        Scope(compilation, this) {}

    CompilationUnitSymbol(const CompilationUnitSymbol& other) :
        Symbol(other), Scope(other, this) {}

    void toJson(json&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CompilationUnit; }
};

/// A SystemVerilog package construct.
class PackageSymbol : public Symbol, public Scope {
public:
    PackageSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(SymbolKind::Package, name, loc),
        Scope(compilation, this) {}

    PackageSymbol(const PackageSymbol& other) :
        Symbol(other), Scope(other, this) {}

    void toJson(json&) const {}

    static PackageSymbol& fromSyntax(Compilation& compilation, const ModuleDeclarationSyntax& syntax);
    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Package; }
};

/// Represents a definition (module, interface, or program) that can be instantiated
/// to form a node in the design hierarchy.
class DefinitionSymbol : public Symbol, public Scope {
public:
    /// Tracks info about each parameter declaration for later evaluation.
    struct ParameterDecl {
        /// The name of the parameter.
        string_view name;

        /// The syntax describing the parameter's data type. This is evaluated lazily
        /// into a real type since it may require doing inference from the value.
        const DataTypeSyntax* type = nullptr;

        /// The default initializer, or null if the parameter has no default.
        const ExpressionSyntax* initializer = nullptr;

        /// The source location of the parameter.
        SourceLocation location;

        /// Indicates whether the parameter is a localparam (not overridable).
        bool isLocal;

        /// Indicates whether the parameter was declared in the header (parameter port list) or
        /// within the body of the definition itself.
        bool isPort;
    };

    DefinitionSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                     span<const ParameterDecl> parameters) :
        Symbol(SymbolKind::Definition, name, loc),
        Scope(compilation, this),
        parameters(parameters) {}

    DefinitionSymbol(const DefinitionSymbol& other) :
        Symbol(other), Scope(other, this) {}

    span<const ParameterDecl> parameters;

    void toJson(json&) const {}

    static DefinitionSymbol& fromSyntax(Compilation& compilation, const ModuleDeclarationSyntax& syntax);
    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Definition; }
};

/// Base class for module, interface, and program instance symbols.
class InstanceSymbol : public Symbol, public Scope {
public:
    static void fromSyntax(Compilation& compilation, const HierarchyInstantiationSyntax& syntax,
                           LookupLocation location, const Scope& scope, SmallVector<const Symbol*>& results);

    static bool isKind(SymbolKind kind);

    struct ParameterMetadata {
        const DefinitionSymbol::ParameterDecl* decl;
        const Type* type;
        ConstantValue value;
    };

    /// Defines information about a single port exposed by the instance.
    struct Port {
        /// The externally visible name of the port, if it has one.
        string_view name;

        /// The kind of port.
        PortKind kind = PortKind::Net;

        /// The direction of data flowing across the port. Some port kinds
        /// don't have meaningful semantics for direction; in those cases, this
        /// is set to NotApplicable.
        PortDirection direction = PortDirection::NotApplicable;

        /// The type of the port, if it has one. Otherwise nullptr.
        const Type* type = nullptr;

        /// An instance-internal symbol that this port connects to, if any.
        /// Ports that do not connect directly to an internal symbol will have
        /// this set to nullptr.
        const Symbol* symbol = nullptr;

        /// For explicit ports, this is the expression that controls how it
        /// connects to the instance's internals.
        const Expression* explicitConnection = nullptr;

        /// The default value of the port, if any. Otherwise nullptr.
        const ConstantValue* defaultValue = nullptr;
    };

    /// The set of ports exposed by the instance.
    span<const Port> ports;

protected:
    InstanceSymbol(SymbolKind kind, Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(kind, name, loc),
        Scope(compilation, this) {}

    // TODO: copy ports
    InstanceSymbol(const InstanceSymbol& other) :
        Symbol(other), Scope(other, this) {}

    struct PortListBuilder {
        Compilation& compilation;

        PortKind lastKind;
        PortDirection lastDirection;
        const Type* lastType;

        SmallVectorSized<Port, 8> ports;

        explicit PortListBuilder(Compilation& compilation);

        void add(const Port& port);
    };

    void populate(const DefinitionSymbol& definition, span<const ParameterMetadata> parameters);
    void handleAnsiPorts(const AnsiPortListSyntax& syntax);
    void handleImplicitAnsiPort(const ImplicitAnsiPortSyntax& syntax, PortListBuilder& builder);
    void handleNonAnsiPorts(const NonAnsiPortListSyntax& syntax);
};

class ModuleInstanceSymbol : public InstanceSymbol {
public:
    ModuleInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        InstanceSymbol(SymbolKind::ModuleInstance, compilation, name, loc) {}

    void toJson(json&) const {}

    static ModuleInstanceSymbol& instantiate(Compilation& compilation, string_view name, SourceLocation loc,
                                             const DefinitionSymbol& definition);

    static ModuleInstanceSymbol& instantiate(Compilation& compilation, string_view name, SourceLocation loc,
                                             const DefinitionSymbol& definition,
                                             span<const ParameterMetadata> parameters);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ModuleInstance; }
};

class InterfaceInstanceSymbol : public InstanceSymbol {
public:
    InterfaceInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        InstanceSymbol(SymbolKind::InterfaceInstance, compilation, name, loc) {}

    void toJson(json&) const {}

    static InterfaceInstanceSymbol& instantiate(Compilation& compilation, string_view name, SourceLocation loc,
                                                const DefinitionSymbol& definition,
                                                span<const ParameterMetadata> parameters);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InterfaceInstance; }
};

class SequentialBlockSymbol : public Symbol, public StatementBodiedScope {
public:
    SequentialBlockSymbol(Compilation& compilation, SourceLocation loc) :
        Symbol(SymbolKind::SequentialBlock, "", loc),
        StatementBodiedScope(compilation, this) {}

    SequentialBlockSymbol(const SequentialBlockSymbol& other) :
        Symbol(other), StatementBodiedScope(other, this) {}

    void toJson(json&) const {}

    static SequentialBlockSymbol& fromSyntax(Compilation& compilation, const BlockStatementSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::SequentialBlock; }
};

class ProceduralBlockSymbol : public Symbol, public StatementBodiedScope {
public:
    ProceduralBlockKind procedureKind;

    ProceduralBlockSymbol(Compilation& compilation, SourceLocation loc, ProceduralBlockKind procedureKind) :
        Symbol(SymbolKind::ProceduralBlock, "", loc),
        StatementBodiedScope(compilation, this),
        procedureKind(procedureKind) {}

    ProceduralBlockSymbol(const ProceduralBlockSymbol& other) :
        Symbol(other), StatementBodiedScope(other, this),
        procedureKind(procedureKind) {}

    void toJson(json& j) const;

    static ProceduralBlockSymbol& fromSyntax(Compilation& compilation, const ProceduralBlockSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ProceduralBlock; }
};

/// Represents blocks that are instantiated by a loop generate or conditional
/// generate construct.
class GenerateBlockSymbol : public Symbol, public Scope {
public:
    GenerateBlockSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(SymbolKind::GenerateBlock, name, loc),
        Scope(compilation, this) {}

    GenerateBlockSymbol(const GenerateBlockSymbol& other) :
        Symbol(other), Scope(other, this) {}

    void toJson(json&) const {}

    /// Creates a generate block from the given if-generate syntax node. Note that
    /// this can return null if the condition is false and there is no else block.
    static GenerateBlockSymbol* fromSyntax(Compilation& compilation, const IfGenerateSyntax& syntax,
                                           LookupLocation location, const Scope& parent);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::GenerateBlock; }
};

/// Represents an array of generate blocks, as generated by a loop generate construct.
class GenerateBlockArraySymbol : public Symbol, public Scope {
public:
    GenerateBlockArraySymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(SymbolKind::GenerateBlockArray, name, loc),
        Scope(compilation, this) {}

    GenerateBlockArraySymbol(const GenerateBlockArraySymbol& other) :
        Symbol(other), Scope(other, this) {}

    void toJson(json&) const {}

    /// Creates a generate block array from the given loop-generate syntax node.
    static GenerateBlockArraySymbol& fromSyntax(Compilation& compilation,
                                                const LoopGenerateSyntax& syntax,
                                                LookupLocation location, const Scope& parent);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::GenerateBlockArray; }
};

/// Represents the entirety of a design, along with all contained compilation units.
class RootSymbol : public Symbol, public Scope {
public:
    span<const ModuleInstanceSymbol* const> topInstances;
    span<const CompilationUnitSymbol* const> compilationUnits;

    explicit RootSymbol(Compilation& compilation) :
        Symbol(SymbolKind::Root, "$root", SourceLocation()), Scope(compilation, this) {}

    // TODO: remove members
    RootSymbol(const RootSymbol& other) :
        Symbol(other), Scope(other, this) {}

    void toJson(json&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Root; }
};

}
