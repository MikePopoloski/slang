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
class ParameterSymbol;

/// The root of a single compilation unit.
class CompilationUnitSymbol : public Symbol, public Scope {
public:
    explicit CompilationUnitSymbol(Compilation& compilation) :
        Symbol(SymbolKind::CompilationUnit, "", SourceLocation()),
        Scope(compilation, this) {}

    void toJson(json&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CompilationUnit; }
};

/// A SystemVerilog package construct.
class PackageSymbol : public Symbol, public Scope {
public:
    PackageSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(SymbolKind::Package, name, loc),
        Scope(compilation, this) {}

    void toJson(json&) const {}

    static PackageSymbol& fromSyntax(Compilation& compilation, const ModuleDeclarationSyntax& syntax);
    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Package; }
};

/// Represents a definition (module, interface, or program) that can be instantiated
/// to form a node in the design hierarchy.
class DefinitionSymbol : public Symbol, public Scope {
public:
    span<const ParameterSymbol* const> parameters;

    DefinitionSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(SymbolKind::Definition, name, loc),
        Scope(compilation, this) {}

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

protected:
    InstanceSymbol(SymbolKind kind, Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(kind, name, loc),
        Scope(compilation, this) {}

    void populate(const DefinitionSymbol& definition, span<const Expression*> parameterOverrides);
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
                                             span<const Expression*> parameterOverrides);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ModuleInstance; }
};

class InterfaceInstanceSymbol : public InstanceSymbol {
public:
    InterfaceInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        InstanceSymbol(SymbolKind::InterfaceInstance, compilation, name, loc) {}

    void toJson(json&) const {}

    static InterfaceInstanceSymbol& instantiate(Compilation& compilation, string_view name, SourceLocation loc,
                                                const DefinitionSymbol& definition,
                                                span<const Expression*> parameterOverrides);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InterfaceInstance; }
};

class SequentialBlockSymbol : public Symbol, public StatementBodiedScope {
public:
    SequentialBlockSymbol(Compilation& compilation, SourceLocation loc) :
        Symbol(SymbolKind::SequentialBlock, "", loc),
        StatementBodiedScope(compilation, this) {}

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

    void toJson(json&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Root; }
};

}
