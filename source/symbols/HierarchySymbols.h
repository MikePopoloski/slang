//------------------------------------------------------------------------------
// HierarchySymbols.h
// Contains hierarchy-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "binding/ConstantValue.h"
#include "symbols/Definition.h"
#include "symbols/SemanticFacts.h"
#include "symbols/StatementBodiedScope.h"
#include "symbols/Symbol.h"

namespace slang {

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

/// Base class for module, interface, and program instance symbols.
class InstanceSymbol : public Symbol, public Scope {
public:
    static void fromSyntax(Compilation& compilation, const HierarchyInstantiationSyntax& syntax,
                           LookupLocation location, const Scope& scope, SmallVector<const Symbol*>& results);

    static bool isKind(SymbolKind kind);

    struct ParameterMetadata {
        const Definition::ParameterDecl* decl;
        const Type* type;
        ConstantValue value;
    };

protected:
    InstanceSymbol(SymbolKind kind, Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(kind, name, loc),
        Scope(compilation, this) {}

    void populate(const Definition& definition, span<const ParameterMetadata> parameters);
};

class ModuleInstanceSymbol : public InstanceSymbol {
public:
    ModuleInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        InstanceSymbol(SymbolKind::ModuleInstance, compilation, name, loc) {}

    void toJson(json&) const {}

    static ModuleInstanceSymbol& instantiate(Compilation& compilation, string_view name, SourceLocation loc,
                                             const Definition& definition);

    static ModuleInstanceSymbol& instantiate(Compilation& compilation, string_view name, SourceLocation loc,
                                             const Definition& definition, span<const ParameterMetadata> parameters);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ModuleInstance; }
};

class InterfaceInstanceSymbol : public InstanceSymbol {
public:
    InterfaceInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        InstanceSymbol(SymbolKind::InterfaceInstance, compilation, name, loc) {}

    void toJson(json&) const {}

    static InterfaceInstanceSymbol& instantiate(Compilation& compilation, string_view name, SourceLocation loc,
                                                const Definition& definition, span<const ParameterMetadata> parameters);

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
    explicit GenerateBlockSymbol(Compilation& compilation) :
        Symbol(SymbolKind::GenerateBlock, "", SourceLocation()),
        Scope(compilation, this) {}

    GenerateBlockSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(SymbolKind::GenerateBlock, name, loc),
        Scope(compilation, this) {}

    void toJson(json&) const {}

    void elaborate(const IfGenerateSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::GenerateBlock; }
};

/// Represents an array of generate blocks, as generated by a loop generate construct.
class GenerateBlockArraySymbol : public Symbol, public Scope {
public:
    explicit GenerateBlockArraySymbol(Compilation& compilation) :
        Symbol(SymbolKind::GenerateBlockArray, "", SourceLocation()),
        Scope(compilation, this) {}

    void toJson(json&) const {}

    void elaborate(const LoopGenerateSyntax& syntax);

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
