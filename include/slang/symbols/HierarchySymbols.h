//------------------------------------------------------------------------------
// HierarchySymbols.h
// Contains hierarchy-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/ConstantValue.h"
#include "slang/binding/Statements.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/Symbol.h"

namespace slang {

class Expression;
class ModportSymbol;
class NetType;
class ParameterSymbolBase;
class PortSymbol;

struct ModuleDeclarationSyntax;
struct TimeUnitsDeclarationSyntax;

/// A helper base class for symbols that have an associated time scale.
class TimeScaleSymbolBase {
protected:
    void setTimeScale(const Scope& scope, const TimeUnitsDeclarationSyntax& syntax, bool isFirst);
    void finalizeTimeScale(const Scope& parentScope, const ModuleDeclarationSyntax& syntax);

    TimeScale timeScale;
    optional<SourceRange> unitsRange;
    optional<SourceRange> precisionRange;
};

/// The root of a single compilation unit.
class CompilationUnitSymbol : public Symbol, public Scope, TimeScaleSymbolBase {
public:
    explicit CompilationUnitSymbol(Compilation& compilation);

    void addMembers(const SyntaxNode& syntax);

    TimeScale getTimeScale() const { return timeScale; }
    void toJson(json&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CompilationUnit; }

private:
    // Used for tracking whether a time scale directive is first in scope.
    bool anyMembers = false;
};

/// A SystemVerilog package construct.
class PackageSymbol : public Symbol, public Scope, TimeScaleSymbolBase {
public:
    const NetType& defaultNetType;

    PackageSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                  const NetType& defaultNetType);

    TimeScale getTimeScale() const { return timeScale; }
    void toJson(json&) const {}

    static PackageSymbol& fromSyntax(Compilation& compilation,
                                     const ModuleDeclarationSyntax& syntax, const Scope& scope);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Package; }
};

/// Represents a definition (module, interface, or program) that can be instantiated
/// to form a node in the design hierarchy.
class DefinitionSymbol : public Symbol, public Scope, TimeScaleSymbolBase {
public:
    span<const ParameterSymbolBase* const> parameters;
    DefinitionKind definitionKind;
    const NetType& defaultNetType;

    DefinitionSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                     DefinitionKind definitionKind, const NetType& defaultNetType);

    const SymbolMap& getPortMap() const {
        ensureElaborated();
        return *portMap;
    }

    /// Looks for a modport in this definition and issues a diagnostic if not found.
    const ModportSymbol* getModportOrError(string_view modport, const Scope& scope,
                                           SourceRange range) const;

    TimeScale getTimeScale() const { return timeScale; }
    void toJson(json& j) const;

    static DefinitionSymbol& fromSyntax(Compilation& compilation,
                                        const ModuleDeclarationSyntax& syntax, const Scope& scope);
    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Definition; }

private:
    SymbolMap* portMap;
};

struct HierarchicalInstanceSyntax;
struct HierarchyInstantiationSyntax;

/// Base class for module, interface, and program instance symbols.
class InstanceSymbol : public Symbol, public Scope {
public:
    const DefinitionSymbol& definition;
    span<const int32_t> arrayPath;

    const SymbolMap& getPortMap() const {
        ensureElaborated();
        return *portMap;
    }

    void toJson(json& j) const;

    static void fromSyntax(Compilation& compilation, const HierarchyInstantiationSyntax& syntax,
                           LookupLocation location, const Scope& scope,
                           SmallVector<const Symbol*>& results);

    static bool isKind(SymbolKind kind);

protected:
    InstanceSymbol(SymbolKind kind, Compilation& compilation, string_view name, SourceLocation loc,
                   const DefinitionSymbol& definition);

    void populate(const HierarchicalInstanceSyntax* syntax,
                  span<const ParameterSymbolBase* const> parameters);

private:
    SymbolMap* portMap;
};

class ModuleInstanceSymbol : public InstanceSymbol {
public:
    ModuleInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                         const DefinitionSymbol& definition) :
        InstanceSymbol(SymbolKind::ModuleInstance, compilation, name, loc, definition) {}

    static ModuleInstanceSymbol& instantiate(Compilation& compilation, string_view name,
                                             SourceLocation loc,
                                             const DefinitionSymbol& definition);

    static ModuleInstanceSymbol& instantiate(Compilation& compilation,
                                             const HierarchicalInstanceSyntax& syntax,
                                             const DefinitionSymbol& definition,
                                             span<const ParameterSymbolBase* const> parameters);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ModuleInstance; }
};

class InterfaceInstanceSymbol : public InstanceSymbol {
public:
    InterfaceInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                            const DefinitionSymbol& definition) :
        InstanceSymbol(SymbolKind::InterfaceInstance, compilation, name, loc, definition) {}

    static InterfaceInstanceSymbol& instantiate(Compilation& compilation,
                                                const HierarchicalInstanceSyntax& syntax,
                                                const DefinitionSymbol& definition,
                                                span<const ParameterSymbolBase* const> parameters);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InterfaceInstance; }
};

class InstanceArraySymbol : public Symbol, public Scope {
public:
    span<const Symbol* const> elements;
    ConstantRange range;

    InstanceArraySymbol(Compilation& compilation, string_view name, SourceLocation loc,
                        span<const Symbol* const> elements, ConstantRange range) :
        Symbol(SymbolKind::InstanceArray, name, loc),
        Scope(compilation, this), elements(elements), range(range) {}

    void toJson(json& j) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InstanceArray; }
};

class StatementBlockSymbol : public Symbol, public Scope {
public:
    StatementBlockSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(SymbolKind::StatementBlock, name, loc), Scope(compilation, this) {}

    void setTemporaryParent(const Scope& scope, SymbolIndex index) { setParent(scope, index); }
    const Statement& getBody() const;

    void toJson(json&) const {}

    static StatementBlockSymbol& fromSyntax(Compilation& compilation,
                                            const BlockStatementSyntax& syntax);
    static StatementBlockSymbol& fromSyntax(Compilation& compilation,
                                            const ForLoopStatementSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::StatementBlock; }

private:
    StatementBinder binder;
};

struct ProceduralBlockSyntax;

class ProceduralBlockSymbol : public Symbol {
public:
    ProceduralBlockKind procedureKind;

    ProceduralBlockSymbol(SourceLocation loc, ProceduralBlockKind procedureKind) :
        Symbol(SymbolKind::ProceduralBlock, "", loc), procedureKind(procedureKind) {}

    const Statement& getBody() const;
    void toJson(json& j) const;

    static ProceduralBlockSymbol& fromSyntax(
        const Scope& scope, const ProceduralBlockSyntax& syntax,
        span<const StatementBlockSymbol* const>& additionalBlocks);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ProceduralBlock; }

private:
    StatementBinder binder;
};

struct CaseGenerateSyntax;
struct IfGenerateSyntax;

/// Represents blocks that are instantiated by a loop generate or conditional
/// generate construct.
class GenerateBlockSymbol : public Symbol, public Scope {
public:
    uint32_t constructIndex = 0;
    bool isInstantiated = false;

    GenerateBlockSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                        uint32_t constructIndex, bool isInstantiated) :
        Symbol(SymbolKind::GenerateBlock, name, loc),
        Scope(compilation, this), constructIndex(constructIndex), isInstantiated(isInstantiated) {}

    void toJson(json& j) const;

    static void fromSyntax(Compilation& compilation, const IfGenerateSyntax& syntax,
                           LookupLocation location, const Scope& parent, uint32_t constructIndex,
                           bool isInstantiated, SmallVector<GenerateBlockSymbol*>& results);

    static void fromSyntax(Compilation& compilation, const CaseGenerateSyntax& syntax,
                           LookupLocation location, const Scope& parent, uint32_t constructIndex,
                           bool isInstantiated, SmallVector<GenerateBlockSymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::GenerateBlock; }
};

struct LoopGenerateSyntax;

/// Represents an array of generate blocks, as generated by a loop generate construct.
class GenerateBlockArraySymbol : public Symbol, public Scope {
public:
    struct ArrayEntry {
        not_null<const SVInt*> index;
        not_null<const GenerateBlockSymbol*> block;
    };

    span<const ArrayEntry> entries;
    uint32_t constructIndex = 0;

    GenerateBlockArraySymbol(Compilation& compilation, string_view name, SourceLocation loc,
                             uint32_t constructIndex) :
        Symbol(SymbolKind::GenerateBlockArray, name, loc),
        Scope(compilation, this), constructIndex(constructIndex) {}

    void toJson(json& j) const;

    /// Creates a generate block array from the given loop-generate syntax node.
    static GenerateBlockArraySymbol& fromSyntax(Compilation& compilation,
                                                const LoopGenerateSyntax& syntax,
                                                SymbolIndex scopeIndex, LookupLocation location,
                                                const Scope& parent, uint32_t constructIndex);

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

} // namespace slang
