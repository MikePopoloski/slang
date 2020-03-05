//------------------------------------------------------------------------------
//! @file DefinitionSymbols.h
//! @brief Contains definition-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/ConstantValue.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/Symbol.h"
#include "slang/symbols/TimeScaleSymbolBase.h"

namespace slang {

class ModportSymbol;
class NetType;
class ParameterSymbolBase;
class PortSymbol;

/// Represents a definition (module, interface, or program) that can be instantiated
/// to form a node in the design hierarchy.
class DefinitionSymbol : public Symbol, public Scope, TimeScaleSymbolBase {
public:
    span<const ParameterSymbolBase* const> parameters;
    const NetType& defaultNetType;
    DefinitionKind definitionKind;
    VariableLifetime defaultLifetime;
    UnconnectedDrive unconnectedDrive;

    DefinitionSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                     DefinitionKind definitionKind, VariableLifetime defaultLifetime,
                     const NetType& defaultNetType, UnconnectedDrive unconnectedDrive);

    const SymbolMap& getPortMap() const {
        ensureElaborated();
        return *portMap;
    }

    /// Looks for a modport in this definition and issues a diagnostic if not found.
    const ModportSymbol* getModportOrError(string_view modport, const Scope& scope,
                                           SourceRange range) const;

    TimeScale getTimeScale() const { return timeScale; }
    void serializeTo(ASTSerializer& serializer) const;

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
    uint32_t hierarchyDepth;

    const SymbolMap& getPortMap() const {
        ensureElaborated();
        return *portMap;
    }

    /// If this instance is part of an array, walk upward to find the array's name.
    /// Otherwise returns the name of the instance itself.
    string_view getArrayName() const;

    /// Gets the set of dimensions describing the instance array that contains this instance.
    /// If this instance is not part of an array, does not add any dimensions to the given list.
    void getArrayDimensions(SmallVector<ConstantRange>& dimensions) const;

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(Compilation& compilation, const HierarchyInstantiationSyntax& syntax,
                           LookupLocation location, const Scope& scope,
                           SmallVector<const Symbol*>& results);

    static bool isKind(SymbolKind kind);

protected:
    InstanceSymbol(SymbolKind kind, Compilation& compilation, string_view name, SourceLocation loc,
                   const DefinitionSymbol& definition, uint32_t hierarchyDepth);

    void populate(const HierarchicalInstanceSyntax* syntax,
                  span<const ParameterSymbolBase* const> parameters);

private:
    SymbolMap* portMap;
};

class ModuleInstanceSymbol : public InstanceSymbol {
public:
    ModuleInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                         const DefinitionSymbol& definition, uint32_t hierarchyDepth) :
        InstanceSymbol(SymbolKind::ModuleInstance, compilation, name, loc, definition,
                       hierarchyDepth) {}

    static ModuleInstanceSymbol& instantiate(Compilation& compilation, string_view name,
                                             SourceLocation loc,
                                             const DefinitionSymbol& definition);

    static ModuleInstanceSymbol& instantiate(Compilation& compilation,
                                             const HierarchicalInstanceSyntax& syntax,
                                             const DefinitionSymbol& definition,
                                             span<const ParameterSymbolBase* const> parameters,
                                             uint32_t hierarchyDepth);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ModuleInstance; }
};

class ProgramInstanceSymbol : public InstanceSymbol {
public:
    ProgramInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                          const DefinitionSymbol& definition, uint32_t hierarchyDepth) :
        InstanceSymbol(SymbolKind::ProgramInstance, compilation, name, loc, definition,
                       hierarchyDepth) {}

    static ProgramInstanceSymbol& instantiate(Compilation& compilation,
                                              const HierarchicalInstanceSyntax& syntax,
                                              const DefinitionSymbol& definition,
                                              span<const ParameterSymbolBase* const> parameters,
                                              uint32_t hierarchyDepth);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ProgramInstance; }
};

class InterfaceInstanceSymbol : public InstanceSymbol {
public:
    InterfaceInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                            const DefinitionSymbol& definition, uint32_t hierarchyDepth) :
        InstanceSymbol(SymbolKind::InterfaceInstance, compilation, name, loc, definition,
                       hierarchyDepth) {}

    static InterfaceInstanceSymbol& instantiate(Compilation& compilation,
                                                const HierarchicalInstanceSyntax& syntax,
                                                const DefinitionSymbol& definition,
                                                span<const ParameterSymbolBase* const> parameters,
                                                uint32_t hierarchyDepth);

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

    /// If this array is part of a multidimensional array, walk upward to find
    /// the root array's name. Otherwise returns the name of this symbol itself.
    string_view getArrayName() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InstanceArray; }
};

} // namespace slang
