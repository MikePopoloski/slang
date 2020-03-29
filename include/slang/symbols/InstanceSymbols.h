//------------------------------------------------------------------------------
//! @file InstanceSymbols.h
//! @brief Contains instance-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/ConstantValue.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/Symbol.h"

namespace slang {

class Definition;
class ParameterSymbolBase;

struct HierarchicalInstanceSyntax;
struct HierarchyInstantiationSyntax;

/// Base class for module, interface, and program instance symbols.
class InstanceSymbol : public Symbol, public Scope {
public:
    const Definition& definition;
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
                   const Definition& definition, uint32_t hierarchyDepth);

    void populate(const HierarchicalInstanceSyntax* syntax,
                  span<const ParameterSymbolBase* const> parameters);

private:
    SymbolMap* portMap;
};

class ModuleInstanceSymbol : public InstanceSymbol {
public:
    ModuleInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                         const Definition& definition, uint32_t hierarchyDepth) :
        InstanceSymbol(SymbolKind::ModuleInstance, compilation, name, loc, definition,
                       hierarchyDepth) {}

    static ModuleInstanceSymbol& instantiate(Compilation& compilation, string_view name,
                                             SourceLocation loc, const Definition& definition);

    static ModuleInstanceSymbol& instantiate(Compilation& compilation,
                                             const HierarchicalInstanceSyntax& syntax,
                                             const Definition& definition,
                                             span<const ParameterSymbolBase* const> parameters,
                                             uint32_t hierarchyDepth);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ModuleInstance; }
};

class ProgramInstanceSymbol : public InstanceSymbol {
public:
    ProgramInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                          const Definition& definition, uint32_t hierarchyDepth) :
        InstanceSymbol(SymbolKind::ProgramInstance, compilation, name, loc, definition,
                       hierarchyDepth) {}

    static ProgramInstanceSymbol& instantiate(Compilation& compilation,
                                              const HierarchicalInstanceSyntax& syntax,
                                              const Definition& definition,
                                              span<const ParameterSymbolBase* const> parameters,
                                              uint32_t hierarchyDepth);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ProgramInstance; }
};

class InterfaceInstanceSymbol : public InstanceSymbol {
public:
    InterfaceInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                            const Definition& definition, uint32_t hierarchyDepth) :
        InstanceSymbol(SymbolKind::InterfaceInstance, compilation, name, loc, definition,
                       hierarchyDepth) {}

    static InterfaceInstanceSymbol& instantiate(Compilation& compilation,
                                                const HierarchicalInstanceSyntax& syntax,
                                                const Definition& definition,
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
