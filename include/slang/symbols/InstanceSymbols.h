//------------------------------------------------------------------------------
//! @file InstanceSymbols.h
//! @brief Contains instance-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/compilation/InstanceCache.h"
#include "slang/numeric/ConstantValue.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/Symbol.h"

namespace slang {

class Definition;
class InstanceBodySymbol;
class InterfacePortSymbol;
class ParameterSymbolBase;
class PortConnection;
class PortSymbol;

struct HierarchicalInstanceSyntax;
struct HierarchyInstantiationSyntax;

/// Base class for module, interface, and program instance symbols.
class InstanceSymbol : public Symbol {
public:
    const InstanceBodySymbol& body;
    span<const int32_t> arrayPath;

    InstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                   const InstanceBodySymbol& body);

    InstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                   const InstanceCacheKey& cacheKey,
                   span<const ParameterSymbolBase* const> parameters);

    const Definition& getDefinition() const;
    bool isModule() const;
    bool isInterface() const;

    const PortConnection* getPortConnection(const PortSymbol& port) const;
    const PortConnection* getPortConnection(const InterfacePortSymbol& port) const;
    void resolvePortConnections() const;

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

    /// Creates a default-instantiated instance of the given definition. All parameters must
    /// have defaults specified.
    static InstanceSymbol& createDefault(
        Compilation& compilation, const Definition& definition,
        const flat_hash_map<string_view, const ConstantValue*>* paramOverrides = nullptr);

    /// Creates an intentionally invalid instance by forcing all parameters to null values.
    /// This allows type checking instance members as long as they don't depend on any parameters.
    static InstanceSymbol& createInvalid(Compilation& compilation, const Definition& definition);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Instance; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const; // implementation is in ASTVisitor.h

private:
    mutable PointerMap* connections = nullptr;
};

class InstanceBodySymbol : public Symbol, public Scope {
public:
    InstanceBodySymbol(Compilation& compilation, const InstanceCacheKey& cacheKey);

    span<const Symbol* const> getPortList() const {
        ensureElaborated();
        return portList;
    }

    const Symbol* findPort(string_view name) const;

    const Definition& getDefinition() const { return cacheKey.getDefinition(); }
    const InstanceCacheKey& getCacheKey() const { return cacheKey; }

    static const InstanceBodySymbol& fromDefinition(
        Compilation& compilation, const Definition& definition, bool forceInvalidParams,
        const flat_hash_map<string_view, const ConstantValue*>* paramOverrides);

    static const InstanceBodySymbol& fromDefinition(
        Compilation& compilation, const InstanceCacheKey& cacheKey,
        span<const ParameterSymbolBase* const> parameters);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InstanceBody; }

private:
    friend class Scope;

    void setPorts(span<const Symbol* const> ports) const { portList = ports; }

    InstanceCacheKey cacheKey;
    mutable span<const Symbol* const> portList;
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
