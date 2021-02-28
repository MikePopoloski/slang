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
class Expression;
class InstanceBodySymbol;
class InterfacePortSymbol;
class ParameterSymbolBase;
class PortConnection;
class PortSymbol;

struct BindDirectiveSyntax;
struct HierarchicalInstanceSyntax;
struct HierarchyInstantiationSyntax;
struct ParamOverrideNode;

/// Base class for module, interface, and program instance symbols.
class InstanceSymbol : public Symbol {
public:
    const InstanceBodySymbol& body;
    span<const int32_t> arrayPath;

    InstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                   const InstanceBodySymbol& body);

    InstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                   const InstanceCacheKey& cacheKey, const ParamOverrideNode* paramOverrideNode,
                   span<const ParameterSymbolBase* const> parameters, bool isUninstantiated);

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

    /// Creates one or more instances and binds them into a target scoped, based on the
    /// provided syntax directive.
    static void fromBindDirective(const Scope& scope, const BindDirectiveSyntax& syntax);

    /// Creates a default-instantiated instance of the given definition. All parameters must
    /// have defaults specified.
    static InstanceSymbol& createDefault(Compilation& compilation, const Definition& definition,
                                         const ParamOverrideNode* paramOverrideNode);

    /// Creates an intentionally invalid instance by forcing all parameters to null values.
    /// This allows type checking instance members as long as they don't depend on any parameters.
    static InstanceSymbol& createInvalid(Compilation& compilation, const Definition& definition);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Instance; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const; // implementation is in ASTVisitor.h

private:
    mutable PointerMap* connections = nullptr;
};

struct ParameterValueAssignmentSyntax;

class InstanceBodySymbol : public Symbol, public Scope {
public:
    /// A pointer into the parameter override tree, if this instance or any
    /// child instances have parameter overrides that need to be applied.
    const ParamOverrideNode* paramOverrideNode;

    /// A copy of all port parameter symbols used to construct the instance body.
    span<const ParameterSymbolBase* const> parameters;

    /// Indicates whether the module isn't actually instantiated in the design.
    /// This might be because it was created with invalid parameters simply to
    /// check name lookup rules but it's never actually referenced elsewhere
    /// in the user's code.
    bool isUninstantiated = false;

    InstanceBodySymbol(Compilation& compilation, const InstanceCacheKey& cacheKey,
                       const ParamOverrideNode* paramOverrideNode,
                       span<const ParameterSymbolBase* const> parameters, bool isUninstantiated);

    span<const Symbol* const> getPortList() const {
        ensureElaborated();
        return portList;
    }

    const Symbol* findPort(string_view name) const;

    const Definition& getDefinition() const { return cacheKey.getDefinition(); }
    const InstanceCacheKey& getCacheKey() const { return cacheKey; }

    static const InstanceBodySymbol& fromDefinition(Compilation& compilation,
                                                    const Definition& definition,
                                                    bool isUninstantiated,
                                                    const ParamOverrideNode* paramOverrideNode);

    static const InstanceBodySymbol* fromDefinition(
        const Scope& scope, LookupLocation lookupLocation, SourceLocation sourceLoc,
        const Definition& definition, const ParameterValueAssignmentSyntax* parameterSyntax);

    static const InstanceBodySymbol& fromDefinition(
        Compilation& compilation, const InstanceCacheKey& cacheKey,
        const ParamOverrideNode* paramOverrideNode,
        span<const ParameterSymbolBase* const> parameters, bool isUninstantiated,
        bool forceUncached = false);

    const InstanceBodySymbol& cloneUncached() const;

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

/// Represents an instance of some unknown module (or interface / program).
/// This is a placeholder in the AST so that we don't record further errors
/// after the initial one about the unknown module itself.
class UnknownModuleSymbol : public Symbol {
public:
    /// The self-determined expressions that are assigned to the parameters
    /// in the instantiation. These aren't necessarily correctly typed
    /// since we can't know the destination type of each parameter.
    span<const Expression* const> paramExpressions;

    UnknownModuleSymbol(string_view name, SourceLocation loc,
                        span<const Expression* const> params) :
        Symbol(SymbolKind::UnknownModule, name, loc),
        paramExpressions(params) {}

    /// Gets the self-determined expressions that are assigned to the ports
    /// in the instantiation. These aren't necessarily correctly typed
    /// since we can't know the destination type of each port.
    span<const Expression* const> getPortConnections() const;

    static void fromSyntax(Compilation& compilation, const HierarchyInstantiationSyntax& syntax,
                           LookupLocation location, const Scope& scope,
                           SmallVector<const Symbol*>& results);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::UnknownModule; }

private:
    mutable optional<span<const Expression* const>> ports;
};

} // namespace slang
