//------------------------------------------------------------------------------
// InstanceSymbols.cpp
// Contains instance-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/InstanceSymbols.h"

#include "ParameterBuilder.h"

#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/compilation/Definition.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/ParameterSymbols.h"
#include "slang/symbols/PortSymbols.h"
#include "slang/symbols/Type.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/StackContainer.h"

namespace {

using namespace slang;

class InstanceBuilder {
public:
    InstanceBuilder(const BindContext& context, const InstanceCacheKey& cacheKeyBase,
                    span<const ParameterSymbolBase* const> parameters,
                    span<const AttributeInstanceSyntax* const> attributes, bool isUninstantiated) :
        compilation(context.getCompilation()),
        context(context), cacheKeyBase(cacheKeyBase), parameters(parameters),
        attributes(attributes), isUninstantiated(isUninstantiated) {}

    Symbol* create(const HierarchicalInstanceSyntax& syntax) {
        path.clear();

        auto dims = syntax.dimensions;
        return recurse(syntax, dims.begin(), dims.end());
    }

private:
    using DimIterator = span<VariableDimensionSyntax*>::iterator;

    Compilation& compilation;
    const BindContext& context;
    const InstanceCacheKey& cacheKeyBase;
    SmallVectorSized<int32_t, 4> path;
    span<const ParameterSymbolBase* const> parameters;
    span<const AttributeInstanceSyntax* const> attributes;
    bool isUninstantiated = false;

    Symbol* createInstance(const HierarchicalInstanceSyntax& syntax) {
        // Find all port connections to interface instances so we can
        // extract their cache keys.
        auto& def = cacheKeyBase.getDefinition();
        SmallVectorSized<std::pair<const InstanceCacheKey*, string_view>, 8> ifaceKeys;
        InterfacePortSymbol::findInterfaceInstanceKeys(context.scope, def, syntax.connections,
                                                       ifaceKeys);

        // Try to look up a cached instance using our own key to avoid redoing work.
        InstanceCacheKey cacheKey = cacheKeyBase;
        if (!ifaceKeys.empty())
            cacheKey.setInterfacePortKeys(ifaceKeys.copy(compilation));

        auto inst = compilation.emplace<InstanceSymbol>(compilation, syntax.name.valueText(),
                                                        syntax.name.location(), cacheKey,
                                                        parameters, isUninstantiated);

        inst->arrayPath = path.copy(compilation);
        inst->setSyntax(syntax);
        inst->setAttributes(context.scope, attributes);
        return inst;
    }

    Symbol* recurse(const HierarchicalInstanceSyntax& syntax, DimIterator it, DimIterator end) {
        if (it == end)
            return createInstance(syntax);

        // Evaluate the dimensions of the array. If this fails for some reason,
        // make up an empty array so that we don't get further errors when
        // things try to reference this symbol.
        auto nameToken = syntax.name;
        auto dim = context.evalDimension(**it, /* requireRange */ true, /* isPacked */ false);
        if (!dim.isRange()) {
            return compilation.emplace<InstanceArraySymbol>(
                compilation, nameToken.valueText(), nameToken.location(),
                span<const Symbol* const>{}, ConstantRange());
        }

        ++it;

        ConstantRange range = dim.range;
        SmallVectorSized<const Symbol*, 8> elements;
        for (int32_t i = range.lower(); i <= range.upper(); i++) {
            path.append(i);
            auto symbol = recurse(syntax, it, end);
            path.pop();

            symbol->name = "";
            elements.append(symbol);
        }

        auto result = compilation.emplace<InstanceArraySymbol>(compilation, nameToken.valueText(),
                                                               nameToken.location(),
                                                               elements.copy(compilation), range);
        for (auto element : elements)
            result->addMember(*element);

        return result;
    }
};

void createParams(Compilation& compilation, const Definition& definition,
                  ParameterBuilder& paramBuilder, LookupLocation ll, SourceLocation instanceLoc,
                  bool forceInvalidParams) {
    // Construct a temporary scope that has the right parent to house instance parameters
    // as we're evaluating them. We hold on to the initializer expressions and give them
    // to the instances later when we create them.
    struct TempInstance : public InstanceBodySymbol {
        TempInstance(Compilation& compilation, const Definition& definition,
                     bool forceInvalidParams) :
            InstanceBodySymbol(compilation, InstanceCacheKey(definition, {}, {}),
                               forceInvalidParams) {
            setParent(definition.scope);
        }
    };

    auto& tempDef = *compilation.emplace<TempInstance>(compilation, definition, forceInvalidParams);

    // Need the imports here as well, since parameters may depend on them.
    for (auto import : definition.syntax.header->imports)
        tempDef.addMembers(*import);

    paramBuilder.createParams(tempDef, ll, instanceLoc, forceInvalidParams,
                              /* suppressErrors */ false);
}

void createImplicitNets(const HierarchicalInstanceSyntax& instance, const BindContext& context,
                        const NetType& netType, SmallSet<string_view, 8>& implicitNetNames,
                        SmallVector<const Symbol*>& results) {
    // If no default nettype is set, we don't create implicit nets.
    if (netType.isError())
        return;

    for (auto conn : instance.connections) {
        const ExpressionSyntax* expr = nullptr;
        switch (conn->kind) {
            case SyntaxKind::OrderedPortConnection:
                expr = conn->as<OrderedPortConnectionSyntax>().expr;
                break;
            case SyntaxKind::NamedPortConnection:
                expr = conn->as<NamedPortConnectionSyntax>().expr;
                break;
            default:
                break;
        }

        if (!expr)
            continue;

        SmallVectorSized<Token, 8> implicitNets;
        Expression::findPotentiallyImplicitNets(*expr, context, implicitNets);

        for (Token t : implicitNets) {
            if (implicitNetNames.emplace(t.valueText()).second) {
                auto& comp = context.getCompilation();
                auto net = comp.emplace<NetSymbol>(t.valueText(), t.location(), netType);
                net->setType(comp.getLogicType());
                results.append(net);
            }
        }
    }
}

} // namespace

namespace slang {

InstanceSymbol::InstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                               const InstanceBodySymbol& body) :
    Symbol(SymbolKind::Instance, name, loc),
    body(body) {
    compilation.addInstance(*this);
}

InstanceSymbol::InstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                               const InstanceCacheKey& cacheKey,
                               span<const ParameterSymbolBase* const> parameters,
                               bool isUninstantiated) :
    InstanceSymbol(
        compilation, name, loc,
        InstanceBodySymbol::fromDefinition(compilation, cacheKey, parameters, isUninstantiated)) {
}

InstanceSymbol& InstanceSymbol::createDefault(
    Compilation& compilation, const Definition& definition,
    const flat_hash_map<string_view, const ConstantValue*>* paramOverrides) {
    return *compilation.emplace<InstanceSymbol>(
        compilation, definition.name, definition.location,
        InstanceBodySymbol::fromDefinition(compilation, definition,
                                           /* isUninstantiated */ false, paramOverrides));
}

InstanceSymbol& InstanceSymbol::createInvalid(Compilation& compilation,
                                              const Definition& definition) {
    // Give this instance an empty name so that it can't be referenced by name.
    return *compilation.emplace<InstanceSymbol>(
        compilation, "", SourceLocation::NoLocation,
        InstanceBodySymbol::fromDefinition(compilation, definition,
                                           /* isUninstantiated */ true, nullptr));
}

void InstanceSymbol::fromSyntax(Compilation& compilation,
                                const HierarchyInstantiationSyntax& syntax, LookupLocation location,
                                const Scope& scope, SmallVector<const Symbol*>& results) {
    auto definition = compilation.getDefinition(syntax.type.valueText(), scope);
    if (!definition) {
        scope.addDiag(diag::UnknownModule, syntax.type.range()) << syntax.type.valueText();
        return;
    }

    // Figure out whether this instance is being created within
    // an uninstantiated parent instance.
    auto currScope = &scope;
    while (currScope && currScope->asSymbol().kind != SymbolKind::InstanceBody)
        currScope = currScope->asSymbol().getParentScope();

    bool isUninstantiated = false;
    if (currScope)
        isUninstantiated = currScope->asSymbol().as<InstanceBodySymbol>().isUninstantiated;

    ParameterBuilder paramBuilder(scope, definition->name, definition->parameters);
    if (syntax.parameters)
        paramBuilder.setAssignments(*syntax.parameters);

    // Determine values for all parameters now so that they can be
    // shared between instances, and so that we can use them to create
    // a cache key to lookup any instance bodies that may already be
    // suitable for the new instances we're about to create.
    createParams(compilation, *definition, paramBuilder, location,
                 syntax.getFirstToken().location(), isUninstantiated);

    BindContext context(scope, location);
    InstanceCacheKey cacheKey(*definition, paramBuilder.paramValues.copy(compilation),
                              paramBuilder.typeParams.copy(compilation));

    InstanceBuilder builder(context, cacheKey, paramBuilder.paramSymbols, syntax.attributes,
                            isUninstantiated);

    // We have to check each port connection expression for any names that can't be resolved,
    // which represent implicit nets that need to be created now.
    SmallSet<string_view, 8> implicitNetNames;
    auto& netType = scope.getDefaultNetType();

    for (auto instanceSyntax : syntax.instances) {
        createImplicitNets(*instanceSyntax, context, netType, implicitNetNames, results);
        results.append(builder.create(*instanceSyntax));
    }
}

static void getInstanceArrayDimensions(const InstanceArraySymbol& array,
                                       SmallVector<ConstantRange>& dimensions) {
    auto scope = array.getParentScope();
    if (scope && scope->asSymbol().kind == SymbolKind::InstanceArray)
        getInstanceArrayDimensions(scope->asSymbol().as<InstanceArraySymbol>(), dimensions);

    dimensions.append(array.range);
}

const Definition& InstanceSymbol::getDefinition() const {
    return body.getDefinition();
}

bool InstanceSymbol::isModule() const {
    return getDefinition().definitionKind == DefinitionKind::Module;
}

bool InstanceSymbol::isInterface() const {
    return getDefinition().definitionKind == DefinitionKind::Interface;
}

const PortConnection* InstanceSymbol::getPortConnection(const PortSymbol& port) const {
    resolvePortConnections();

    auto it = connections->find(reinterpret_cast<uintptr_t>(&port));
    if (it == connections->end())
        return nullptr;

    return reinterpret_cast<const PortConnection*>(it->second);
}

const PortConnection* InstanceSymbol::getPortConnection(const InterfacePortSymbol& port) const {
    resolvePortConnections();

    auto it = connections->find(reinterpret_cast<uintptr_t>(&port));
    if (it == connections->end())
        return nullptr;

    return reinterpret_cast<const PortConnection*>(it->second);
}

void InstanceSymbol::resolvePortConnections() const {
    // Note: the order of operations here is very subtly important.
    // In order to resolve connections, we need to actually know our list of ports.
    // Asking the body for the list of ports requires fully elaborating the instance,
    // especially because of things like non-ansi port declarations which might be
    // deep in the body. That process of elaboration can actually depend back on the
    // port connections because of interface ports.
    // For example:
    //
    //     interface I #(parameter int i) (); endinterface
    //     module M(I iface, input logic [iface.i - 1 : 0] foo);
    //         localparam int j = $bits(foo);
    //     endmodule
    //
    // In order to resolve connections for an instance of M, we elaborate its body,
    // which then requires evaluating $bits(foo) which then depends on the connection
    // provided to `iface`. In the code, this translates to a reetrant call to this
    // function; the first time we call getPortList() on the body will call back in here.
    auto portList = body.getPortList();
    if (connections)
        return;

    auto scope = getParentScope();
    ASSERT(scope);

    connections = scope->getCompilation().allocPointerMap();

    auto syntax = getSyntax();
    if (!syntax)
        return;

    PortConnection::makeConnections(
        *this, portList, syntax->as<HierarchicalInstanceSyntax>().connections, *connections);
}

string_view InstanceSymbol::getArrayName() const {
    auto scope = getParentScope();
    if (scope && scope->asSymbol().kind == SymbolKind::InstanceArray)
        return scope->asSymbol().as<InstanceArraySymbol>().getArrayName();

    return name;
}

void InstanceSymbol::getArrayDimensions(SmallVector<ConstantRange>& dimensions) const {
    auto scope = getParentScope();
    if (scope && scope->asSymbol().kind == SymbolKind::InstanceArray)
        getInstanceArrayDimensions(scope->asSymbol().as<InstanceArraySymbol>(), dimensions);
}

void InstanceSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("body", body);
}

InstanceBodySymbol::InstanceBodySymbol(Compilation& compilation, const InstanceCacheKey& cacheKey,
                                       bool isUninstantiated) :
    Symbol(SymbolKind::InstanceBody, cacheKey.getDefinition().name,
           cacheKey.getDefinition().location),
    Scope(compilation, this), isUninstantiated(isUninstantiated), cacheKey(cacheKey) {
    setParent(cacheKey.getDefinition().scope, cacheKey.getDefinition().indexInScope);
}

const InstanceBodySymbol& InstanceBodySymbol::fromDefinition(
    Compilation& compilation, const Definition& definition, bool isUninstantiated,
    const flat_hash_map<string_view, const ConstantValue*>* paramOverrides) {

    ParameterBuilder paramBuilder(definition.scope, definition.name, definition.parameters);

    if (paramOverrides)
        paramBuilder.setGlobalOverrides(*paramOverrides);

    createParams(compilation, definition, paramBuilder, LookupLocation::max, definition.location,
                 isUninstantiated);

    return fromDefinition(compilation, InstanceCacheKey(definition, {}, {}),
                          paramBuilder.paramSymbols, isUninstantiated);
}

const InstanceBodySymbol& InstanceBodySymbol::fromDefinition(
    Compilation& comp, const InstanceCacheKey& cacheKey,
    span<const ParameterSymbolBase* const> parameters, bool isUninstantiated) {

    // If there's already a cached body for this key, return that instead of creating a new one.
    if (auto cached = comp.getInstanceCache().find(cacheKey))
        return *cached;

    auto& declSyntax = cacheKey.getDefinition().syntax;
    auto result = comp.emplace<InstanceBodySymbol>(comp, cacheKey, isUninstantiated);
    result->setSyntax(declSyntax);

    // Package imports from the header always come first.
    for (auto import : declSyntax.header->imports)
        result->addMembers(*import);

    // Now add in all parameter ports.
    auto paramIt = parameters.begin();
    while (paramIt != parameters.end()) {
        auto original = *paramIt;
        if (!original->isPortParam())
            break;

        if (original->symbol.kind == SymbolKind::Parameter)
            result->addMember(original->symbol.as<ParameterSymbol>().clone(comp));
        else
            result->addMember(original->symbol.as<TypeParameterSymbol>().clone(comp));

        paramIt++;
    }

    if (declSyntax.header->ports)
        result->addMembers(*declSyntax.header->ports);

    // Finally add members from the body.
    for (auto member : declSyntax.members) {
        // If this is a parameter declaration, we should already have metadata for it in our
        // parameters list. The list is given in declaration order, so we should be be able to move
        // through them incrementally.
        if (member->kind != SyntaxKind::ParameterDeclarationStatement) {
            result->addMembers(*member);
        }
        else {
            auto paramBase = member->as<ParameterDeclarationStatementSyntax>().parameter;
            if (paramBase->kind == SyntaxKind::ParameterDeclaration) {
                for (auto declarator : paramBase->as<ParameterDeclarationSyntax>().declarators) {
                    ASSERT(paramIt != parameters.end());

                    auto& symbol = (*paramIt)->symbol;
                    ASSERT(declarator->name.valueText() == symbol.name);

                    result->addMember(symbol.as<ParameterSymbol>().clone(comp));
                    paramIt++;
                }
            }
            else {
                for (auto declarator :
                     paramBase->as<TypeParameterDeclarationSyntax>().declarators) {
                    ASSERT(paramIt != parameters.end());

                    auto& symbol = (*paramIt)->symbol;
                    ASSERT(declarator->name.valueText() == symbol.name);

                    result->addMember(symbol.as<TypeParameterSymbol>().clone(comp));
                    paramIt++;
                }
            }
        }
    }

    comp.getInstanceCache().insert(*result);
    return *result;
}

const Symbol* InstanceBodySymbol::findPort(string_view portName) const {
    for (auto port : getPortList()) {
        if (port->name == portName)
            return port;
    }
    return nullptr;
}

void InstanceBodySymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("definition", cacheKey.getDefinition().name);
}

string_view InstanceArraySymbol::getArrayName() const {
    auto scope = getParentScope();
    if (scope && scope->asSymbol().kind == SymbolKind::InstanceArray)
        return scope->asSymbol().as<InstanceArraySymbol>().getArrayName();

    return name;
}

void InstanceArraySymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("range", range.toString());
}

} // namespace slang
