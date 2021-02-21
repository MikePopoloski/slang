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
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/NetType.h"
#include "slang/types/Type.h"
#include "slang/util/StackContainer.h"

namespace {

using namespace slang;

class InstanceBuilder {
public:
    InstanceBuilder(const BindContext& context, const InstanceCacheKey& cacheKeyBase,
                    const ParamOverrideNode* paramOverrideNode,
                    span<const ParameterSymbolBase* const> parameters,
                    span<const AttributeInstanceSyntax* const> attributes, bool isUninstantiated) :
        compilation(context.getCompilation()),
        context(context), cacheKeyBase(cacheKeyBase), parameters(parameters),
        attributes(attributes), paramOverrideNode(paramOverrideNode),
        isUninstantiated(isUninstantiated) {}

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
    const ParamOverrideNode* paramOverrideNode;
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

        auto inst = compilation.emplace<InstanceSymbol>(
            compilation, syntax.name.valueText(), syntax.name.location(), cacheKey,
            paramOverrideNode, parameters, isUninstantiated);

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

bool createParams(Compilation& compilation, const Definition& definition,
                  ParameterBuilder& paramBuilder, LookupLocation ll, SourceLocation instanceLoc,
                  bool forceInvalidParams) {
    // Construct a temporary scope that has the right parent to house instance parameters
    // as we're evaluating them. We hold on to the initializer expressions and give them
    // to the instances later when we create them.
    struct TempInstance : public InstanceBodySymbol {
        TempInstance(Compilation& compilation, const Definition& definition,
                     bool forceInvalidParams) :
            InstanceBodySymbol(compilation, InstanceCacheKey(definition, {}, {}), nullptr, {},
                               forceInvalidParams) {
            setParent(definition.scope);
        }
    };

    auto& tempDef = *compilation.emplace<TempInstance>(compilation, definition, forceInvalidParams);

    // Need the imports here as well, since parameters may depend on them.
    for (auto import : definition.syntax.header->imports)
        tempDef.addMembers(*import);

    return paramBuilder.createParams(tempDef, ll, instanceLoc, forceInvalidParams,
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
                               const ParamOverrideNode* paramOverrideNode,
                               span<const ParameterSymbolBase* const> parameters,
                               bool isUninstantiated) :
    InstanceSymbol(compilation, name, loc,
                   InstanceBodySymbol::fromDefinition(compilation, cacheKey, paramOverrideNode,
                                                      parameters, isUninstantiated)) {
}

InstanceSymbol& InstanceSymbol::createDefault(Compilation& compilation,
                                              const Definition& definition,
                                              const ParamOverrideNode* paramOverrideNode) {
    return *compilation.emplace<InstanceSymbol>(
        compilation, definition.name, definition.location,
        InstanceBodySymbol::fromDefinition(compilation, definition,
                                           /* isUninstantiated */ false, paramOverrideNode));
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
    // Figure out whether this instance is being created within
    // an uninstantiated parent instance.
    auto currScope = &scope;
    while (currScope && currScope->asSymbol().kind != SymbolKind::InstanceBody)
        currScope = currScope->asSymbol().getParentScope();

    const ParamOverrideNode* parentOverrideNode = nullptr;
    bool isUninstantiated = false;
    if (currScope) {
        auto& instanceBody = currScope->asSymbol().as<InstanceBodySymbol>();
        parentOverrideNode = instanceBody.paramOverrideNode;
        isUninstantiated = instanceBody.isUninstantiated;
    }

    auto definition = compilation.getDefinition(syntax.type.valueText(), scope);
    if (!definition) {
        if (!isUninstantiated)
            scope.addDiag(diag::UnknownModule, syntax.type.range()) << syntax.type.valueText();

        UnknownModuleSymbol::fromSyntax(compilation, syntax, location, scope, results);
        return;
    }

    // We have to check each port connection expression for any names that can't be resolved,
    // which represent implicit nets that need to be created now.
    BindContext context(scope, location);
    SmallSet<string_view, 8> implicitNetNames;
    auto& netType = scope.getDefaultNetType();

    // The common case is that our parent doesn't have a parameter override node,
    // which lets us evaluate all parameter assignments for this instance in a batch.
    if (!parentOverrideNode) {
        ParameterBuilder paramBuilder(scope, definition->name, definition->parameters);
        if (syntax.parameters)
            paramBuilder.setAssignments(*syntax.parameters);

        // Determine values for all parameters now so that they can be
        // shared between instances, and so that we can use them to create
        // a cache key to lookup any instance bodies that may already be
        // suitable for the new instances we're about to create.
        createParams(compilation, *definition, paramBuilder, location,
                     syntax.getFirstToken().location(), isUninstantiated);

        InstanceCacheKey cacheKey(*definition, paramBuilder.paramValues.copy(compilation),
                                  paramBuilder.typeParams.copy(compilation));

        InstanceBuilder builder(context, cacheKey, nullptr, paramBuilder.paramSymbols,
                                syntax.attributes, isUninstantiated);

        for (auto instanceSyntax : syntax.instances) {
            createImplicitNets(*instanceSyntax, context, netType, implicitNetNames, results);
            results.append(builder.create(*instanceSyntax));
        }
    }
    else {
        // Otherwise we need to evaluate parameters separately for each child.
        for (auto instanceSyntax : syntax.instances) {
            const ParamOverrideNode* overrideNode = nullptr;
            auto instName = instanceSyntax->name.valueText();
            if (!instName.empty()) {
                if (auto it = parentOverrideNode->childNodes.find(std::string(instName));
                    it != parentOverrideNode->childNodes.end()) {
                    overrideNode = &it->second;
                }
            }

            ParameterBuilder paramBuilder(scope, definition->name, definition->parameters);
            if (syntax.parameters)
                paramBuilder.setAssignments(*syntax.parameters);
            if (overrideNode)
                paramBuilder.setOverrides(overrideNode->overrides);

            // Determine values for all parameters now so that they can be
            // shared between instances, and so that we can use them to create
            // a cache key to lookup any instance bodies that may already be
            // suitable for the new instances we're about to create.
            createParams(compilation, *definition, paramBuilder, location,
                         syntax.getFirstToken().location(), isUninstantiated);

            InstanceCacheKey cacheKey(*definition, paramBuilder.paramValues.copy(compilation),
                                      paramBuilder.typeParams.copy(compilation));

            InstanceBuilder builder(context, cacheKey, overrideNode, paramBuilder.paramSymbols,
                                    syntax.attributes, isUninstantiated);

            createImplicitNets(*instanceSyntax, context, netType, implicitNetNames, results);
            results.append(builder.create(*instanceSyntax));
        }
    }
}

void InstanceSymbol::fromBindDirective(const Scope& scope, const BindDirectiveSyntax& syntax) {
    auto& comp = scope.getCompilation();
    BindContext context(scope, LookupLocation::max);
    const Definition* targetDef = nullptr;

    // TODO: check results of noteBindDirective

    auto createInstances = [&](const Scope& targetScope) {
        SmallVectorSized<const Symbol*, 4> instances;
        fromSyntax(comp, *syntax.instantiation, LookupLocation::max, targetScope, instances);

        // If instances is an empty array, an error must have occurred and we should
        // not attempt creating more instances later.
        if (instances.empty())
            return false;

        // The nature of bind directives makes this const_cast necessary; we maintain the
        // outward invariant of a scope having all its members by making the Compilation
        // object search through all instances and find bind directives up front before
        // handing off access to any nodes.
        Scope& newScope = const_cast<Scope&>(targetScope);
        for (auto inst : instances)
            newScope.addMember(*inst);

        return true;
    };

    // If an instance list is given, then the target name must be a definition name.
    // Otherwise, the target name can be either an instance name or a definition name,
    // preferencing the instance if found.
    if (syntax.targetInstances) {
        comp.noteBindDirective(syntax, nullptr);

        // TODO: The parser checks for an invalid target name here.
        if (syntax.target->kind != SyntaxKind::IdentifierName)
            return;

        Token name = syntax.target->as<IdentifierNameSyntax>().identifier;
        targetDef = comp.getDefinition(name.valueText(), scope);
        if (!targetDef) {
            scope.addDiag(diag::UnknownModule, name.range()) << name.valueText();
            return;
        }

        // TODO: check that def is not a program here

        for (auto inst : syntax.targetInstances->targets) {
            LookupResult result;
            Lookup::name(*inst, context, LookupFlags::None, result);
            result.reportErrors(context);

            if (result.found) {
                // TODO: check valid target
                // TODO: check that instance is of targetDef
                if (!createInstances(result.found->as<InstanceSymbol>().body))
                    return;
            }
        }
    }
    else {
        LookupResult result;
        Lookup::name(*syntax.target, context, LookupFlags::None, result);

        if (result.found) {
            // TODO: check valid target
            comp.noteBindDirective(syntax, nullptr);
            createInstances(result.found->as<InstanceSymbol>().body);
        }
        else {
            // If we didn't find the name as an instance, try as a definition.
            if (syntax.target->kind == SyntaxKind::IdentifierName) {
                Token name = syntax.target->as<IdentifierNameSyntax>().identifier;
                targetDef = comp.getDefinition(name.valueText(), scope);
            }

            comp.noteBindDirective(syntax, targetDef);

            // If no name and no definition, report an error.
            if (!targetDef) {
                result.reportErrors(context);
                return;
            }
        }
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

    resolvePortConnections();
    serializer.startArray("connections");
    for (auto& [_, connPtr] : *connections) {
        serializer.startObject();
        reinterpret_cast<const PortConnection*>(connPtr)->serializeTo(serializer);
        serializer.endObject();
    }
    serializer.endArray();
}

InstanceBodySymbol::InstanceBodySymbol(Compilation& compilation, const InstanceCacheKey& cacheKey,
                                       const ParamOverrideNode* paramOverrideNode,
                                       span<const ParameterSymbolBase* const> parameters,
                                       bool isUninstantiated) :
    Symbol(SymbolKind::InstanceBody, cacheKey.getDefinition().name,
           cacheKey.getDefinition().location),
    Scope(compilation, this), paramOverrideNode(paramOverrideNode), parameters(parameters),
    isUninstantiated(isUninstantiated), cacheKey(cacheKey) {
    setParent(cacheKey.getDefinition().scope, cacheKey.getDefinition().indexInScope);
}

const InstanceBodySymbol& InstanceBodySymbol::cloneUncached() const {
    auto& result = fromDefinition(getCompilation(), getCacheKey(), paramOverrideNode, parameters,
                                  isUninstantiated, /* forceUncached */ true);

    // const_cast is ok here only because we pass forceUncached above, which ensures
    // the function just created a new instance.
    auto scope = getParentScope();
    ASSERT(scope);
    const_cast<InstanceBodySymbol&>(result).setParent(*scope, getIndex());

    return result;
}

const InstanceBodySymbol& InstanceBodySymbol::fromDefinition(
    Compilation& compilation, const Definition& definition, bool isUninstantiated,
    const ParamOverrideNode* paramOverrideNode) {

    ParameterBuilder paramBuilder(definition.scope, definition.name, definition.parameters);
    if (paramOverrideNode)
        paramBuilder.setOverrides(paramOverrideNode->overrides);

    createParams(compilation, definition, paramBuilder, LookupLocation::max, definition.location,
                 isUninstantiated);

    return fromDefinition(compilation, InstanceCacheKey(definition, {}, {}), paramOverrideNode,
                          paramBuilder.paramSymbols, isUninstantiated);
}

const InstanceBodySymbol* InstanceBodySymbol::fromDefinition(
    const Scope& scope, LookupLocation lookupLocation, SourceLocation sourceLoc,
    const Definition& definition, const ParameterValueAssignmentSyntax* parameterSyntax) {

    ParameterBuilder paramBuilder(scope, definition.name, definition.parameters);
    if (parameterSyntax)
        paramBuilder.setAssignments(*parameterSyntax);

    auto& comp = scope.getCompilation();
    if (!createParams(comp, definition, paramBuilder, lookupLocation, sourceLoc,
                      /* isUninstantiated */ false)) {
        return nullptr;
    }

    InstanceCacheKey cacheKey(definition, paramBuilder.paramValues.copy(comp),
                              paramBuilder.typeParams.copy(comp));

    return &fromDefinition(comp, cacheKey, nullptr, paramBuilder.paramSymbols,
                           /* isUninstantiated */ false);
}

static span<const ParameterSymbolBase* const> copyParams(
    BumpAllocator& alloc, span<const ParameterSymbolBase* const> source) {
    if (source.empty())
        return {};

    using PSB = const ParameterSymbolBase*;
    PSB* ptr = reinterpret_cast<PSB*>(alloc.allocate(source.size() * sizeof(PSB), alignof(PSB)));
    memcpy(ptr, source.data(), source.size() * sizeof(PSB));

    return span<PSB const>(ptr, source.size());
}

const InstanceBodySymbol& InstanceBodySymbol::fromDefinition(
    Compilation& comp, const InstanceCacheKey& cacheKey, const ParamOverrideNode* paramOverrideNode,
    span<const ParameterSymbolBase* const> parameters, bool isUninstantiated, bool forceUncached) {

    // If there's already a cached body for this key, return that instead of creating a new one.
    if (!paramOverrideNode && !forceUncached) {
        if (auto cached = comp.getInstanceCache().find(cacheKey))
            return *cached;
    }

    auto& declSyntax = cacheKey.getDefinition().syntax;
    auto result = comp.emplace<InstanceBodySymbol>(comp, cacheKey, paramOverrideNode,
                                                   copyParams(comp, parameters), isUninstantiated);
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

void UnknownModuleSymbol::fromSyntax(Compilation& compilation,
                                     const HierarchyInstantiationSyntax& syntax,
                                     LookupLocation location, const Scope& scope,
                                     SmallVector<const Symbol*>& results) {
    SmallVectorSized<const Expression*, 8> params;
    BindContext context(scope, location, BindFlags::NonProcedural);

    if (syntax.parameters) {
        for (auto expr : syntax.parameters->assignments->parameters) {
            // Empty expressions are just ignored here.
            if (expr->kind == SyntaxKind::OrderedArgument)
                params.append(&Expression::bind(*expr->as<OrderedArgumentSyntax>().expr, context));
            else if (expr->kind == SyntaxKind::NamedArgument) {
                if (auto ex = expr->as<NamedArgumentSyntax>().expr)
                    params.append(&Expression::bind(*ex, context));
            }
        }
    }

    SmallSet<string_view, 8> implicitNetNames;
    auto& netType = scope.getDefaultNetType();
    auto paramSpan = params.copy(compilation);

    for (auto instanceSyntax : syntax.instances) {
        createImplicitNets(*instanceSyntax, context, netType, implicitNetNames, results);

        SmallVectorSized<const Expression*, 8> ports;
        for (auto port : instanceSyntax->connections) {
            if (port->kind == SyntaxKind::OrderedPortConnection)
                ports.append(
                    &Expression::bind(*port->as<OrderedPortConnectionSyntax>().expr, context));
            else if (port->kind == SyntaxKind::NamedPortConnection) {
                if (auto ex = port->as<NamedPortConnectionSyntax>().expr)
                    ports.append(&Expression::bind(*ex, context));
            }
        }

        auto name = instanceSyntax->name;
        results.append(compilation.emplace<UnknownModuleSymbol>(
            name.valueText(), name.location(), paramSpan, ports.copy(compilation)));
    }
}

void UnknownModuleSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("parameters");
    for (auto expr : paramExpressions)
        serializer.serialize(*expr);
    serializer.endArray();

    serializer.startArray("ports");
    for (auto expr : portConnections)
        serializer.serialize(*expr);
    serializer.endArray();
}

} // namespace slang
