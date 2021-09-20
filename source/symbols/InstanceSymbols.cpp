//------------------------------------------------------------------------------
// InstanceSymbols.cpp
// Contains instance-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/InstanceSymbols.h"

#include "ParameterBuilder.h"

#include "slang/binding/AssertionExpr.h"
#include "slang/binding/Expression.h"
#include "slang/binding/TimingControl.h"
#include "slang/compilation/Compilation.h"
#include "slang/compilation/Definition.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/ParserDiags.h"
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

std::pair<string_view, SourceLocation> getNameLoc(const HierarchicalInstanceSyntax& syntax) {
    string_view name;
    SourceLocation loc;
    if (syntax.decl) {
        name = syntax.decl->name.valueText();
        loc = syntax.decl->name.location();
    }
    else {
        name = "";
        loc = syntax.getFirstToken().location();
    }
    return std::make_pair(name, loc);
}

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

        if (!syntax.decl) {
            context.addDiag(diag::InstanceNameRequired, syntax.sourceRange());
            return createInstance(syntax);
        }

        auto dims = syntax.decl->dimensions;
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
        InterfacePortSymbol::findInterfaceInstanceKeys(*context.scope, def, syntax.connections,
                                                       ifaceKeys);

        // Try to look up a cached instance using our own key to avoid redoing work.
        InstanceCacheKey cacheKey = cacheKeyBase;
        if (!ifaceKeys.empty())
            cacheKey.setInterfacePortKeys(ifaceKeys.copy(compilation));

        auto [name, loc] = getNameLoc(syntax);
        auto inst = compilation.emplace<InstanceSymbol>(
            compilation, name, loc, cacheKey, paramOverrideNode, parameters, isUninstantiated);

        inst->arrayPath = path.copy(compilation);
        inst->setSyntax(syntax);
        inst->setAttributes(*context.scope, attributes);
        return inst;
    }

    Symbol* recurse(const HierarchicalInstanceSyntax& syntax, DimIterator it, DimIterator end) {
        if (it == end)
            return createInstance(syntax);

        // Evaluate the dimensions of the array. If this fails for some reason,
        // make up an empty array so that we don't get further errors when
        // things try to reference this symbol.
        ASSERT(syntax.decl);
        auto nameToken = syntax.decl->name;
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
        const PropertyExprSyntax* expr = nullptr;
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

void getInstanceArrayDimensions(const InstanceArraySymbol& array,
                                SmallVector<ConstantRange>& dimensions) {
    auto scope = array.getParentScope();
    if (scope && scope->asSymbol().kind == SymbolKind::InstanceArray)
        getInstanceArrayDimensions(scope->asSymbol().as<InstanceArraySymbol>(), dimensions);

    dimensions.append(array.range);
}

} // namespace

namespace slang {

string_view InstanceSymbolBase::getArrayName() const {
    auto scope = getParentScope();
    if (scope && scope->asSymbol().kind == SymbolKind::InstanceArray)
        return scope->asSymbol().as<InstanceArraySymbol>().getArrayName();

    return name;
}

void InstanceSymbolBase::getArrayDimensions(SmallVector<ConstantRange>& dimensions) const {
    auto scope = getParentScope();
    if (scope && scope->asSymbol().kind == SymbolKind::InstanceArray)
        getInstanceArrayDimensions(scope->asSymbol().as<InstanceArraySymbol>(), dimensions);
}

InstanceSymbol::InstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                               const InstanceBodySymbol& body) :
    InstanceSymbolBase(SymbolKind::Instance, name, loc),
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

static const ParamOverrideNode* findParentOverrideNode(const Scope& scope) {
    auto& sym = scope.asSymbol();
    if (sym.kind == SymbolKind::InstanceBody)
        return sym.as<InstanceBodySymbol>().paramOverrideNode;

    // Guaranteed to have a parent here since we never get called otherwise.
    auto node = findParentOverrideNode(*sym.getParentScope());
    if (!node)
        return nullptr;

    auto it = node->childNodes.find(std::string(sym.name));
    if (it == node->childNodes.end())
        return nullptr;

    return &it->second;
}

void InstanceSymbol::fromSyntax(Compilation& compilation,
                                const HierarchyInstantiationSyntax& syntax,
                                const BindContext& context, SmallVector<const Symbol*>& results,
                                SmallVector<const Symbol*>& implicitNets) {
    // Find our parent instance.
    const Scope* currScope = context.scope;
    while (currScope && currScope->asSymbol().kind != SymbolKind::InstanceBody)
        currScope = currScope->asSymbol().getParentScope();

    const Definition* owningDefinition = nullptr;
    const ParamOverrideNode* parentOverrideNode = nullptr;
    bool isUninstantiated = false;
    if (currScope) {
        auto& instanceBody = currScope->asSymbol().as<InstanceBodySymbol>();
        isUninstantiated = instanceBody.isUninstantiated;
        owningDefinition = &instanceBody.getDefinition();

        // In the uncommon case that our parent instance has a param override
        // node set, we need to go back and make sure we account for any
        // generate blocks that might actually be along the parent path for
        // the new instances we're creating.
        if (instanceBody.paramOverrideNode)
            parentOverrideNode = findParentOverrideNode(*context.scope);
    }

    auto definition = compilation.getDefinition(syntax.type.valueText(), *context.scope);
    if (!definition) {
        // This might actually be a user-defined primitive instantiation.
        if (auto prim = compilation.getPrimitive(syntax.type.valueText())) {
            PrimitiveInstanceSymbol::fromSyntax(*prim, syntax, context, results, implicitNets);
            if (!results.empty() &&
                (!owningDefinition || owningDefinition->definitionKind != DefinitionKind::Module)) {
                context.addDiag(diag::InvalidPrimInstanceForParent, syntax.type.range());
            }
        }
        else {
            if (!isUninstantiated)
                context.addDiag(diag::UnknownModule, syntax.type.range())
                    << syntax.type.valueText();

            UnknownModuleSymbol::fromSyntax(compilation, syntax, context, results, implicitNets);
        }
        return;
    }

    if (owningDefinition) {
        auto owningKind = owningDefinition->definitionKind;
        if (owningKind == DefinitionKind::Program ||
            (owningKind == DefinitionKind::Interface &&
             definition->definitionKind == DefinitionKind::Module)) {
            context.addDiag(diag::InvalidInstanceForParent, syntax.type.range())
                << definition->getArticleKindString() << owningDefinition->getArticleKindString();
        }
    }

    // We have to check each port connection expression for any names that can't be resolved,
    // which represent implicit nets that need to be created now.
    SmallSet<string_view, 8> implicitNetNames;
    auto& netType = context.scope->getDefaultNetType();

    // The common case is that our parent doesn't have a parameter override node,
    // which lets us evaluate all parameter assignments for this instance in a batch.
    if (!parentOverrideNode) {
        ParameterBuilder paramBuilder(*context.scope, definition->name, definition->parameters);
        if (syntax.parameters)
            paramBuilder.setAssignments(*syntax.parameters);

        // Determine values for all parameters now so that they can be
        // shared between instances, and so that we can use them to create
        // a cache key to lookup any instance bodies that may already be
        // suitable for the new instances we're about to create.
        createParams(compilation, *definition, paramBuilder, context.getLocation(),
                     syntax.getFirstToken().location(), isUninstantiated);

        InstanceCacheKey cacheKey(*definition, paramBuilder.paramValues.copy(compilation),
                                  paramBuilder.typeParams.copy(compilation));

        InstanceBuilder builder(context, cacheKey, nullptr, paramBuilder.paramSymbols,
                                syntax.attributes, isUninstantiated);

        for (auto instanceSyntax : syntax.instances) {
            createImplicitNets(*instanceSyntax, context, netType, implicitNetNames, implicitNets);
            results.append(builder.create(*instanceSyntax));
        }
    }
    else {
        // Otherwise we need to evaluate parameters separately for each child.
        for (auto instanceSyntax : syntax.instances) {
            const ParamOverrideNode* overrideNode = nullptr;

            if (instanceSyntax->decl) {
                auto instName = instanceSyntax->decl->name.valueText();
                if (!instName.empty()) {
                    if (auto it = parentOverrideNode->childNodes.find(std::string(instName));
                        it != parentOverrideNode->childNodes.end()) {
                        overrideNode = &it->second;
                    }
                }
            }

            ParameterBuilder paramBuilder(*context.scope, definition->name, definition->parameters);
            if (syntax.parameters)
                paramBuilder.setAssignments(*syntax.parameters);
            if (overrideNode)
                paramBuilder.setOverrides(overrideNode->overrides);

            // Determine values for all parameters now so that they can be
            // shared between instances, and so that we can use them to create
            // a cache key to lookup any instance bodies that may already be
            // suitable for the new instances we're about to create.
            createParams(compilation, *definition, paramBuilder, context.getLocation(),
                         syntax.getFirstToken().location(), isUninstantiated);

            InstanceCacheKey cacheKey(*definition, paramBuilder.paramValues.copy(compilation),
                                      paramBuilder.typeParams.copy(compilation));

            InstanceBuilder builder(context, cacheKey, overrideNode, paramBuilder.paramSymbols,
                                    syntax.attributes, isUninstantiated);

            createImplicitNets(*instanceSyntax, context, netType, implicitNetNames, implicitNets);
            results.append(builder.create(*instanceSyntax));
        }
    }
}

void InstanceSymbol::fromBindDirective(const Scope& scope, const BindDirectiveSyntax& syntax) {
    auto& comp = scope.getCompilation();
    const Definition* targetDef = nullptr;

    // TODO: check results of noteBindDirective

    auto createInstances = [&](const Scope& targetScope) {
        SmallVectorSized<const Symbol*, 4> instances;
        SmallVectorSized<const Symbol*, 4> implicitNets;
        BindContext ctx(targetScope, LookupLocation::max);
        fromSyntax(comp, *syntax.instantiation, ctx, instances, implicitNets);

        // If instances is an empty array, an error must have occurred and we should
        // not attempt creating more instances later.
        if (instances.empty())
            return false;

        // The nature of bind directives makes this const_cast necessary; we maintain the
        // outward invariant of a scope having all its members by making the Compilation
        // object search through all instances and find bind directives up front before
        // handing off access to any nodes.
        Scope& newScope = const_cast<Scope&>(targetScope);
        for (auto net : implicitNets)
            newScope.addMember(*net);
        for (auto inst : instances)
            newScope.addMember(*inst);

        return true;
    };

    // If an instance list is given, then the target name must be a definition name.
    // Otherwise, the target name can be either an instance name or a definition name,
    // preferencing the instance if found.
    BindContext context(scope, LookupLocation::max);
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
    const BindContext& context, SourceLocation sourceLoc, const Definition& definition,
    const ParameterValueAssignmentSyntax* parameterSyntax) {

    ParameterBuilder paramBuilder(*context.scope, definition.name, definition.parameters);
    if (parameterSyntax)
        paramBuilder.setAssignments(*parameterSyntax);

    auto& comp = context.getCompilation();
    if (!createParams(comp, definition, paramBuilder, context.getLocation(), sourceLoc,
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

template<typename TSyntax>
static void createUnknownModules(Compilation& compilation, const TSyntax& syntax,
                                 string_view moduleName, const BindContext& context,
                                 span<const Expression* const> params,
                                 SmallVector<const Symbol*>& results,
                                 SmallVector<const Symbol*>& implicitNets) {
    SmallSet<string_view, 8> implicitNetNames;
    auto& netType = context.scope->getDefaultNetType();
    for (auto instanceSyntax : syntax.instances) {
        createImplicitNets(*instanceSyntax, context, netType, implicitNetNames, implicitNets);

        auto [name, loc] = getNameLoc(*instanceSyntax);
        auto sym = compilation.emplace<UnknownModuleSymbol>(name, loc, moduleName, params);
        sym->setSyntax(*instanceSyntax);
        sym->setAttributes(*context.scope, syntax.attributes);
        results.append(sym);
    }
}

void UnknownModuleSymbol::fromSyntax(Compilation& compilation,
                                     const HierarchyInstantiationSyntax& syntax,
                                     const BindContext& parentContext,
                                     SmallVector<const Symbol*>& results,
                                     SmallVector<const Symbol*>& implicitNets) {
    SmallVectorSized<const Expression*, 8> params;
    BindContext context = parentContext.resetFlags(BindFlags::NonProcedural);

    if (syntax.parameters) {
        for (auto expr : syntax.parameters->parameters) {
            // Empty expressions are just ignored here.
            if (expr->kind == SyntaxKind::OrderedParamAssignment)
                params.append(
                    &Expression::bind(*expr->as<OrderedParamAssignmentSyntax>().expr, context));
            else if (expr->kind == SyntaxKind::NamedParamAssignment) {
                if (auto ex = expr->as<NamedParamAssignmentSyntax>().expr)
                    params.append(&Expression::bind(*ex, context));
            }
        }
    }

    auto paramSpan = params.copy(compilation);
    createUnknownModules(compilation, syntax, syntax.type.valueText(), context, paramSpan, results,
                         implicitNets);
}

void UnknownModuleSymbol::fromSyntax(Compilation& compilation,
                                     const PrimitiveInstantiationSyntax& syntax,
                                     const BindContext& parentContext,
                                     SmallVector<const Symbol*>& results,
                                     SmallVector<const Symbol*>& implicitNets) {
    BindContext context = parentContext.resetFlags(BindFlags::NonProcedural);
    createUnknownModules(compilation, syntax, syntax.type.valueText(), context, {}, results,
                         implicitNets);
}

span<const AssertionExpr* const> UnknownModuleSymbol::getPortConnections() const {
    if (!ports) {
        auto syntax = getSyntax();
        auto scope = getParentScope();
        ASSERT(syntax && scope);

        auto& comp = scope->getCompilation();
        BindContext context(*scope, LookupLocation::after(*this));

        SmallVectorSized<const AssertionExpr*, 8> results;
        SmallVectorSized<string_view, 8> names;
        for (auto port : syntax->as<HierarchicalInstanceSyntax>().connections) {
            if (port->kind == SyntaxKind::OrderedPortConnection) {
                names.append(""sv);
                results.append(
                    &AssertionExpr::bind(*port->as<OrderedPortConnectionSyntax>().expr, context));
            }
            else if (port->kind == SyntaxKind::NamedPortConnection) {
                auto& npc = port->as<NamedPortConnectionSyntax>();
                names.append(npc.name.valueText());

                if (auto ex = npc.expr)
                    results.append(&AssertionExpr::bind(*ex, context));
            }
        }

        ports = results.copy(comp);
        portNames = names.copy(comp);

        for (auto port : *ports) {
            if (port->kind != AssertionExprKind::Simple ||
                port->as<SimpleAssertionExpr>().repetition) {
                mustBeChecker = true;
                break;
            }
        }
    }
    return *ports;
}

span<string_view const> UnknownModuleSymbol::getPortNames() const {
    if (!ports)
        getPortConnections();
    return portNames;
}

void UnknownModuleSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("moduleName", moduleName);

    serializer.startArray("parameters");
    for (auto expr : paramExpressions)
        serializer.serialize(*expr);
    serializer.endArray();

    auto conns = getPortConnections();
    auto names = getPortNames();
    ASSERT(conns.size() == names.size());

    serializer.startArray("ports");
    for (size_t i = 0; i < conns.size(); i++) {
        serializer.startObject();
        if (!names[i].empty())
            serializer.write("name", names[i]);

        if (mustBeChecker) {
            serializer.write("expr", *conns[i]);
        }
        else {
            serializer.write("expr", conns[i]->as<SimpleAssertionExpr>().expr);
        }

        serializer.endObject();
    }
    serializer.endArray();
}

namespace {

PrimitiveInstanceSymbol* createPrimInst(Compilation& compilation, const Scope& scope,
                                        const PrimitiveSymbol& primitive,
                                        const HierarchicalInstanceSyntax& syntax,
                                        span<const AttributeInstanceSyntax* const> attributes,
                                        SmallVector<int32_t>& path) {
    auto [name, loc] = getNameLoc(syntax);
    auto result = compilation.emplace<PrimitiveInstanceSymbol>(name, loc, primitive);
    result->arrayPath = path.copy(compilation);
    result->setSyntax(syntax);
    result->setAttributes(scope, attributes);
    return result;
}

using DimIterator = span<VariableDimensionSyntax*>::iterator;

Symbol* recursePrimArray(Compilation& compilation, const PrimitiveSymbol& primitive,
                         const HierarchicalInstanceSyntax& instance, const BindContext& context,
                         DimIterator it, DimIterator end,
                         span<const AttributeInstanceSyntax* const> attributes,
                         SmallVector<int32_t>& path) {
    if (it == end)
        return createPrimInst(compilation, *context.scope, primitive, instance, attributes, path);

    // Evaluate the dimensions of the array. If this fails for some reason,
    // make up an empty array so that we don't get further errors when
    // things try to reference this symbol.
    ASSERT(instance.decl);
    auto nameToken = instance.decl->name;
    auto dim = context.evalDimension(**it, /* requireRange */ true, /* isPacked */ false);
    if (!dim.isRange()) {
        return compilation.emplace<InstanceArraySymbol>(
            compilation, nameToken.valueText(), nameToken.location(), span<const Symbol* const>{},
            ConstantRange());
    }

    ++it;

    ConstantRange range = dim.range;
    SmallVectorSized<const Symbol*, 8> elements;
    for (int32_t i = range.lower(); i <= range.upper(); i++) {
        path.append(i);
        auto symbol =
            recursePrimArray(compilation, primitive, instance, context, it, end, attributes, path);
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

template<typename TSyntax>
void createPrimitives(const PrimitiveSymbol& primitive, const TSyntax& syntax,
                      const BindContext& parentContext, SmallVector<const Symbol*>& results,
                      SmallVector<const Symbol*>& implicitNets) {
    SmallSet<string_view, 8> implicitNetNames;
    SmallVectorSized<int32_t, 4> path;

    BindContext context = parentContext.resetFlags(BindFlags::Constant);
    auto& comp = context.getCompilation();
    auto& netType = context.scope->getDefaultNetType();

    for (auto instance : syntax.instances) {
        path.clear();
        createImplicitNets(*instance, context, netType, implicitNetNames, implicitNets);

        if (!instance->decl) {
            results.append(createPrimInst(comp, *context.scope, primitive, *instance,
                                          syntax.attributes, path));
        }
        else {
            auto dims = instance->decl->dimensions;
            auto symbol = recursePrimArray(comp, primitive, *instance, context, dims.begin(),
                                           dims.end(), syntax.attributes, path);
            results.append(symbol);
        }
    }
}

} // namespace

void PrimitiveInstanceSymbol::fromSyntax(const PrimitiveSymbol& primitive,
                                         const HierarchyInstantiationSyntax& syntax,
                                         const BindContext& context,
                                         SmallVector<const Symbol*>& results,
                                         SmallVector<const Symbol*>& implicitNets) {
    createPrimitives(primitive, syntax, context, results, implicitNets);
}

void PrimitiveInstanceSymbol::fromSyntax(const PrimitiveInstantiationSyntax& syntax,
                                         const BindContext& context,
                                         SmallVector<const Symbol*>& results,
                                         SmallVector<const Symbol*>& implicitNets) {
    auto& comp = context.getCompilation();
    auto name = syntax.type.valueText();
    auto prim = syntax.type.kind == TokenKind::Identifier ? comp.getPrimitive(name)
                                                          : comp.getGateType(name);

    if (!prim) {
        // See if there is a definition with this name, which indicates an error
        // in providing a drive strength or net delay.
        if (comp.getDefinition(name, *context.scope)) {
            ASSERT(syntax.strength || syntax.delay);
            if (syntax.strength) {
                context.addDiag(diag::InstanceWithStrength, syntax.strength->sourceRange()) << name;
            }
            else {
                context.addDiag(diag::InstanceWithDelay,
                                syntax.delay->getFirstToken().location() + 1);
            }
        }
        else {
            // Find our parent instance to see if it is uninstantiated.
            const Scope* currScope = context.scope;
            while (currScope && currScope->asSymbol().kind != SymbolKind::InstanceBody)
                currScope = currScope->asSymbol().getParentScope();

            bool isUninstantiated =
                currScope && currScope->asSymbol().as<InstanceBodySymbol>().isUninstantiated;

            if (!isUninstantiated)
                context.addDiag(diag::UnknownPrimitive, syntax.type.range()) << name;
        }

        UnknownModuleSymbol::fromSyntax(comp, syntax, context, results, implicitNets);
        return;
    }

    createPrimitives(*prim, syntax, context, results, implicitNets);
}

span<const Expression* const> PrimitiveInstanceSymbol::getPortConnections() const {
    if (!ports) {
        auto syntax = getSyntax();
        auto scope = getParentScope();
        ASSERT(syntax && scope);

        auto& comp = scope->getCompilation();
        BindContext context(*scope, LookupLocation::after(*this), BindFlags::NonProcedural);
        context.instance = this;

        SmallVectorSized<const ExpressionSyntax*, 8> conns;
        auto& his = syntax->as<HierarchicalInstanceSyntax>();
        for (auto port : his.connections) {
            if (port->kind == SyntaxKind::OrderedPortConnection) {
                auto expr =
                    context.requireSimpleExpr(*port->as<OrderedPortConnectionSyntax>().expr);
                if (!expr) {
                    ports.emplace();
                    return *ports;
                }

                conns.append(expr);
            }
            else if (port->kind != SyntaxKind::EmptyPortConnection ||
                     primitiveType.primitiveKind != PrimitiveSymbol::UserDefined) {
                context.addDiag(diag::InvalidPrimitivePortConn, port->sourceRange());
                ports.emplace();
                return *ports;
            }
            else {
                context.addDiag(diag::EmptyUdpPort, port->sourceRange());
                conns.append(nullptr);
            }
        }

        SmallVectorSized<const Expression*, 8> results;
        if (primitiveType.primitiveKind == PrimitiveSymbol::NInput ||
            primitiveType.primitiveKind == PrimitiveSymbol::NOutput) {
            // Some of the built-in gates allow n-inputs or n-outputs; handle those specially.
            if (conns.size() < 2) {
                auto& diag = context.addDiag(diag::InvalidNGateCount, his.openParen.location());
                diag << primitiveType.name;
                ports.emplace();
                return *ports;
            }

            for (size_t i = 0; i < conns.size(); i++) {
                ArgumentDirection dir;
                if (primitiveType.primitiveKind == PrimitiveSymbol::NInput)
                    dir = i == 0 ? ArgumentDirection::Out : ArgumentDirection::In;
                else
                    dir = conns.size() - 1 ? ArgumentDirection::In : ArgumentDirection::Out;

                ASSERT(conns[i]);
                results.append(
                    &Expression::bindArgument(comp.getLogicType(), dir, *conns[i], context));
            }
        }
        else {
            if (conns.size() != primitiveType.ports.size()) {
                auto& diag =
                    context.addDiag(diag::PrimitivePortCountWrong, his.openParen.location());
                diag << primitiveType.name;
                diag << conns.size() << primitiveType.ports.size();
                ports.emplace();
                return *ports;
            }

            for (size_t i = 0; i < conns.size(); i++) {
                if (!conns[i])
                    continue;

                ArgumentDirection dir = ArgumentDirection::In;
                switch (primitiveType.ports[i]->direction) {
                    case PrimitivePortDirection::In:
                        dir = ArgumentDirection::In;
                        break;
                    case PrimitivePortDirection::InOut:
                        dir = ArgumentDirection::InOut;
                        break;
                    case PrimitivePortDirection::Out:
                    case PrimitivePortDirection::OutReg:
                        dir = ArgumentDirection::Out;
                        break;
                }
                results.append(
                    &Expression::bindArgument(comp.getLogicType(), dir, *conns[i], context));
            }
        }

        ports = results.copy(scope->getCompilation());
    }
    return *ports;
}

const TimingControl* PrimitiveInstanceSymbol::getDelay() const {
    if (delay)
        return *delay;

    auto scope = getParentScope();
    auto syntax = getSyntax();
    if (!scope || !syntax || !syntax->parent) {
        delay = nullptr;
        return nullptr;
    }

    BindContext context(*scope, LookupLocation::before(*this), BindFlags::NonProcedural);

    auto& parent = *syntax->parent;
    if (parent.kind == SyntaxKind::HierarchyInstantiation) {
        if (auto params = parent.as<HierarchyInstantiationSyntax>().parameters) {
            delay = &Delay3Control::fromParams(scope->getCompilation(), *params, context);
            if (delay.value()->kind == TimingControlKind::Delay3) {
                if (auto d3 = delay.value()->as<Delay3Control>().expr3)
                    context.addDiag(diag::Delay3UdpNotAllowed, d3->sourceRange);
            }
            return *delay;
        }
    }
    else {
        auto delaySyntax = parent.as<PrimitiveInstantiationSyntax>().delay;
        if (delaySyntax) {
            delay = &TimingControl::bind(*delaySyntax, context);
            return *delay;
        }
    }

    delay = nullptr;
    return nullptr;
}

void PrimitiveInstanceSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.writeLink("primitiveType", primitiveType);

    serializer.startArray("ports");
    for (auto expr : getPortConnections())
        serializer.serialize(*expr);
    serializer.endArray();

    if (auto delayCtrl = getDelay())
        serializer.write("delay", *delayCtrl);
}

} // namespace slang
