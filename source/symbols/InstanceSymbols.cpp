//------------------------------------------------------------------------------
// InstanceSymbols.cpp
// Contains instance-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/InstanceSymbols.h"

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
                    span<const AttributeInstanceSyntax* const> attributes) :
        compilation(context.getCompilation()),
        context(context), cacheKeyBase(cacheKeyBase), parameters(parameters),
        attributes(attributes) {}

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

    Symbol* createInstance(const HierarchicalInstanceSyntax& syntax) {
        // Find all port connections to interface instances so we can
        // extract their cache keys.
        auto& def = cacheKeyBase.getDefinition();
        SmallVectorSized<const InstanceCacheKey*, 8> ifaceKeys;
        InterfacePortSymbol::findInterfaceInstanceKeys(context.scope, def, syntax.connections,
                                                       ifaceKeys);

        // Try to look up a cached instance using our own key to avoid redoing work.
        InstanceCacheKey cacheKey = cacheKeyBase;
        if (!ifaceKeys.empty())
            cacheKey.setInterfacePortKeys(ifaceKeys.copy(compilation));

        auto inst = compilation.emplace<InstanceSymbol>(
            compilation, syntax.name.valueText(), syntax.name.location(), cacheKey, parameters);

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
        EvaluatedDimension dim = context.evalDimension(**it, true);
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

void createParams(Compilation& compilation, const Definition& definition, const Scope& scope,
                  LookupLocation ll, SourceLocation instanceLoc,
                  SmallMap<string_view, const ExpressionSyntax*, 8>& paramOverrides,
                  SmallVector<const ParameterSymbolBase*>& parameters,
                  SmallVector<const ConstantValue*>& paramValues,
                  SmallVector<const Type*>& typeParams) {
    // Construct a temporary scope that has the right parent to house instance parameters
    // as we're evaluating them. We hold on to the initializer expressions and give them
    // to the instances later when we create them.
    struct TempInstance : public InstanceBodySymbol {
        TempInstance(Compilation& compilation, const Definition& definition) :
            InstanceBodySymbol(compilation, InstanceCacheKey(definition, {}, {})) {
            setParent(definition.scope);
        }
    };

    auto& tempDef = *compilation.emplace<TempInstance>(compilation, definition);

    // Need the imports here as well, since parameters may depend on them.
    for (auto import : definition.syntax.header->imports)
        tempDef.addMembers(*import);

    BindContext context(scope, ll, BindFlags::Constant);
    for (auto& param : definition.parameters) {
        if (!param.isTypeParam) {
            // This is a value parameter.
            const ExpressionSyntax* newInitializer = nullptr;
            if (auto it = paramOverrides.find(param.name); it != paramOverrides.end())
                newInitializer = it->second;

            auto& newParam = ParameterSymbol::fromDecl(param, tempDef, context, newInitializer);
            parameters.append(&newParam);
            if (newParam.isLocalParam())
                continue;

            // For all port params, if we were provided a parameter override save
            // that value now for use with the cache key. Otherwise use a nullptr
            // to represent that the default will be used. We can't evaluate the
            // default now because it might depend on other members that haven't
            // been created yet.
            if (newInitializer)
                paramValues.append(&newParam.getValue());
            else
                paramValues.append(nullptr);

            if (newParam.isPortParam() && !newParam.getDeclaredType()->getInitializerSyntax()) {
                auto& diag = scope.addDiag(diag::ParamHasNoValue, instanceLoc);
                diag << definition.name;
                diag << newParam.name;
            }
        }
        else {
            // Otherwise this is a type parameter.
            const ExpressionSyntax* newInitializer = nullptr;
            if (auto it = paramOverrides.find(param.name); it != paramOverrides.end())
                newInitializer = it->second;

            auto& newParam = TypeParameterSymbol::fromDecl(param, tempDef, context, newInitializer);
            parameters.append(&newParam);
            if (newParam.isLocalParam())
                continue;

            if (newInitializer)
                typeParams.append(&newParam.targetType.getType());
            else
                typeParams.append(nullptr);

            if (!newInitializer && newParam.isPortParam() && !newParam.targetType.getTypeSyntax()) {
                auto& diag = scope.addDiag(diag::ParamHasNoValue, instanceLoc);
                diag << definition.name;
                diag << newParam.name;
            }
        }
    }
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
                               const Definition& definition) :
    Symbol(SymbolKind::Instance, name, loc),
    body(InstanceBodySymbol::fromDefinition(compilation, definition)) {
    compilation.addInstance(*this);
}

InstanceSymbol::InstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                               const InstanceCacheKey& cacheKey,
                               span<const ParameterSymbolBase* const> parameters) :
    Symbol(SymbolKind::Instance, name, loc),
    body(InstanceBodySymbol::fromDefinition(compilation, cacheKey, parameters)) {
    compilation.addInstance(*this);
}

void InstanceSymbol::fromSyntax(Compilation& compilation,
                                const HierarchyInstantiationSyntax& syntax, LookupLocation location,
                                const Scope& scope, SmallVector<const Symbol*>& results) {
    auto definition = compilation.getDefinition(syntax.type.valueText(), scope);
    if (!definition) {
        scope.addDiag(diag::UnknownModule, syntax.type.range()) << syntax.type.valueText();
        return;
    }

    SmallMap<string_view, const ExpressionSyntax*, 8> paramOverrides;
    if (syntax.parameters) {
        // Build up data structures to easily index the parameter assignments. We need to handle
        // both ordered assignment as well as named assignment, though a specific instance can only
        // use one method or the other.
        bool hasParamAssignments = false;
        bool orderedAssignments = true;
        SmallVectorSized<const OrderedArgumentSyntax*, 8> orderedParams;
        SmallMap<string_view, std::pair<const NamedArgumentSyntax*, bool>, 8> namedParams;

        for (auto paramBase : syntax.parameters->assignments->parameters) {
            bool isOrdered = paramBase->kind == SyntaxKind::OrderedArgument;
            if (!hasParamAssignments) {
                hasParamAssignments = true;
                orderedAssignments = isOrdered;
            }
            else if (isOrdered != orderedAssignments) {
                scope.addDiag(diag::MixingOrderedAndNamedParams,
                              paramBase->getFirstToken().location());
                break;
            }

            if (isOrdered)
                orderedParams.append(&paramBase->as<OrderedArgumentSyntax>());
            else {
                const NamedArgumentSyntax& nas = paramBase->as<NamedArgumentSyntax>();
                auto name = nas.name.valueText();
                if (!name.empty()) {
                    auto pair = namedParams.emplace(name, std::make_pair(&nas, false));
                    if (!pair.second) {
                        auto& diag =
                            scope.addDiag(diag::DuplicateParamAssignment, nas.name.location());
                        diag << name;
                        diag.addNote(diag::NotePreviousUsage,
                                     pair.first->second.first->name.location());
                    }
                }
            }
        }

        // For each parameter assignment we have, match it up to a real parameter
        if (orderedAssignments) {
            uint32_t orderedIndex = 0;
            for (auto& param : definition->parameters) {
                if (orderedIndex >= orderedParams.size())
                    break;

                if (param.isLocalParam)
                    continue;

                paramOverrides.emplace(param.name, orderedParams[orderedIndex++]->expr);
            }

            // Make sure there aren't extra param assignments for non-existent params.
            if (orderedIndex < orderedParams.size()) {
                auto loc = orderedParams[orderedIndex]->getFirstToken().location();
                auto& diag = scope.addDiag(diag::TooManyParamAssignments, loc);
                diag << definition->name;
                diag << orderedParams.size();
                diag << orderedIndex;
            }
        }
        else {
            // Otherwise handle named assignments.
            for (auto& param : definition->parameters) {
                auto it = namedParams.find(param.name);
                if (it == namedParams.end())
                    continue;

                const NamedArgumentSyntax* arg = it->second.first;
                it->second.second = true;
                if (param.isLocalParam) {
                    // Can't assign to localparams, so this is an error.
                    DiagCode code = param.isPortParam ? diag::AssignedToLocalPortParam
                                                      : diag::AssignedToLocalBodyParam;

                    auto& diag = scope.addDiag(code, arg->name.location());
                    diag.addNote(diag::NoteDeclarationHere, param.location);
                    continue;
                }

                // It's allowed to have no initializer in the assignment; it means to just use the
                // default.
                if (!arg->expr)
                    continue;

                paramOverrides.emplace(param.name, arg->expr);
            }

            for (const auto& pair : namedParams) {
                // We marked all the args that we used, so anything left over is a param assignment
                // for a non-existent parameter.
                if (!pair.second.second) {
                    auto& diag = scope.addDiag(diag::ParameterDoesNotExist,
                                               pair.second.first->name.location());
                    diag << pair.second.first->name.valueText();
                    diag << definition->name;
                }
            }
        }
    }

    // Determine values for all parameters now so that they can be
    // shared between instances, and so that we can use them to create
    // a cache key to lookup any instance bodies that may already be
    // suitable for the new instances we're about to create.
    SmallVectorSized<const ParameterSymbolBase*, 8> parameters;
    SmallVectorSized<const ConstantValue*, 8> paramValues;
    SmallVectorSized<const Type*, 8> typeParams;
    createParams(compilation, *definition, scope, location, syntax.getFirstToken().location(),
                 paramOverrides, parameters, paramValues, typeParams);

    BindContext context(scope, location);
    InstanceCacheKey cacheKey(*definition, paramValues.copy(compilation),
                              typeParams.copy(compilation));

    InstanceBuilder builder(context, cacheKey, parameters, syntax.attributes);

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

InstanceBodySymbol::InstanceBodySymbol(Compilation& compilation, const InstanceCacheKey& cacheKey) :
    Symbol(SymbolKind::InstanceBody, cacheKey.getDefinition().name,
           cacheKey.getDefinition().location),
    Scope(compilation, this), cacheKey(cacheKey) {
    setParent(cacheKey.getDefinition().scope, cacheKey.getDefinition().indexInScope);
}

InstanceBodySymbol& InstanceBodySymbol::fromDefinition(Compilation& compilation,
                                                       const Definition& definition) {
    // Create parameters with all default values set.
    SmallMap<string_view, const ExpressionSyntax*, 8> unused;
    SmallVectorSized<const ParameterSymbolBase*, 2> parameters;
    SmallVectorSized<const ConstantValue*, 2> paramValues;
    SmallVectorSized<const Type*, 2> typeParams;

    createParams(compilation, definition, definition.scope, LookupLocation::max,
                 definition.location, unused, parameters, paramValues, typeParams);

    return fromDefinition(compilation, InstanceCacheKey(definition, {}, {}), parameters);
}

InstanceBodySymbol& InstanceBodySymbol::fromDefinition(
    Compilation& comp, const InstanceCacheKey& cacheKey,
    span<const ParameterSymbolBase* const> parameters) {

    auto& declSyntax = cacheKey.getDefinition().syntax;
    auto result = comp.emplace<InstanceBodySymbol>(comp, cacheKey);
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
