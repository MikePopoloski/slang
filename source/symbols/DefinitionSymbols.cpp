//------------------------------------------------------------------------------
// DefinitionSymbols.cpp
// Contains definition-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/DefinitionSymbols.h"

#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/compilation/Definition.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/ParameterSymbols.h"
#include "slang/symbols/Type.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/StackContainer.h"

namespace slang {

DefinitionSymbol::DefinitionSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                                   DefinitionKind definitionKind, VariableLifetime defaultLifetime,
                                   const NetType& defaultNetType,
                                   UnconnectedDrive unconnectedDrive) :
    Symbol(SymbolKind::Definition, name, loc),
    Scope(compilation, this), defaultNetType(defaultNetType), definitionKind(definitionKind),
    defaultLifetime(defaultLifetime), unconnectedDrive(unconnectedDrive),
    portMap(compilation.allocSymbolMap()) {
}

const ModportSymbol* DefinitionSymbol::getModportOrError(string_view modport, const Scope& scope,
                                                         SourceRange range) const {
    if (modport.empty())
        return nullptr;

    auto symbol = find(modport);
    if (!symbol) {
        auto& diag = scope.addDiag(diag::UnknownMember, range);
        diag << modport;
        diag << this->name;
        return nullptr;
    }

    if (symbol->kind != SymbolKind::Modport) {
        auto& diag = scope.addDiag(diag::NotAModport, range);
        diag << modport;
        diag.addNote(diag::NoteDeclarationHere, symbol->location);
        return nullptr;
    }

    return &symbol->as<ModportSymbol>();
}

DefinitionSymbol& DefinitionSymbol::fromSyntax(Compilation& compilation,
                                               const ModuleDeclarationSyntax& syntax,
                                               const Scope& scope) {
    auto nameToken = syntax.header->name;
    DefinitionKind definitionKind = SemanticFacts::getDefinitionKind(syntax.kind);
    VariableLifetime lifetime = SemanticFacts::getVariableLifetime(syntax.header->lifetime)
                                    .value_or(VariableLifetime::Static);
    const NetType& defaultNetType = compilation.getDefaultNetType(syntax);
    UnconnectedDrive unconnectedDrive = compilation.getUnconnectedDrive(syntax);

    auto result = compilation.emplace<DefinitionSymbol>(compilation, nameToken.valueText(),
                                                        nameToken.location(), definitionKind,
                                                        lifetime, defaultNetType, unconnectedDrive);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    for (auto import : syntax.header->imports)
        result->addMembers(*import);

    SmallVectorSized<const ParameterSymbolBase*, 8> parameters;
    bool hasPortParams = syntax.header->parameters;
    if (hasPortParams) {
        bool lastLocal = false;
        for (auto declaration : syntax.header->parameters->declarations) {
            // It's legal to leave off the parameter keyword in the parameter port list.
            // If you do so, we "inherit" the parameter or localparam keyword from the previous
            // entry. This isn't allowed in a module body, but the parser will take care of the
            // error for us.
            if (declaration->keyword)
                lastLocal = declaration->keyword.kind == TokenKind::LocalParamKeyword;

            if (declaration->kind == SyntaxKind::ParameterDeclaration) {
                SmallVectorSized<ParameterSymbol*, 8> params;
                ParameterSymbol::fromSyntax(*result, declaration->as<ParameterDeclarationSyntax>(),
                                            lastLocal, /* isPort */ true, params);

                for (auto param : params) {
                    parameters.append(param);
                    result->addMember(*param);
                }
            }
            else {
                SmallVectorSized<TypeParameterSymbol*, 8> params;
                TypeParameterSymbol::fromSyntax(*result,
                                                declaration->as<TypeParameterDeclarationSyntax>(),
                                                lastLocal, /* isPort */ true, params);

                for (auto param : params) {
                    parameters.append(param);
                    result->addMember(*param);
                }
            }
        }
    }

    if (syntax.header->ports)
        result->addMembers(*syntax.header->ports);

    bool first = true;
    for (auto member : syntax.members) {
        if (member->kind == SyntaxKind::TimeUnitsDeclaration)
            result->setTimeScale(*result, member->as<TimeUnitsDeclarationSyntax>(), first);
        else if (member->kind != SyntaxKind::ParameterDeclarationStatement) {
            result->addMembers(*member);
            first = false;
        }
        else {
            first = false;

            auto declaration = member->as<ParameterDeclarationStatementSyntax>().parameter;
            bool isLocal =
                hasPortParams || declaration->keyword.kind == TokenKind::LocalParamKeyword;

            if (declaration->kind == SyntaxKind::ParameterDeclaration) {
                SmallVectorSized<ParameterSymbol*, 8> params;
                ParameterSymbol::fromSyntax(*result, declaration->as<ParameterDeclarationSyntax>(),
                                            isLocal, false, params);

                for (auto param : params) {
                    parameters.append(param);
                    result->addMember(*param);
                }
            }
            else {
                SmallVectorSized<TypeParameterSymbol*, 8> params;
                TypeParameterSymbol::fromSyntax(*result,
                                                declaration->as<TypeParameterDeclarationSyntax>(),
                                                isLocal, false, params);

                for (auto param : params) {
                    parameters.append(param);
                    result->addMember(*param);
                }
            }
        }
    }

    result->finalizeTimeScale(scope, syntax);
    result->parameters = parameters.copy(compilation);
    return *result;
}

void DefinitionSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("definitionKind", toString(definitionKind));
}

namespace {

class InstanceBuilder {
public:
    InstanceBuilder(const BindContext& context, const Definition& definition,
                    span<const ParameterSymbolBase* const> parameters,
                    span<const AttributeInstanceSyntax* const> attributes,
                    uint32_t hierarchyDepth) :
        compilation(context.getCompilation()),
        context(context), definition(definition), parameters(parameters), attributes(attributes),
        hierarchyDepth(hierarchyDepth) {}

    Symbol* create(const HierarchicalInstanceSyntax& syntax) {
        path.clear();

        auto dims = syntax.dimensions;
        return recurse(syntax, dims.begin(), dims.end());
    }

private:
    using DimIterator = span<VariableDimensionSyntax*>::iterator;

    Compilation& compilation;
    const BindContext& context;
    const Definition& definition;
    SmallVectorSized<int32_t, 4> path;
    span<const ParameterSymbolBase* const> parameters;
    span<const AttributeInstanceSyntax* const> attributes;
    uint32_t hierarchyDepth;

    Symbol* createInstance(const HierarchicalInstanceSyntax& syntax) {
        InstanceSymbol* inst;
        switch (definition.definitionKind) {
            case DefinitionKind::Module:
                inst = &ModuleInstanceSymbol::instantiate(compilation, syntax, definition,
                                                          parameters, hierarchyDepth);
                break;
            case DefinitionKind::Interface:
                inst = &InterfaceInstanceSymbol::instantiate(compilation, syntax, definition,
                                                             parameters, hierarchyDepth);
                break;
            case DefinitionKind::Program:
                inst = &ProgramInstanceSymbol::instantiate(compilation, syntax, definition,
                                                           parameters, hierarchyDepth);
                break;
            default:
                THROW_UNREACHABLE;
        }

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
                  SmallVector<const ParameterSymbolBase*>& parameters) {
    // Construct a temporary scope that has the right parent to house instance parameters
    // as we're evaluating them. We hold on to the initializer expressions and give them
    // to the instances later when we create them.
    struct TempInstance : public ModuleInstanceSymbol {
        using ModuleInstanceSymbol::ModuleInstanceSymbol;
        void setParent(const Scope& scope) { ModuleInstanceSymbol::setParent(scope); }
    };

    auto& tempDef = *compilation.emplace<TempInstance>(compilation, definition.name,
                                                       definition.location, definition, 0u);
    tempDef.setParent(definition.scope);

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

            if (!newParam.isLocalParam() && newParam.isPortParam() &&
                !newParam.getDeclaredType()->getInitializerSyntax()) {
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

            if (!newInitializer && !newParam.isLocalParam() && newParam.isPortParam() &&
                !newParam.targetType.getTypeSyntax()) {
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

    // As an optimization, determine values for all parameters now so that they can be
    // shared between instances. That way an instance array with hundreds of entries
    // doesn't recompute the same param values over and over again.
    SmallVectorSized<const ParameterSymbolBase*, 8> parameters;
    createParams(compilation, *definition, scope, location, syntax.getFirstToken().location(),
                 paramOverrides, parameters);

    // In order to avoid infinitely recursive instantiations, keep track of how deep we are
    // in the hierarchy tree. Each instance knows, so we only need to walk up as far as our
    // nearest parent in order to know our own depth here.
    uint32_t hierarchyDepth = 0;
    const Symbol* parent = &scope.asSymbol();
    while (true) {
        if (InstanceSymbol::isKind(parent->kind)) {
            hierarchyDepth = parent->as<InstanceSymbol>().hierarchyDepth + 1;
            if (hierarchyDepth > compilation.getOptions().maxInstanceDepth) {
                auto& diag = scope.addDiag(diag::MaxInstanceDepthExceeded, syntax.type.range());
                diag << compilation.getOptions().maxInstanceDepth;
                return;
            }
            break;
        }

        auto s = parent->getParentScope();
        if (!s)
            break;

        parent = &s->asSymbol();
    }

    // We have to check each port connection expression for any names that can't be resolved,
    // which represent implicit nets that need to be created now.
    SmallSet<string_view, 8> implicitNetNames;
    auto& netType = scope.getDefaultNetType();

    BindContext context(scope, location);
    InstanceBuilder builder(context, *definition, parameters, syntax.attributes, hierarchyDepth);

    for (auto instanceSyntax : syntax.instances) {
        createImplicitNets(*instanceSyntax, context, netType, implicitNetNames, results);
        results.append(builder.create(*instanceSyntax));
    }
}

InstanceSymbol::InstanceSymbol(SymbolKind kind, Compilation& compilation, string_view name,
                               SourceLocation loc, const Definition& definition,
                               uint32_t hierarchyDepth) :
    Symbol(kind, name, loc),
    Scope(compilation, this), definition(definition), hierarchyDepth(hierarchyDepth),
    portMap(compilation.allocSymbolMap()) {
}

static void getInstanceArrayDimensions(const InstanceArraySymbol& array,
                                       SmallVector<ConstantRange>& dimensions) {
    auto scope = array.getParentScope();
    if (scope && scope->asSymbol().kind == SymbolKind::InstanceArray)
        getInstanceArrayDimensions(scope->asSymbol().as<InstanceArraySymbol>(), dimensions);

    dimensions.append(array.range);
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
    serializer.write("definition", definition.name);
}

bool InstanceSymbol::isKind(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::ModuleInstance:
        case SymbolKind::ProgramInstance:
        case SymbolKind::InterfaceInstance:
            return true;
        default:
            return false;
    }
}

void InstanceSymbol::populate(const HierarchicalInstanceSyntax* instanceSyntax,
                              span<const ParameterSymbolBase* const> parameters) {
    // TODO: getSyntax dependency
    auto& declSyntax = definition.syntax;
    Compilation& comp = getCompilation();

    // Package imports from the header always come first.
    for (auto import : declSyntax.header->imports)
        addMembers(*import);

    // Now add in all parameter ports.
    auto paramIt = parameters.begin();
    while (paramIt != parameters.end()) {
        auto original = *paramIt;
        if (!original->isPortParam())
            break;

        if (original->symbol.kind == SymbolKind::Parameter)
            addMember(original->symbol.as<ParameterSymbol>().clone(comp));
        else
            addMember(original->symbol.as<TypeParameterSymbol>().clone(comp));

        paramIt++;
    }

    // It's important that the port syntax is added before any body members, so that port
    // connections are elaborated before anything tries to depend on any interface port params.
    if (declSyntax.header->ports)
        addMembers(*declSyntax.header->ports);

    // Connect all ports to external sources.
    if (instanceSyntax)
        setPortConnections(instanceSyntax->connections);

    // Finally add members from the body.
    for (auto member : declSyntax.members) {
        // If this is a parameter declaration, we should already have metadata for it in our
        // parameters list. The list is given in declaration order, so we should be be able to move
        // through them incrementally.
        if (member->kind != SyntaxKind::ParameterDeclarationStatement)
            addMembers(*member);
        else {
            auto paramBase = member->as<ParameterDeclarationStatementSyntax>().parameter;
            if (paramBase->kind == SyntaxKind::ParameterDeclaration) {
                for (auto declarator : paramBase->as<ParameterDeclarationSyntax>().declarators) {
                    ASSERT(paramIt != parameters.end());

                    auto& symbol = (*paramIt)->symbol;
                    ASSERT(declarator->name.valueText() == symbol.name);

                    addMember(symbol.as<ParameterSymbol>().clone(comp));
                    paramIt++;
                }
            }
            else {
                for (auto declarator :
                     paramBase->as<TypeParameterDeclarationSyntax>().declarators) {
                    ASSERT(paramIt != parameters.end());

                    auto& symbol = (*paramIt)->symbol;
                    ASSERT(declarator->name.valueText() == symbol.name);

                    addMember(symbol.as<TypeParameterSymbol>().clone(comp));
                    paramIt++;
                }
            }
        }
    }
}

ModuleInstanceSymbol& ModuleInstanceSymbol::instantiate(Compilation& compilation, string_view name,
                                                        SourceLocation loc,
                                                        const Definition& definition) {
    SmallMap<string_view, const ExpressionSyntax*, 8> unused;
    SmallVectorSized<const ParameterSymbolBase*, 8> parameters;
    createParams(compilation, definition, definition.scope, LookupLocation::max, loc, unused,
                 parameters);

    auto instance =
        compilation.emplace<ModuleInstanceSymbol>(compilation, name, loc, definition, 0u);
    instance->populate(nullptr, parameters);
    return *instance;
}

ModuleInstanceSymbol& ModuleInstanceSymbol::instantiate(
    Compilation& compilation, const HierarchicalInstanceSyntax& syntax,
    const Definition& definition, span<const ParameterSymbolBase* const> parameters,
    uint32_t hierarchyDepth) {

    auto instance = compilation.emplace<ModuleInstanceSymbol>(
        compilation, syntax.name.valueText(), syntax.name.location(), definition, hierarchyDepth);
    instance->populate(&syntax, parameters);
    return *instance;
}

ProgramInstanceSymbol& ProgramInstanceSymbol::instantiate(
    Compilation& compilation, const HierarchicalInstanceSyntax& syntax,
    const Definition& definition, span<const ParameterSymbolBase* const> parameters,
    uint32_t hierarchyDepth) {

    auto instance = compilation.emplace<ProgramInstanceSymbol>(
        compilation, syntax.name.valueText(), syntax.name.location(), definition, hierarchyDepth);

    instance->populate(&syntax, parameters);
    return *instance;
}

InterfaceInstanceSymbol& InterfaceInstanceSymbol::instantiate(
    Compilation& compilation, const HierarchicalInstanceSyntax& syntax,
    const Definition& definition, span<const ParameterSymbolBase* const> parameters,
    uint32_t hierarchyDepth) {

    auto instance = compilation.emplace<InterfaceInstanceSymbol>(
        compilation, syntax.name.valueText(), syntax.name.location(), definition, hierarchyDepth);

    instance->populate(&syntax, parameters);
    return *instance;
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
