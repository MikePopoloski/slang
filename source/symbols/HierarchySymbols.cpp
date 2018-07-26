//------------------------------------------------------------------------------
// HierarchySymbols.cpp
// Contains hierarchy-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "HierarchySymbols.h"

#include <nlohmann/json.hpp>

#include "compilation/Compilation.h"
#include "util/StackContainer.h"

namespace slang {

PackageSymbol& PackageSymbol::fromSyntax(Compilation& compilation, const ModuleDeclarationSyntax& syntax) {
    auto result = compilation.emplace<PackageSymbol>(compilation, syntax.header.name.valueText(),
                                                     syntax.header.name.location());
    for (auto member : syntax.members)
        result->addMembers(*member);
    return *result;
}

void InstanceSymbol::fromSyntax(Compilation& compilation, const HierarchyInstantiationSyntax& syntax,
                                LookupLocation location, const Scope& scope, SmallVector<const Symbol*>& results) {

    auto definition = compilation.getDefinition(syntax.type.valueText(), scope);
    if (!definition) {
        // TODO: error
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

        // TODO: syntax node names here are dumb
        for (auto paramBase : syntax.parameters->parameters.parameters) {
            bool isOrdered = paramBase->kind == SyntaxKind::OrderedArgument;
            if (!hasParamAssignments) {
                hasParamAssignments = true;
                orderedAssignments = isOrdered;
            }
            else if (isOrdered != orderedAssignments) {
                compilation.addError(DiagCode::MixingOrderedAndNamedParams, paramBase->getFirstToken().location());
                break;
            }

            if (isOrdered)
                orderedParams.append(&paramBase->as<OrderedArgumentSyntax>());
            else {
                const NamedArgumentSyntax& nas = paramBase->as<NamedArgumentSyntax>();
                auto pair = namedParams.emplace(nas.name.valueText(), std::make_pair(&nas, false));
                if (!pair.second) {
                    auto& diag = compilation.addError(DiagCode::DuplicateParamAssignment, nas.name.location());
                    diag << nas.name.valueText();
                    diag.addNote(DiagCode::NotePreviousUsage, pair.first->second.first->name.location());
                }
            }
        }

        // For each parameter assignment we have, match it up to a real parameter
        if (orderedAssignments) {
            uint32_t orderedIndex = 0;
            for (auto param : definition->parameters) {
                if (orderedIndex >= orderedParams.size())
                    break;

                if (param.isLocal)
                    continue;

                paramOverrides.emplace(param.name, &orderedParams[orderedIndex++]->expr);
            }

            // Make sure there aren't extra param assignments for non-existent params.
            if (orderedIndex < orderedParams.size()) {
                auto loc = orderedParams[orderedIndex]->getFirstToken().location();
                auto& diag = compilation.addError(DiagCode::TooManyParamAssignments, loc);
                diag << definition->name;
                diag << orderedParams.size();
                diag << orderedIndex;
            }
        }
        else {
            // Otherwise handle named assignments.
            for (auto param : definition->parameters) {
                auto it = namedParams.find(param.name);
                if (it == namedParams.end())
                    continue;

                const NamedArgumentSyntax* arg = it->second.first;
                it->second.second = true;
                if (param.isLocal) {
                    // Can't assign to localparams, so this is an error.
                    DiagCode code = param.isPort ? DiagCode::AssignedToLocalPortParam : DiagCode::AssignedToLocalBodyParam;
                    auto& diag = compilation.addError(code, arg->name.location());
                    diag.addNote(DiagCode::NoteDeclarationHere, param.location);
                    continue;
                }

                // It's allowed to have no initializer in the assignment; it means to just use the default
                if (!arg->expr)
                    continue;

                paramOverrides.emplace(param.name, arg->expr);
            }

            for (const auto& pair : namedParams) {
                // We marked all the args that we used, so anything left over is a param assignment
                // for a non-existent parameter.
                if (!pair.second.second) {
                    auto& diag = compilation.addError(DiagCode::ParameterDoesNotExist, pair.second.first->name.location());
                    diag << pair.second.first->name.valueText();
                    diag << definition->name;
                }
            }
        }
    }

    // Determine values for all parameters now so that they can be shared between instances.
    SmallVectorSized<ParameterMetadata, 8> params;
    for (const auto& decl : definition->parameters) {
        std::tuple<const Type*, ConstantValue> typeAndValue(nullptr, nullptr);
        if (auto it = paramOverrides.find(decl.name); it != paramOverrides.end())
            typeAndValue = ParameterSymbol::evaluate(*decl.type, *it->second, location, scope);
        else if (!decl.initializer && !decl.isLocal && decl.isPort) {
            auto& diag = compilation.addError(DiagCode::ParamHasNoValue, syntax.getFirstToken().location());
            diag << definition->name;
            diag << decl.name;
        }

        params.emplace(ParameterMetadata { &decl, std::get<0>(typeAndValue), std::move(std::get<1>(typeAndValue)) });
    }

    for (auto instanceSyntax : syntax.instances) {
        const Symbol* inst;
        switch (definition->syntax.kind) {
            case SyntaxKind::ModuleDeclaration:
                inst = &ModuleInstanceSymbol::instantiate(compilation, instanceSyntax->name.valueText(),
                                                          instanceSyntax->name.location(), *definition, params);
                break;
            case SyntaxKind::InterfaceDeclaration:
                inst = &InterfaceInstanceSymbol::instantiate(compilation, instanceSyntax->name.valueText(),
                                                             instanceSyntax->name.location(), *definition, params);
                break;
            default:
                THROW_UNREACHABLE;
        }

        // TODO: instance arrays
        results.append(inst);
    }
}

bool InstanceSymbol::isKind(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::ModuleInstance:
        case SymbolKind::InterfaceInstance:
        case SymbolKind::Program:
            return true;
        default:
            return false;
    }
}

void InstanceSymbol::populate(const Definition& definition, span<const ParameterMetadata> parameters) {
    // Add all port parameters as members first.
    Compilation& comp = getCompilation();
    auto paramIt = parameters.begin();
    while (paramIt != parameters.end()) {
        auto decl = paramIt->decl;
        if (!decl->isPort)
            break;

        auto& param = ParameterSymbol::fromDecl(comp, *decl);
        addMember(param);

        if (paramIt->type) {
            param.setType(*paramIt->type);
            param.setValue(paramIt->value);
        }
        paramIt++;
    }

    const PortListSyntax* portSyntax = definition.syntax.header.ports;
    if (portSyntax) {
        switch (portSyntax->kind) {
            case SyntaxKind::AnsiPortList:
                handleAnsiPorts(portSyntax->as<AnsiPortListSyntax>());
                break;
            case SyntaxKind::NonAnsiPortList:
                handleNonAnsiPorts(portSyntax->as<NonAnsiPortListSyntax>());
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    for (auto member : definition.syntax.members) {
        // If this is a parameter declaration, we should already have metadata for it in our parameters list.
        // The list is given in declaration order, so we should be be able to move through them incrementally.
        if (member->kind != SyntaxKind::ParameterDeclarationStatement)
            addMembers(*member);
        else {
            for (auto declarator : member->as<ParameterDeclarationStatementSyntax>().parameter.declarators) {
                (void)declarator;
                ASSERT(paramIt != parameters.end());

                auto decl = paramIt->decl;
                auto& param = ParameterSymbol::fromDecl(comp, *decl);
                if (paramIt->type) {
                    param.setType(*paramIt->type);
                    param.setValue(paramIt->value);
                }
                addMember(param);
                paramIt++;
            }
        }
    }
}

void InstanceSymbol::handleAnsiPorts(const AnsiPortListSyntax& syntax) {
    Compilation& comp = getCompilation();

    PortListBuilder builder{comp};
    for (const MemberSyntax* port : syntax.ports) {
        switch (port->kind) {
            case SyntaxKind::ImplicitAnsiPort: {
                handleImplicitAnsiPort(port->as<ImplicitAnsiPortSyntax>(), builder);
                break;
            }
            default:
                // TODO:
                THROW_UNREACHABLE;
        }
    }

    ports = builder.ports.copy(getCompilation());
}

void InstanceSymbol::handleImplicitAnsiPort(const ImplicitAnsiPortSyntax& syntax, PortListBuilder& builder) {
    Compilation& comp = getCompilation();

    Port port;
    port.name = syntax.declarator.name.valueText();

    // Helper function to check if an implicit type syntax is totally empty.
    auto typeSyntaxEmpty = [](const DataTypeSyntax& typeSyntax) {
        if (typeSyntax.kind != SyntaxKind::ImplicitType)
            return false;

        const auto& implicitType = typeSyntax.as<ImplicitTypeSyntax>();
        return !implicitType.signing && implicitType.dimensions.count() == 0;
    };

    // Helper function to set the port's direction and data type, which are both optional.
    auto setDirectionAndType = [&](const auto& header) {
        if (!header.direction)
            port.direction = builder.lastDirection;
        else
            port.direction = SemanticFacts::getPortDirection(header.direction.kind);

        if (typeSyntaxEmpty(header.dataType))
            port.type = &comp.getLogicType();
        else {
            // We always add ports in syntactical order, so it's fine to just
            // always do a lookup from the "end" of the instance. No other members have been added yet.
            port.type = &comp.getType(header.dataType, LookupLocation::max, *this);
        }
    };

    switch (syntax.header.kind) {
        case SyntaxKind::VariablePortHeader: {
            const auto& header = syntax.header.as<VariablePortHeaderSyntax>();
            if (!header.direction && !header.varKeyword && typeSyntaxEmpty(header.dataType)) {
                // If all three are omitted, take all from the previous port.
                // TODO: default nettype?
                port.kind = builder.lastKind;
                port.direction = builder.lastDirection;
                port.type = builder.lastType;
            }
            else {
                setDirectionAndType(header);

                if (header.varKeyword)
                    port.kind = PortKind::Variable;
                else {
                    // Rules from [23.2.2.3]:
                    // - For input and inout, default to a net
                    // - For output, if we have a data type it's a var, otherwise net
                    // - For ref it's always a var
                    switch (port.direction) {
                        case PortDirection::In:
                        case PortDirection::InOut:
                            // TODO: default nettype
                            port.kind = PortKind::Net;
                            break;
                        case PortDirection::Out:
                            if (header.dataType.kind == SyntaxKind::ImplicitType)
                                port.kind = PortKind::Net;
                            else
                                port.kind = PortKind::Variable;
                            break;
                        case PortDirection::Ref:
                            port.kind = PortKind::Variable;
                            break;
                        case PortDirection::NotApplicable:
                            THROW_UNREACHABLE;
                    }
                }
            }

            // Unpacked dimensions are not inherited, so make sure not to set port.type with them.
            const Type* finalType = &comp.getType(*port.type, syntax.declarator.dimensions,
                                                  LookupLocation::max, *this);

            // Create a new symbol to represent this port internally to the instance.
            // TODO: interconnect ports don't have a datatype
            // TODO: variable lifetime
            auto variable = comp.emplace<VariableSymbol>(port.name, syntax.declarator.name.location());
            port.symbol = variable;
            variable->type = finalType;
            addMember(*variable);

            // Initializers here are evaluated in the context of the port list and must always be a constant value.
            // TODO: handle initializers

            break;
        }
        case SyntaxKind::NetPortHeader: {
            const auto& header = syntax.header.as<NetPortHeaderSyntax>();
            port.kind = PortKind::Net;
            setDirectionAndType(header);

            // Unpacked dimensions are not inherited, so make sure not to set port.type with them.
            const Type* finalType = &comp.getType(*port.type, syntax.declarator.dimensions,
                                                  LookupLocation::max, *this);

            // Create a new symbol to represent this port internally to the instance.
            // TODO: net type
            auto net = comp.emplace<NetSymbol>(port.name, syntax.declarator.name.location());
            port.symbol = net;
            net->dataType = finalType;
            addMember(*net);

            break;
        }
        default:
            // TODO:
            THROW_UNREACHABLE;
    }

    builder.add(port);
}

void InstanceSymbol::handleNonAnsiPorts(const NonAnsiPortListSyntax&) {
    // TODO: implement
}

InstanceSymbol::PortListBuilder::PortListBuilder(Compilation& compilation) :
    compilation(compilation),
    lastKind(PortKind::Net),
    lastDirection(PortDirection::InOut),
    lastType(&compilation.getLogicType())
{
}

void InstanceSymbol::PortListBuilder::add(const Port& port) {
    ports.append(port);

    lastKind = port.kind;
    lastDirection = port.direction;
    lastType = port.type;

    if (lastDirection == PortDirection::NotApplicable)
        lastDirection = PortDirection::InOut;

    if (lastKind == PortKind::Explicit || lastKind == PortKind::Interface) {
        switch (lastDirection) {
            case PortDirection::In:
            case PortDirection::InOut:
            case PortDirection::Out:
                // TODO: default nettype
                lastKind = PortKind::Net;
                break;
            case PortDirection::Ref:
                lastKind = PortKind::Variable;
                break;
            case PortDirection::NotApplicable:
                THROW_UNREACHABLE;
        }
    }

    if (lastKind != PortKind::Interconnect && !lastType)
        lastType = &compilation.getLogicType();
}

ModuleInstanceSymbol& ModuleInstanceSymbol::instantiate(Compilation& compilation, string_view name,
                                                        SourceLocation loc, const Definition& definition) {
    SmallVectorSized<ParameterMetadata, 8> params;
    for (const auto& decl : definition.parameters) {
        // This function should only be called for definitions where all parameters have defaults.
        ASSERT(decl.initializer);
        params.emplace(ParameterMetadata { &decl, nullptr, nullptr });
    }

    return instantiate(compilation, name, loc, definition, params);
}

ModuleInstanceSymbol& ModuleInstanceSymbol::instantiate(Compilation& compilation, string_view name,
                                                        SourceLocation loc, const Definition& definition,
                                                        span<const ParameterMetadata> parameters) {

    auto instance = compilation.emplace<ModuleInstanceSymbol>(compilation, name, loc);
    instance->populate(definition, parameters);
    return *instance;
}

InterfaceInstanceSymbol& InterfaceInstanceSymbol::instantiate(Compilation& compilation, string_view name,
                                                              SourceLocation loc, const Definition& definition,
                                                              span<const ParameterMetadata> parameters) {

    auto instance = compilation.emplace<InterfaceInstanceSymbol>(compilation, name, loc);
    instance->populate(definition, parameters);
    return *instance;
}

SequentialBlockSymbol& SequentialBlockSymbol::fromSyntax(Compilation& compilation,
                                                         const BlockStatementSyntax& syntax) {
    auto result = compilation.emplace<SequentialBlockSymbol>(compilation, syntax.begin.location());
    result->setBody(syntax.items);
    return *result;
}

ProceduralBlockSymbol& ProceduralBlockSymbol::fromSyntax(Compilation& compilation,
                                                         const ProceduralBlockSyntax& syntax) {
    auto kind = SemanticFacts::getProceduralBlockKind(syntax.kind);
    auto result = compilation.emplace<ProceduralBlockSymbol>(compilation,
                                                             syntax.keyword.location(),
                                                             kind);
    result->setBody(syntax.statement);
    return *result;
}

void ProceduralBlockSymbol::toJson(json& j) const {
    // TODO: stringify
    j["procedureKind"] = procedureKind;
}

static string_view getGenerateBlockName(const SyntaxNode& node) {
    if (node.kind != SyntaxKind::GenerateBlock)
        return "";

    // Try to find a name for this block. Generate blocks allow the name to be specified twice
    // (for no good reason) so check both locations. The parser has already checked for inconsistencies here.
    const GenerateBlockSyntax& block = node.as<GenerateBlockSyntax>();
    if (block.label)
        return block.label->name.valueText();

    if (block.beginName)
        return block.beginName->name.valueText();

    return "";
}

GenerateBlockSymbol* GenerateBlockSymbol::fromSyntax(Compilation& compilation, const IfGenerateSyntax& syntax,
                                                     LookupLocation location, const Scope& parent) {
    // TODO: better error checking
    BindContext bindContext(parent, location, BindFlags::Constant);
    const auto& cond = Expression::bind(compilation, syntax.condition, bindContext);
    if (!cond.constant)
        return nullptr;

    const SVInt& value = cond.constant->integer();

    const SyntaxNode* memberSyntax = nullptr;
    if ((logic_t)value)
        memberSyntax = &syntax.block;
    else if (syntax.elseClause)
        memberSyntax = &syntax.elseClause->clause;
    else
        return nullptr;

    string_view name = getGenerateBlockName(*memberSyntax);
    SourceLocation loc = memberSyntax->getFirstToken().location();
    
    auto block = compilation.emplace<GenerateBlockSymbol>(compilation, name, loc);
    block->addMembers(*memberSyntax);
    return block;
}

GenerateBlockArraySymbol& GenerateBlockArraySymbol::fromSyntax(Compilation& compilation,
                                                               const LoopGenerateSyntax& syntax,
                                                               LookupLocation location,
                                                               const Scope& parent) {
    // If the loop initializer has a genvar keyword, we can use it directly. Otherwise
    // we need to do a lookup to make sure we have the actual genvar.
    // TODO: do the actual lookup

    string_view name = getGenerateBlockName(syntax.block);
    SourceLocation loc = syntax.block.getFirstToken().location();
    auto result = compilation.emplace<GenerateBlockArraySymbol>(compilation, name, loc);

    // Initialize the genvar
    BindContext bindContext(parent, location, BindFlags::Constant);
    const auto& initial = Expression::bind(compilation, syntax.initialExpr, bindContext);
    if (!initial.constant)
        return *result;

    // Fabricate a local variable that will serve as the loop iteration variable.
    SequentialBlockSymbol iterScope(compilation, SourceLocation());
    VariableSymbol local { syntax.identifier.valueText(), syntax.identifier.location() };
    local.type = compilation.getIntType();
    iterScope.addMember(local);

    // Bind the stop and iteration expressions so we can reuse them on each iteration.
    const auto& stopExpr = Expression::bind(compilation, syntax.stopExpr, BindContext(iterScope, LookupLocation::max));
    const auto& iterExpr = Expression::bind(compilation, syntax.iterationExpr, BindContext(iterScope, LookupLocation::max));

    // Create storage for the iteration variable.
    EvalContext context;
    auto genvar = context.createLocal(&local, *initial.constant);

    // Generate blocks!
    SmallVectorSized<const Symbol*, 16> arrayEntries;
    for (; stopExpr.evalBool(context); iterExpr.eval(context)) {
        // Spec: each generate block gets their own scope, with an implicit
        // localparam of the same name as the genvar.
        // TODO: scope name
        auto block = compilation.emplace<GenerateBlockSymbol>(compilation, "", SourceLocation());
        auto implicitParam = compilation.emplace<ParameterSymbol>(syntax.identifier.valueText(),
                                                                  syntax.identifier.location(),
                                                                  true /* isLocal */,
                                                                  false /* isPort */);
        block->addMember(*implicitParam);
        block->addMembers(syntax.block);
        result->addMember(*block);

        implicitParam->setType(*local.type);
        implicitParam->setValue(*genvar);
    }

    return *result;
}

}
