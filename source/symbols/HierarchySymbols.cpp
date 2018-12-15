//------------------------------------------------------------------------------
// HierarchySymbols.cpp
// Contains hierarchy-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/HierarchySymbols.h"

#include <nlohmann/json.hpp>

#include "slang/compilation/Compilation.h"
#include "slang/util/StackContainer.h"

namespace slang {

PackageSymbol& PackageSymbol::fromSyntax(Compilation& compilation,
                                         const ModuleDeclarationSyntax& syntax) {
    auto result = compilation.emplace<PackageSymbol>(compilation, syntax.header->name.valueText(),
                                                     syntax.header->name.location());
    for (auto member : syntax.members)
        result->addMembers(*member);

    result->setSyntax(syntax);
    return *result;
}

DefinitionSymbol::DefinitionSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                                   DefinitionKind definitionKind) :
    Symbol(SymbolKind::Definition, name, loc),
    Scope(compilation, this), definitionKind(definitionKind),
    portMap(compilation.allocSymbolMap()) {
}

DefinitionSymbol& DefinitionSymbol::fromSyntax(Compilation& compilation,
                                               const ModuleDeclarationSyntax& syntax) {
    auto result = compilation.emplace<DefinitionSymbol>(
        compilation, syntax.header->name.valueText(), syntax.header->name.location(),
        SemanticFacts::getDefinitionKind(syntax.kind));
    result->setSyntax(syntax);

    SmallVectorSized<const ParameterSymbol*, 8> parameters;
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

            SmallVectorSized<ParameterSymbol*, 8> params;
            ParameterSymbol::fromSyntax(compilation, *declaration, lastLocal, true, params);

            for (auto param : params) {
                parameters.append(param);
                result->addMember(*param);
            }
        }
    }

    if (syntax.header->ports)
        result->addMembers(*syntax.header->ports);

    for (auto member : syntax.members) {
        if (member->kind != SyntaxKind::ParameterDeclarationStatement)
            result->addMembers(*member);
        else {
            auto declaration = member->as<ParameterDeclarationStatementSyntax>().parameter;
            bool isLocal =
                hasPortParams || declaration->keyword.kind == TokenKind::LocalParamKeyword;

            SmallVectorSized<ParameterSymbol*, 8> params;
            ParameterSymbol::fromSyntax(compilation, *declaration, isLocal, false, params);

            for (auto param : params) {
                parameters.append(param);
                result->addMember(*param);
            }
        }
    }

    result->parameters = parameters.copy(compilation);
    return *result;
}

void InstanceSymbol::fromSyntax(Compilation& compilation,
                                const HierarchyInstantiationSyntax& syntax, LookupLocation location,
                                const Scope& scope, SmallVector<const Symbol*>& results) {

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

        for (auto paramBase : syntax.parameters->assignments->parameters) {
            bool isOrdered = paramBase->kind == SyntaxKind::OrderedArgument;
            if (!hasParamAssignments) {
                hasParamAssignments = true;
                orderedAssignments = isOrdered;
            }
            else if (isOrdered != orderedAssignments) {
                scope.addDiag(DiagCode::MixingOrderedAndNamedParams,
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
                            scope.addDiag(DiagCode::DuplicateParamAssignment, nas.name.location());
                        diag << name;
                        diag.addNote(DiagCode::NotePreviousUsage,
                                     pair.first->second.first->name.location());
                    }
                }
            }
        }

        // For each parameter assignment we have, match it up to a real parameter
        if (orderedAssignments) {
            uint32_t orderedIndex = 0;
            for (auto param : definition->parameters) {
                if (orderedIndex >= orderedParams.size())
                    break;

                if (param->isLocalParam())
                    continue;

                paramOverrides.emplace(param->name, orderedParams[orderedIndex++]->expr);
            }

            // Make sure there aren't extra param assignments for non-existent params.
            if (orderedIndex < orderedParams.size()) {
                auto loc = orderedParams[orderedIndex]->getFirstToken().location();
                auto& diag = scope.addDiag(DiagCode::TooManyParamAssignments, loc);
                diag << definition->name;
                diag << orderedParams.size();
                diag << orderedIndex;
            }
        }
        else {
            // Otherwise handle named assignments.
            for (auto param : definition->parameters) {
                auto it = namedParams.find(param->name);
                if (it == namedParams.end())
                    continue;

                const NamedArgumentSyntax* arg = it->second.first;
                it->second.second = true;
                if (param->isLocalParam()) {
                    // Can't assign to localparams, so this is an error.
                    DiagCode code = param->isPortParam() ? DiagCode::AssignedToLocalPortParam
                                                         : DiagCode::AssignedToLocalBodyParam;

                    auto& diag = scope.addDiag(code, arg->name.location());
                    diag.addNote(DiagCode::NoteDeclarationHere, param->location);
                    continue;
                }

                // It's allowed to have no initializer in the assignment; it means to just use the
                // default.
                if (!arg->expr)
                    continue;

                paramOverrides.emplace(param->name, arg->expr);
            }

            for (const auto& pair : namedParams) {
                // We marked all the args that we used, so anything left over is a param assignment
                // for a non-existent parameter.
                if (!pair.second.second) {
                    auto& diag = scope.addDiag(DiagCode::ParameterDoesNotExist,
                                               pair.second.first->name.location());
                    diag << pair.second.first->name.valueText();
                    diag << definition->name;
                }
            }
        }
    }

    // Determine values for all parameters now so that they can be shared between instances.
    SmallVectorSized<const Expression*, 8> overrides;
    for (auto param : definition->parameters) {
        if (auto it = paramOverrides.find(param->name); it != paramOverrides.end()) {
            auto declared = param->getDeclaredType();
            auto typeSyntax = declared->getTypeSyntax();
            ASSERT(typeSyntax);

            auto& expr = DeclaredType::resolveInitializer(
                *typeSyntax, declared->getDimensionSyntax(), *it->second,
                it->second->getFirstToken().location(),
                BindContext(scope, location, BindFlags::Constant),
                DeclaredTypeFlags::InferImplicit);
            overrides.append(&expr);
        }
        else if (!param->getInitializer() && !param->isLocalParam() && param->isPortParam()) {
            auto& diag =
                scope.addDiag(DiagCode::ParamHasNoValue, syntax.getFirstToken().location());
            diag << definition->name;
            diag << param->name;
            overrides.append(nullptr);
        }
        else {
            overrides.append(nullptr);
        }
    }

    for (auto instanceSyntax : syntax.instances) {
        Symbol* inst;
        switch (definition->definitionKind) {
            case DefinitionKind::Module:
                inst = &ModuleInstanceSymbol::instantiate(compilation, *instanceSyntax, *definition,
                                                          overrides);
                break;
            case DefinitionKind::Interface:
                inst = &InterfaceInstanceSymbol::instantiate(compilation, *instanceSyntax,
                                                             *definition, overrides);
                break;
            default:
                THROW_UNREACHABLE;
        }

        // TODO: instance arrays
        inst->setSyntax(*instanceSyntax);
        results.append(inst);
    }
}

InstanceSymbol::InstanceSymbol(SymbolKind kind, Compilation& compilation, string_view name,
                               SourceLocation loc) :
    Symbol(kind, name, loc),
    Scope(compilation, this), portMap(compilation.allocSymbolMap()) {
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

void InstanceSymbol::populate(const DefinitionSymbol& definition,
                              const HierarchicalInstanceSyntax* instanceSyntax,
                              span<const Expression*> parameterOverides) {
    // Add all port parameters as members first.
    Compilation& comp = getCompilation();
    auto paramIt = definition.parameters.begin();
    auto overrideIt = parameterOverides.begin();

    while (paramIt != definition.parameters.end()) {
        auto original = *paramIt;
        if (!original->isPortParam())
            break;

        ASSERT(overrideIt != parameterOverides.end());
        addMember(original->createOverride(comp, *overrideIt));

        paramIt++;
        overrideIt++;
    }

    auto& declSyntax =
        definition.getSyntax()->as<ModuleDeclarationSyntax>(); // TODO: getSyntax dependency
    if (declSyntax.header->ports)
        addMembers(*declSyntax.header->ports);

    if (instanceSyntax)
        setPortConnections(instanceSyntax->connections);

    for (auto member : declSyntax.members) {
        // If this is a parameter declaration, we should already have metadata for it in our
        // parameters list. The list is given in declaration order, so we should be be able to move
        // through them incrementally.
        if (member->kind != SyntaxKind::ParameterDeclarationStatement)
            addMembers(*member);
        else {
            for (auto declarator :
                 member->as<ParameterDeclarationStatementSyntax>().parameter->declarators) {

                ASSERT(paramIt != definition.parameters.end());
                ASSERT(overrideIt != parameterOverides.end());
                ASSERT(declarator->name.valueText() == (*paramIt)->name);

                addMember((*paramIt)->createOverride(comp, *overrideIt));

                paramIt++;
                overrideIt++;
            }
        }
    }
}

ModuleInstanceSymbol& ModuleInstanceSymbol::instantiate(Compilation& compilation, string_view name,
                                                        SourceLocation loc,
                                                        const DefinitionSymbol& definition) {
    SmallVectorSized<const Expression*, 8> overrides;
    for (auto param : definition.parameters) {
        (void)param;
        overrides.emplace(nullptr);
    }

    auto instance = compilation.emplace<ModuleInstanceSymbol>(compilation, name, loc);
    instance->populate(definition, nullptr, overrides);
    return *instance;
}

ModuleInstanceSymbol& ModuleInstanceSymbol::instantiate(
    Compilation& compilation, const HierarchicalInstanceSyntax& syntax,
    const DefinitionSymbol& definition, span<const Expression*> parameterOverrides) {

    auto instance = compilation.emplace<ModuleInstanceSymbol>(compilation, syntax.name.valueText(),
                                                              syntax.name.location());
    instance->populate(definition, &syntax, parameterOverrides);
    return *instance;
}

InterfaceInstanceSymbol& InterfaceInstanceSymbol::instantiate(
    Compilation& compilation, const HierarchicalInstanceSyntax& syntax,
    const DefinitionSymbol& definition, span<const Expression*> parameterOverrides) {

    auto instance = compilation.emplace<InterfaceInstanceSymbol>(
        compilation, syntax.name.valueText(), syntax.name.location());
    instance->populate(definition, &syntax, parameterOverrides);
    return *instance;
}

SequentialBlockSymbol& SequentialBlockSymbol::fromSyntax(Compilation& compilation,
                                                         const BlockStatementSyntax& syntax) {
    auto result = compilation.emplace<SequentialBlockSymbol>(compilation, syntax.begin.location());
    result->setBody(syntax.items);
    result->setSyntax(syntax);
    return *result;
}

ProceduralBlockSymbol& ProceduralBlockSymbol::fromSyntax(Compilation& compilation,
                                                         const ProceduralBlockSyntax& syntax) {
    auto kind = SemanticFacts::getProceduralBlockKind(syntax.kind);
    auto result =
        compilation.emplace<ProceduralBlockSymbol>(compilation, syntax.keyword.location(), kind);
    result->setBody(*syntax.statement);
    result->setSyntax(syntax);
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
    // (for no good reason) so check both locations. The parser has already checked for
    // inconsistencies here.
    const GenerateBlockSyntax& block = node.as<GenerateBlockSyntax>();
    if (block.label)
        return block.label->name.valueText();

    if (block.beginName)
        return block.beginName->name.valueText();

    return "";
}

void GenerateBlockSymbol::fromSyntax(Compilation& compilation, const IfGenerateSyntax& syntax,
                                     LookupLocation location, const Scope& parent,
                                     uint32_t constructIndex, bool isInstantiated,
                                     SmallVector<GenerateBlockSymbol*>& results) {
    optional<bool> selector;
    if (isInstantiated) {
        // TODO: better error checking
        BindContext bindContext(parent, location, BindFlags::Constant);
        const auto& cond = Expression::bind(*syntax.condition, bindContext);
        if (cond.constant)
            selector = (bool)(logic_t)cond.constant->integer();
    }

    auto createBlock = [&](const SyntaxNode& syntax, bool isInstantiated) {
        // [27.5] If a generate block in a conditional generate construct consists of only one item
        // that is itself a conditional generate construct and if that item is not surrounded by
        // begin-end keywords, then this generate block is not treated as a separate scope. The
        // generate construct within this block is said to be directly nested. The generate blocks
        // of the directly nested construct are treated as if they belong to the outer construct.
        switch (syntax.kind) {
            case SyntaxKind::IfGenerate:
                fromSyntax(compilation, syntax.as<IfGenerateSyntax>(), location, parent,
                           constructIndex, isInstantiated, results);
                return;

            case SyntaxKind::CaseGenerate: // TODO:
            default:
                break;
        }

        string_view name = getGenerateBlockName(syntax);
        SourceLocation loc = syntax.getFirstToken().location();

        auto block = compilation.emplace<GenerateBlockSymbol>(compilation, name, loc,
                                                              constructIndex, isInstantiated);

        block->addMembers(syntax);
        block->setSyntax(syntax);
        results.append(block);
    };

    createBlock(*syntax.block, selector.has_value() && selector.value());
    if (syntax.elseClause)
        createBlock(*syntax.elseClause->clause, selector.has_value() && !selector.value());
}

GenerateBlockArraySymbol& GenerateBlockArraySymbol::fromSyntax(
    Compilation& compilation, const LoopGenerateSyntax& syntax, Index scopeIndex,
    LookupLocation location, const Scope& parent, uint32_t constructIndex) {

    // If the loop initializer has a genvar keyword, we can use it directly. Otherwise
    // we need to do a lookup to make sure we have the actual genvar.
    // TODO: do the actual lookup

    string_view name = getGenerateBlockName(*syntax.block);
    SourceLocation loc = syntax.block->getFirstToken().location();
    auto result =
        compilation.emplace<GenerateBlockArraySymbol>(compilation, name, loc, constructIndex);
    result->setSyntax(syntax);

    // TODO: verify that localparam type should be int

    auto createBlock = [&](ConstantValue value, bool isInstantiated) {
        // Spec: each generate block gets their own scope, with an implicit
        // localparam of the same name as the genvar.
        // TODO: block name, location?
        auto block = compilation.emplace<GenerateBlockSymbol>(compilation, "", SourceLocation(),
                                                              isInstantiated, 1);
        auto implicitParam = compilation.emplace<ParameterSymbol>(
            syntax.identifier.valueText(), syntax.identifier.location(), true /* isLocal */,
            false /* isPort */);

        block->addMember(*implicitParam);
        block->addMembers(*syntax.block);
        result->addMember(*block);

        implicitParam->setType(compilation.getIntType());
        implicitParam->setValue(std::move(value));
    };

    // Initialize the genvar
    BindContext bindContext(parent, location, BindFlags::Constant);
    const auto& initial = Expression::bind(*syntax.initialExpr, bindContext);
    if (!initial.constant) {
        createBlock(SVInt(32, 0, true), false);
        return *result;
    }

    // Fabricate a local variable that will serve as the loop iteration variable.
    SequentialBlockSymbol iterScope(compilation, SourceLocation());
    VariableSymbol local{ syntax.identifier.valueText(), syntax.identifier.location() };
    local.setType(compilation.getIntType());

    iterScope.setTemporaryParent(parent, scopeIndex);
    iterScope.addMember(local);

    // Bind the stop and iteration expressions so we can reuse them on each iteration.
    const auto& stopExpr =
        Expression::bind(*syntax.stopExpr, BindContext(iterScope, LookupLocation::max));
    const auto& iterExpr =
        Expression::bind(*syntax.iterationExpr, BindContext(iterScope, LookupLocation::max));

    // Create storage for the iteration variable.
    EvalContext context;
    auto genvar = context.createLocal(&local, *initial.constant);

    // Generate blocks!
    bool any = false;
    for (; stopExpr.evalBool(context); iterExpr.eval(context)) {
        createBlock(*genvar, true);
        any = true;
    }

    if (!any)
        createBlock(SVInt(32, 0, true), false);

    return *result;
}

} // namespace slang
