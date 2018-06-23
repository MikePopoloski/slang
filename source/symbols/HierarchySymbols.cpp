//------------------------------------------------------------------------------
// HierarchySymbols.cpp
// Contains hierarchy-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "HierarchySymbols.h"

#include "json.hpp"

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
    auto paramIt = parameters.begin();
    while (paramIt != parameters.end()) {
        auto decl = paramIt->decl;
        if (!decl->isPort)
            break;

        auto& param = ParameterSymbol::fromDecl(getCompilation(), *decl);
        addMember(param);

        if (paramIt->type) {
            param.setType(*paramIt->type);
            param.setValue(paramIt->value);
        }
        paramIt++;
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
                auto& param = ParameterSymbol::fromDecl(getCompilation(), *decl);
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
    auto result = compilation.emplace<GenerateBlockArraySymbol>(compilation, "", SourceLocation());

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
