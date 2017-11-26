//------------------------------------------------------------------------------
// HierarchySymbols.cpp
// Contains hierarchy-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "util/HashMap.h"

#include "Binder.h"
#include "RootSymbol.h"

namespace slang {

CompilationUnitSymbol::CompilationUnitSymbol(const Scope& parent) :
    Symbol(SymbolKind::CompilationUnit, parent),
    Scope(this)
{
}

PackageSymbol::PackageSymbol(string_view name, const Scope& parent) :
    Symbol(SymbolKind::Package, parent, name),
    Scope(this)
{
}

DefinitionSymbol::DefinitionSymbol(string_view name, const Scope& parent) :
    Symbol(SymbolKind::Module, parent, name),
    Scope(this)
{
}

DefinitionSymbol& DefinitionSymbol::fromSyntax(SymbolFactory& factory, const ModuleDeclarationSyntax& syntax,
                                               const Scope& parent) {
    auto result = factory.emplace<DefinitionSymbol>(syntax.header.name.valueText(), parent);
    SmallVectorSized<const Symbol*, 32> members;

    if (syntax.header.parameters) {
        bool lastLocal = false;
        SmallVectorSized<const ParameterSymbol*, 8> tempParams;
        for (auto declaration : syntax.header.parameters->declarations) {
            // It's legal to leave off the parameter keyword in the parameter port list.
            // If you do so, we "inherit" the parameter or localparam keyword from the previous entry.
            // This isn't allowed in a module body, but the parser will take care of the error for us.
            bool local = false;
            if (!declaration->keyword)
                local = lastLocal;
            else
                local = declaration->keyword.kind == TokenKind::LocalParamKeyword;
            lastLocal = local;

            SmallVectorSized<ParameterSymbol*, 16> params;
            ParameterSymbol::fromSyntax(factory, *declaration, *result, params);

            for (auto param : params) {
                param->isLocalParam = local;
                param->isPortParam = true;
                members.append(param);
                tempParams.append(param);
            }
        }

        // TODO: clean this up

        result->parameters = tempParams.copy(factory);
    }

    for (auto node : syntax.members) {
        // TODO: overrideLocal on body params
        factory.createSymbols(*node, *result, members);
    }

    result->setMembers(members);
    return *result;
}

void DefinitionSymbol::createParamOverrides(const ParameterValueAssignmentSyntax& syntax, ParamOverrideMap& map) const {
    // Build up data structures to easily index the parameter assignments. We need to handle
    // both ordered assignment as well as named assignment, though a specific instance can only
    // use one method or the other.
    bool hasParamAssignments = false;
    bool orderedAssignments = true;
    SmallVectorSized<const OrderedArgumentSyntax*, 8> orderedParams;
    SmallHashMap<string_view, std::pair<const NamedArgumentSyntax*, bool>, 8> namedParams;

    // TODO: the name of the syntax elements here is ridiculous
    for (auto paramBase : syntax.parameters.parameters) {
        bool isOrdered = paramBase->kind == SyntaxKind::OrderedArgument;
        if (!hasParamAssignments) {
            hasParamAssignments = true;
            orderedAssignments = isOrdered;
        }
        else if (isOrdered != orderedAssignments) {
            addError(DiagCode::MixingOrderedAndNamedParams, paramBase->getFirstToken().location());
            break;
        }

        if (isOrdered)
            orderedParams.append(&paramBase->as<OrderedArgumentSyntax>());
        else {
            const NamedArgumentSyntax& nas = paramBase->as<NamedArgumentSyntax>();
            auto pair = namedParams.emplace(nas.name.valueText(), std::make_pair(&nas, false));
            if (!pair.second) {
                addError(DiagCode::DuplicateParamAssignment, nas.name.location()) << nas.name.valueText();
                addError(DiagCode::NotePreviousUsage, pair.first->second.first->name.location());
            }
        }
    }

    // For each parameter assignment we have, match it up to a real parameter
    if (orderedAssignments) {
        uint32_t orderedIndex = 0;
        for (auto param : parameters) {
            if (orderedIndex >= orderedParams.size())
                break;

            if (param->isLocalParam)
                continue;

            map[param] = &orderedParams[orderedIndex++]->expr;
        }

        // Make sure there aren't extra param assignments for non-existent params.
        if (orderedIndex < orderedParams.size()) {
            auto& diag = addError(DiagCode::TooManyParamAssignments, orderedParams[orderedIndex]->getFirstToken().location());
            diag << name;
            diag << orderedParams.size();
            diag << orderedIndex;
        }
    }
    else {
        // Otherwise handle named assignments.
        for (auto param : parameters) {
            auto it = namedParams.find(param->name);
            if (it == namedParams.end())
                continue;

            const NamedArgumentSyntax* arg = it->second.first;
            it->second.second = true;
            if (param->isLocalParam) {
                // Can't assign to localparams, so this is an error.
                addError(param->isPortParam ? DiagCode::AssignedToLocalPortParam : DiagCode::AssignedToLocalBodyParam, arg->name.location());
                addError(DiagCode::NoteDeclarationHere, param->location) << string_view("parameter");
                continue;
            }

            // It's allowed to have no initializer in the assignment; it means to just use the default
            if (!arg->expr)
                continue;

            map[param] = arg->expr;
        }

        for (const auto& pair : namedParams) {
            // We marked all the args that we used, so anything left over is a param assignment
            // for a non-existent parameter.
            if (!pair.second.second) {
                auto& diag = addError(DiagCode::ParameterDoesNotExist, pair.second.first->name.location());
                diag << pair.second.first->name.valueText();
                diag << name;
            }
        }
    }
}

InstanceSymbol::InstanceSymbol(SymbolKind kind, string_view name, const DefinitionSymbol& definition,
                               const Scope& parent) :
    Symbol(kind, parent, name),
    Scope(this),
    definition(definition) {}

void InstanceSymbol::lazyFromSyntax(SymbolFactory& factory, const HierarchyInstantiationSyntax& syntax,
                                    const Scope& parent, SmallVector<const Symbol*>& results) {
    // Definition information (along with parameter overrides) will be shared among all instances.
    auto definition = factory.createLazyDefinition(parent, syntax);

    for (auto instance : syntax.instances) {
        // TODO: handle arrays
        results.append(factory.emplace<LazySyntaxSymbol>(*instance, parent, definition));
    }
}

InstanceSymbol& InstanceSymbol::fromSyntax(SymbolFactory& factory, const HierarchicalInstanceSyntax& syntax,
                                           const LazyDefinition& defInfo, const Scope& parent) {
    const auto& [definition, paramMap] = defInfo.get();

    // TODO: missing module
    ASSERT(definition);

    // TODO: other things besides modules
    auto result = factory.emplace<ModuleInstanceSymbol>(syntax.name.valueText(), *definition, parent);
    
    // Copy all members from the definition
    SmallVectorSized<const Symbol*, 32> members((uint32_t)definition->members().size());
    for (auto member : definition->members()) {
        Symbol& cloned = member->clone(*result);
        members.append(&cloned);

        // If this is a parameter symbol, see if we have a value override for it.
        if (member->kind == SymbolKind::Parameter) {
            auto it = paramMap.find(&member->as<ParameterSymbol>());
            if (it != paramMap.end())
                cloned.as<ParameterSymbol>().value = LazyConstant(result, *it->second);
        }
    }
    result->setMembers(members);
    return *result;
}

ModuleInstanceSymbol::ModuleInstanceSymbol(string_view name, const DefinitionSymbol& definition, const Scope& parent) :
    InstanceSymbol(SymbolKind::ModuleInstance, name, definition, parent) {}

GenerateBlockSymbol::GenerateBlockSymbol(string_view name, const Scope& parent) :
    Symbol(SymbolKind::GenerateBlock, parent, name),
    Scope(this)
{
}

GenerateBlockSymbol* GenerateBlockSymbol::fromSyntax(SymbolFactory& factory, const IfGenerateSyntax& syntax,
                                                     const Scope& parent) {
    // TODO: better error checking
    const auto& cv = parent.evaluateConstant(syntax.condition);
    if (!cv)
        return nullptr;

    // TODO: handle named block
    SmallVectorSized<const Symbol*, 16> members;
    const SVInt& value = cv.integer();
    if ((logic_t)value) {
        auto block = factory.emplace<GenerateBlockSymbol>("", parent);
        factory.createSymbols(syntax.block, *block, members);

        block->setMembers(members);
        return block;
    }
    else if (syntax.elseClause) {
        auto block = factory.emplace<GenerateBlockSymbol>("", parent);
        factory.createSymbols(syntax.elseClause->clause, *block, members);

        block->setMembers(members);
        return block;
    }
    return nullptr;
}

GenerateBlockArraySymbol::GenerateBlockArraySymbol(string_view name, const Scope& parent) :
    Symbol(SymbolKind::GenerateBlockArray, parent, name),
    Scope(this)
{
}

GenerateBlockArraySymbol& GenerateBlockArraySymbol::fromSyntax(SymbolFactory& factory,
                                                               const LoopGenerateSyntax& syntax,
                                                               const Scope& parent) {
    // If the loop initializer has a genvar keyword, we can use it directly. Otherwise
    // we need to do a lookup to make sure we have the actual genvar.
    // TODO: do the actual lookup

    // Initialize the genvar
    auto result = factory.emplace<GenerateBlockArraySymbol>("", parent);
    const auto& initial = parent.evaluateConstant(syntax.initialExpr);
    if (!initial)
        return *result;

    // Fabricate a local variable that will serve as the loop iteration variable.
    DynamicScopeSymbol iterScope(parent);
    VariableSymbol local(syntax.identifier.valueText(), iterScope);
    local.type = factory.getIntType();
    iterScope.addSymbol(local);

    // Bind the stop and iteration expressions so we can reuse them on each iteration.
    Binder binder(iterScope);
    const auto& stopExpr = binder.bindConstantExpression(syntax.stopExpr);
    const auto& iterExpr = binder.bindConstantExpression(syntax.iterationExpr);

    // Create storage for the iteration variable.
    EvalContext context;
    auto genvar = context.createLocal(&local, initial);

    // Generate blocks!
    SmallVectorSized<const Symbol*, 16> arrayEntries;
    for (; stopExpr.evalBool(context); iterExpr.eval(context)) {
        // Spec: each generate block gets their own scope, with an implicit
        // localparam of the same name as the genvar.
        // TODO: scope name
        auto block = factory.emplace<GenerateBlockSymbol>("", parent);

        auto implicitParam = factory.emplace<ParameterSymbol>(syntax.identifier.valueText(), *block);
        implicitParam->value = *genvar;

        SmallVectorSized<const Symbol*, 16> blockMembers;
        blockMembers.append(implicitParam);
        factory.createSymbols(syntax.block, *block, blockMembers);

        block->setMembers(blockMembers);
        arrayEntries.append(block);
    }

    result->setMembers(arrayEntries);
    return *result;
}

}
