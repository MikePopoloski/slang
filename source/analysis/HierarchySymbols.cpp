//------------------------------------------------------------------------------
// HierarchySymbols.cpp
// Contains hierarchy-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "Binder.h"
#include "RootSymbol.h"

namespace slang {

CompilationUnitSymbol::CompilationUnitSymbol(const ScopeSymbol& parent) :
    ScopeSymbol(SymbolKind::CompilationUnit, parent)
{
}

PackageSymbol::PackageSymbol(string_view name, const ScopeSymbol& parent) :
    ScopeSymbol(SymbolKind::Package, parent, name)
{
}

DefinitionSymbol::DefinitionSymbol(string_view name, const ModuleDeclarationSyntax& syntax, const ScopeSymbol& parent) :
    ScopeSymbol(SymbolKind::Module, parent, name),
    syntax(&syntax)
{
    isLazy = true;
}

void DefinitionSymbol::resolveMembers() const {
    SmallVectorSized<const Symbol*, 32> members;

    SymbolFactory& factory = getFactory();
    if (syntax->header.parameters) {
        bool lastLocal = false;
        SmallVectorSized<const ParameterSymbol*, 8> tempParams;
        for (auto declaration : syntax->header.parameters->declarations) {
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
            ParameterSymbol::fromSyntax(factory, *declaration, *this, params);

            for (auto param : params) {
                param->isLocalParam = local;
                param->isPortParam = true;
                members.append(param);
                tempParams.append(param);
            }
        }

        // TODO: clean this up

        parameters = tempParams.copy(factory.alloc);
    }

    for (auto node : syntax->members) {
        // TODO: overrideLocal on body params
        factory.createSymbols(*node, *this, members);
    }

    setMembers(members);
}

InstanceSymbol::InstanceSymbol(SymbolKind kind, string_view name, const DefinitionSymbol& definition,
                               const ScopeSymbol& parent) :
    ScopeSymbol(kind, parent, name),
    definition(definition) {}

void InstanceSymbol::fromSyntax(const ScopeSymbol& parent, const HierarchyInstantiationSyntax& syntax,
                                SmallVector<const Symbol*>& results) {
    // TODO: module namespacing
    Token typeName = syntax.type;
    auto foundSymbol = parent.lookup(typeName.valueText(), typeName.location(), LookupKind::Definition);
    if (!foundSymbol)
        return;

    // TODO: check symbol kind?
    const DefinitionSymbol& definition = foundSymbol->as<DefinitionSymbol>();
    definition.members();
    const RootSymbol& root = parent.getRoot();

    // Evaluate all parameters now so that we can reuse them for all instances below.
    // If we were given a set of parameter assignments, build up some data structures to
    // allow us to easily index them. We need to handle both ordered assignment as well as
    // named assignment (though a specific instance can only use one method or the other).
    SmallHashMap<const ParameterSymbol*, const ExpressionSyntax*, 8> paramMap;
    if (syntax.parameters) {
        bool hasParamAssignments = false;
        bool orderedAssignments = true;
        SmallVectorSized<const OrderedArgumentSyntax*, 8> orderedParams;
        SmallHashMap<string_view, std::pair<const NamedArgumentSyntax*, bool>, 8> namedParams;

        // TODO: the name of the syntax elements here is ridiculous
        for (auto paramBase : syntax.parameters->parameters.parameters) {
            bool isOrdered = paramBase->kind == SyntaxKind::OrderedArgument;
            if (!hasParamAssignments) {
                hasParamAssignments = true;
                orderedAssignments = isOrdered;
            }
            else if (isOrdered != orderedAssignments) {
                root.addError(DiagCode::MixingOrderedAndNamedParams, paramBase->getFirstToken().location());
                break;
            }

            if (isOrdered)
                orderedParams.append(&paramBase->as<OrderedArgumentSyntax>());
            else {
                const NamedArgumentSyntax& nas = paramBase->as<NamedArgumentSyntax>();
                auto pair = namedParams.emplace(nas.name.valueText(), std::make_pair(&nas, false));
                if (!pair.second) {
                    root.addError(DiagCode::DuplicateParamAssignment, nas.name.location()) << nas.name.valueText();
                    root.addError(DiagCode::NotePreviousUsage, pair.first->second.first->name.location());
                }
            }
        }

        // For each parameter assignment we have, match it up to a real parameter
        if (orderedAssignments) {
            uint32_t orderedIndex = 0;
            for (auto param : definition.parameters) {
                if (orderedIndex >= orderedParams.size())
                    break;

                if (param->isLocalParam)
                    continue;

                paramMap[param] = &orderedParams[orderedIndex++]->expr;
            }

            // Make sure there aren't extra param assignments for non-existent params.
            if (orderedIndex < orderedParams.size()) {
                auto& diag = root.addError(DiagCode::TooManyParamAssignments, orderedParams[orderedIndex]->getFirstToken().location());
                diag << definition.name;
                diag << orderedParams.size();
                diag << orderedIndex;
            }
        }
        else {
            // Otherwise handle named assignments.
            for (auto param : definition.parameters) {
                auto it = namedParams.find(param->name);
                if (it == namedParams.end())
                    continue;

                const NamedArgumentSyntax* arg = it->second.first;
                it->second.second = true;
                if (param->isLocalParam) {
                    // Can't assign to localparams, so this is an error.
                    root.addError(param->isPortParam ? DiagCode::AssignedToLocalPortParam : DiagCode::AssignedToLocalBodyParam, arg->name.location());
                    root.addError(DiagCode::NoteDeclarationHere, param->location) << string_view("parameter");
                    continue;
                }

                // It's allowed to have no initializer in the assignment; it means to just use the default
                if (!arg->expr)
                    continue;

                paramMap[param] = arg->expr;
            }

            for (const auto& pair : namedParams) {
                // We marked all the args that we used, so anything left over is a param assignment
                // for a non-existent parameter.
                if (!pair.second.second) {
                    auto& diag = root.addError(DiagCode::ParameterDoesNotExist, pair.second.first->name.location());
                    diag << pair.second.first->name.valueText();
                    diag << definition.name;
                }
            }
        }
    }

    for (auto instance : syntax.instances) {
        // TODO: handle arrays
        auto symbol = &root.allocate<ModuleInstanceSymbol>(instance->name.valueText(), definition, parent);
        results.append(symbol);

        // Copy all members from the definition
        SmallVectorSized<const Symbol*, 32> members((uint32_t)definition.members().size());
        for (auto member : definition.members()) {
            Symbol& cloned = member->clone(*symbol);
            members.append(&cloned);

            // If this is a parameter symbol, see if we have a value override for it.
            if (member->kind == SymbolKind::Parameter) {
                auto it = paramMap.find(&member->as<ParameterSymbol>());
                if (it != paramMap.end())
                    cloned.as<ParameterSymbol>().value = LazyConstant(symbol, *it->second);
            }
        }
        symbol->setMembers(members);
    }
}

ModuleInstanceSymbol::ModuleInstanceSymbol(string_view name, const DefinitionSymbol& definition, const ScopeSymbol& parent) :
    InstanceSymbol(SymbolKind::ModuleInstance, name, definition, parent) {}

IfGenerateSymbol::IfGenerateSymbol(const IfGenerateSyntax& syntax, const ScopeSymbol& parent) :
    ScopeSymbol(SymbolKind::IfGenerate, parent),
    syntax(syntax) {}

void IfGenerateSymbol::fillMembers(MemberBuilder& builder) const {
    // TODO: better error checking
    const auto& cv = getParent()->evaluateConstant(syntax.condition);
    if (!cv)
        return;

    const SVInt& value = cv.integer();
    if ((logic_t)value)
        builder.add(getRoot().allocate<GenerateBlockSymbol>("", SourceLocation(), syntax.block, *this));
    else if (syntax.elseClause)
        builder.add(getRoot().allocate<GenerateBlockSymbol>("", SourceLocation(), syntax.elseClause->clause, *this));
}

LoopGenerateSymbol::LoopGenerateSymbol(const LoopGenerateSyntax& syntax, const ScopeSymbol& parent) :
    ScopeSymbol(SymbolKind::LoopGenerate, parent),
    syntax(syntax) {}

void LoopGenerateSymbol::fillMembers(MemberBuilder& builder) const {
    // If the loop initializer has a genvar keyword, we can use it directly. Otherwise
    // we need to do a lookup to make sure we have the actual genvar.
    // TODO: do the actual lookup

    // Initialize the genvar
    const ScopeSymbol& parent = *getParent();
    const auto& initial = parent.evaluateConstant(syntax.initialExpr);
    if (!initial)
        return;

    // Fabricate a local variable that will serve as the loop iteration variable.
    const RootSymbol& root = parent.getRoot();
    DynamicScopeSymbol iterScope(parent);
    VariableSymbol local(syntax.identifier.valueText(), iterScope);
    local.type = root.factory.getIntType();
    iterScope.addSymbol(local);

    // Bind the stop and iteration expressions so we can reuse them on each iteration.
    Binder binder(iterScope);
    const auto& stopExpr = binder.bindConstantExpression(syntax.stopExpr);
    const auto& iterExpr = binder.bindConstantExpression(syntax.iterationExpr);

    // Create storage for the iteration variable.
    EvalContext context;
    auto genvar = context.createLocal(&local, initial);

    // Generate blocks!
    for (; stopExpr.evalBool(context); iterExpr.eval(context)) {
        // Spec: each generate block gets their own scope, with an implicit
        // localparam of the same name as the genvar.
        // TODO: scope name

        auto& implicitParam = root.allocate<ParameterSymbol>(syntax.identifier.valueText(), *this);
        implicitParam.value = *genvar;

        builder.add(root.allocate<GenerateBlockSymbol>("", SourceLocation(),
                                                       syntax.block, implicitParam, parent));
    }
}

GenerateBlockSymbol::GenerateBlockSymbol(string_view name, SourceLocation location, const SyntaxNode& body,
                                         const ScopeSymbol& parent) :
    ScopeSymbol(SymbolKind::GenerateBlock, parent, name, location),
    body(body) {}

GenerateBlockSymbol::GenerateBlockSymbol(string_view name, SourceLocation location, const SyntaxNode& body,
                                         const ParameterSymbol& implicitParam, const ScopeSymbol& parent) :
    ScopeSymbol(SymbolKind::GenerateBlock, parent, name, location),
    body(body), implicitParam(&implicitParam) {}

void GenerateBlockSymbol::fillMembers(MemberBuilder& builder) const {
    if (implicitParam)
        builder.add(*implicitParam);

    if (body.kind == SyntaxKind::GenerateBlock) {
        for (auto member : body.as<GenerateBlockSyntax>().members)
            builder.add(*member, *this);
    }
    else {
        builder.add(body, *this);
    }
}

}
