//------------------------------------------------------------------------------
// HierarchySymbols.cpp
// Contains hierarchy-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "Binder.h"

namespace slang {

CompilationUnitSymbol::CompilationUnitSymbol(const SyntaxNode& rootNode, const Symbol& parent) :
    ScopeSymbol(SymbolKind::CompilationUnit, parent),
    rootNode(rootNode)
{
}

void CompilationUnitSymbol::fillMembers(MemberBuilder& builder) const {
    // If the root node is a compilation unit, unwrap it into individual members.
    // Otherwise just take the members as they are.
    if (rootNode.kind == SyntaxKind::CompilationUnit) {
        for (auto member : rootNode.as<CompilationUnitSyntax>().members) {
            for (auto symbol : createSymbols(*member, *this))
                builder.add(*symbol);
        }
    }
    else {
        for (auto symbol : createSymbols(rootNode, *this))
            builder.add(*symbol);
    }
}

PackageSymbol::PackageSymbol(const ModuleDeclarationSyntax& syntax, const Symbol& parent) :
    ScopeSymbol(SymbolKind::Package, syntax.header.name, parent), syntax(syntax)
{
}

void PackageSymbol::fillMembers(MemberBuilder& builder) const {
    for (auto member : syntax.members) {
        for (auto symbol : createSymbols(*member, *this))
            builder.add(*symbol);
    }
}

ModuleSymbol::ModuleSymbol(const ModuleDeclarationSyntax& syntax, const Symbol& parent) :
    Symbol(SymbolKind::Module, syntax.header.name, parent), syntax(syntax)
{
}

const ParameterizedModuleSymbol& ModuleSymbol::parameterize(const ParameterValueAssignmentSyntax* assignments,
                                                            const ScopeSymbol* instanceScope) const {
    ASSERT(!assignments || instanceScope);

    // TODO: at this point we don't need to handle anything if there are no assignments

    // If we were given a set of parameter assignments, build up some data structures to
    // allow us to easily index them. We need to handle both ordered assignment as well as
    // named assignment (though a specific instance can only use one method or the other).
    bool hasParamAssignments = false;
    bool orderedAssignments = true;
    SmallVectorSized<const OrderedArgumentSyntax*, 8> orderedParams;
    SmallHashMap<string_view, std::pair<const NamedArgumentSyntax*, bool>, 8> namedParams;

    if (assignments) {
        for (auto paramBase : assignments->parameters.parameters) {
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
    }

    // For each parameter assignment we have, match it up to a real parameter and evaluate its initializer.
    SmallHashMap<string_view, const ExpressionSyntax*, 8> paramMap;
    if (orderedAssignments) {
        // We take this branch if we had ordered parameter assignments,
        // or if we didn't have any parameter assignments at all.
        uint32_t orderedIndex = 0;
        for (const auto& info : getDeclaredParams()) {
            if (orderedIndex >= orderedParams.size())
                break;

            if (info.local)
                continue;

            paramMap[info.name] = &orderedParams[orderedIndex++]->expr;
        }

        // Make sure there aren't extra param assignments for non-existent params.
        if (orderedIndex < orderedParams.size()) {
            auto& diag = addError(DiagCode::TooManyParamAssignments, orderedParams[orderedIndex]->getFirstToken().location());
            diag << syntax.header.name.valueText();
            diag << orderedParams.size();
            diag << orderedIndex;
        }
    }
    else {
        // Otherwise handle named assignments.
        for (const auto& info : getDeclaredParams()) {
            auto it = namedParams.find(info.name);
            if (it == namedParams.end())
                continue;

            const NamedArgumentSyntax* arg = it->second.first;
            it->second.second = true;
            if (info.local) {
                // Can't assign to localparams, so this is an error.
                addError(info.bodyParam ? DiagCode::AssignedToLocalBodyParam : DiagCode::AssignedToLocalPortParam, arg->name.location());
                addError(DiagCode::NoteDeclarationHere, info.location) << string_view("parameter");
                continue;
            }

            // It's allowed to have no initializer in the assignment; it means to just use the default
            if (!arg->expr)
                continue;

            paramMap[info.name] = arg->expr;
        }

        for (const auto& pair : namedParams) {
            // We marked all the args that we used, so anything left over is a param assignment
            // for a non-existent parameter.
            if (!pair.second.second) {
                auto& diag = addError(DiagCode::ParameterDoesNotExist, pair.second.first->name.location());
                diag << pair.second.first->name.valueText();
                diag << syntax.header.name.valueText();
            }
        }
    }

    // TODO: containing symbol is wrong
    return allocate<ParameterizedModuleSymbol>(*this, *this, instanceScope, paramMap);
}

const std::vector<ModuleSymbol::ParameterInfo>& ModuleSymbol::getDeclaredParams() const {
    if (!paramInfoCache) {
        // Discover all of the element's parameters. If we have a parameter port list, the only
        // publicly visible parameters are the ones in that list. Otherwise, parameters declared
        // in the module body are publicly visible.
        const ModuleHeaderSyntax& header = syntax.header;
        SmallHashMap<string_view, SourceLocation, 16> nameDupMap;
        std::vector<ParameterInfo> buffer;

        bool overrideLocal = false;
        if (header.parameters) {
            bool lastLocal = false;
            for (const ParameterDeclarationSyntax* paramDecl : header.parameters->declarations)
                lastLocal = getParamDecls(*paramDecl, buffer, nameDupMap, lastLocal, false, false);
            overrideLocal = true;
        }

        // also find direct body parameters
        for (const MemberSyntax* member : syntax.members) {
            if (member->kind == SyntaxKind::ParameterDeclarationStatement)
                getParamDecls(member->as<ParameterDeclarationStatementSyntax>().parameter, buffer,
                              nameDupMap, false, overrideLocal, true);
        }

        paramInfoCache = std::move(buffer);
    }
    return *paramInfoCache;
}

bool ModuleSymbol::getParamDecls(const ParameterDeclarationSyntax& paramDecl, std::vector<ParameterInfo>& buffer,
                                 HashMapBase<string_view, SourceLocation>& nameDupMap,
                                 bool lastLocal, bool overrideLocal, bool bodyParam) const {
    // It's legal to leave off the parameter keyword in the parameter port list.
    // If you do so, we "inherit" the parameter or localparam keyword from the previous entry.
    // This isn't allowed in a module body, but the parser will take care of the error for us.
    bool local = false;
    if (!paramDecl.keyword)
        local = lastLocal;
    else {
        // In the body of a module that has a parameter port list in its header, parameters are
        // actually just localparams. overrideLocal will be true in this case.
        local = paramDecl.keyword.kind == TokenKind::LocalParamKeyword || overrideLocal;
    }

    for (const VariableDeclaratorSyntax* declarator : paramDecl.declarators) {
        string_view declName = declarator->name.valueText();
        if (declName.empty())
            continue;

        auto declLocation = declarator->name.location();
        auto pair = nameDupMap.emplace(declName, declLocation);
        if (!pair.second) {
            addError(DiagCode::DuplicateDefinition, declLocation) << string("parameter") << declName;
            addError(DiagCode::NotePreviousDefinition, pair.first->second);
        }
        else {
            ExpressionSyntax* init = nullptr;
            if (declarator->initializer)
                init = &declarator->initializer->expr;
            else if (local)
                addError(DiagCode::LocalParamNoInitializer, declLocation);
            else if (bodyParam)
                addError(DiagCode::BodyParamNoInitializer, declLocation);
            buffer.push_back({ paramDecl, *declarator, declName, declLocation, init, local, bodyParam });
        }
    }
    return local;
}

ParameterizedModuleSymbol::ParameterizedModuleSymbol(const ModuleSymbol& module, const Symbol& parent,
                                                     const ScopeSymbol* instanceScope,
                                                     const HashMapBase<string_view, const ExpressionSyntax*>& parameterAssignments) :
    ScopeSymbol(SymbolKind::ParameterizedModule, parent, module.name, module.location),
    module(module), instanceScope(instanceScope)
{
    for (const auto& element : parameterAssignments)
        paramAssignments.emplace(element.first, element.second);

    ASSERT(instanceScope || paramAssignments.empty());
}

void ParameterizedModuleSymbol::fillMembers(MemberBuilder& builder) const {
    ParameterPortListSyntax* parameterList = module.syntax.header.parameters;
    if (parameterList) {
        for (const ParameterDeclarationSyntax* declaration : parameterList->declarations) {
            for (const VariableDeclaratorSyntax* decl : declaration->declarators) {
                // TODO: hack to get param values working

                auto it = paramAssignments.find(decl->name.valueText());
                builder.add(allocate<ParameterSymbol>(decl->name.valueText(), decl->name.location(),
                                                      declaration->type,
                                                      decl->initializer ? &decl->initializer->expr : nullptr,
                                                      it != paramAssignments.end() ? it->second : nullptr,
                                                      instanceScope, false, false, *this));
            }
        }
    }

    for (const MemberSyntax* node : module.syntax.members) {
        switch (node->kind) {
            case SyntaxKind::ParameterDeclarationStatement: {
                const ParameterDeclarationSyntax& declaration = node->as<ParameterDeclarationStatementSyntax>().parameter;
                for (const VariableDeclaratorSyntax* decl : declaration.declarators) {

                    auto it = paramAssignments.find(decl->name.valueText());
                    builder.add(allocate<ParameterSymbol>(decl->name.valueText(), decl->name.location(),
                                                          declaration.type,
                                                          decl->initializer ? &decl->initializer->expr : nullptr,
                                                          it != paramAssignments.end() ? it->second : nullptr,
                                                          instanceScope, false, false, *this));
                }
                break;
            }
            default: {
                for (auto symbol : createSymbols(*node, *this))
                    builder.add(*symbol);
                break;
            }
        }
    }
}

ModuleInstanceSymbol::ModuleInstanceSymbol(string_view name, SourceLocation location,
                                           const ParameterizedModuleSymbol& module, const Symbol& parent) :
    Symbol(SymbolKind::ModuleInstance, parent, name, location),
    module(module) {}

IfGenerateSymbol::IfGenerateSymbol(const IfGenerateSyntax& syntax, const ScopeSymbol& parent) :
    ScopeSymbol(SymbolKind::IfGenerate, parent),
    syntax(syntax) {}

void IfGenerateSymbol::fillMembers(MemberBuilder& builder) const {
    // TODO: better error checking
    const auto& cv = containingScope().evaluateConstant(syntax.condition);
    if (!cv)
        return;

    const SVInt& value = cv.integer();
    if ((logic_t)value)
        builder.add(allocate<GenerateBlockSymbol>("", SourceLocation(), syntax.block, *this));
    else if (syntax.elseClause)
        builder.add(allocate<GenerateBlockSymbol>("", SourceLocation(), syntax.elseClause->clause, *this));
}

LoopGenerateSymbol::LoopGenerateSymbol(const LoopGenerateSyntax& syntax, const ScopeSymbol& parent) :
    ScopeSymbol(SymbolKind::LoopGenerate, parent),
    syntax(syntax) {}

void LoopGenerateSymbol::fillMembers(MemberBuilder& builder) const {
    // If the loop initializer has a genvar keyword, we can use it directly. Otherwise
    // we need to do a lookup to make sure we have the actual genvar.
    // TODO: do the actual lookup

    // Initialize the genvar
    const ScopeSymbol& parent = containingScope();
    const auto& initial = parent.evaluateConstant(syntax.initialExpr);
    if (!initial)
        return;

    // Fabricate a local variable that will serve as the loop iteration variable.
    const DesignRootSymbol& root = parent.getRoot();
    DynamicScopeSymbol iterScope(parent);
    VariableSymbol local(syntax.identifier.valueText(), syntax.identifier.location(),
                         root.getKnownType(SyntaxKind::IntType), iterScope);
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

        const auto& implicitParam = root.allocate<ParameterSymbol>(syntax.identifier.valueText(),
                                                                   syntax.identifier.location(),
                                                                   root.getKnownType(SyntaxKind::IntType),
                                                                   *genvar, *this);

        builder.add(root.allocate<GenerateBlockSymbol>("", SourceLocation(),
                                                       syntax.block, implicitParam, parent));
    }
}

GenerateBlockSymbol::GenerateBlockSymbol(string_view name, SourceLocation location, const SyntaxNode& body,
                                         const Symbol& parent) :
    ScopeSymbol(SymbolKind::GenerateBlock, parent, name, location),
    body(body) {}

GenerateBlockSymbol::GenerateBlockSymbol(string_view name, SourceLocation location, const SyntaxNode& body,
                                         const ParameterSymbol& implicitParam, const Symbol& parent) :
    ScopeSymbol(SymbolKind::GenerateBlock, parent, name, location),
    body(body), implicitParam(&implicitParam) {}

void GenerateBlockSymbol::fillMembers(MemberBuilder& builder) const {
    if (implicitParam)
        builder.add(*implicitParam);

    if (body.kind == SyntaxKind::GenerateBlock) {
        for (auto member : body.as<GenerateBlockSyntax>().members) {
            for (auto symbol : createSymbols(*member, *this))
                builder.add(*symbol);
        }
    }
    else {
        for (auto symbol : createSymbols(body, *this))
            builder.add(*symbol);
    }
}

}
