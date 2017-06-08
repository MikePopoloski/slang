//------------------------------------------------------------------------------
// HierarchySymbols.cpp
// Contains hierarchy-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "Binder.h"
#include "ConstantEvaluator.h"

namespace slang {

CompilationUnitSymbol::CompilationUnitSymbol(const CompilationUnitSyntax& syntax, const Symbol& parent) :
    ScopeSymbol(SymbolKind::CompilationUnit, parent)
{
    for (auto member : syntax.members) {
        for (auto symbol : createSymbols(*member, *this))
            addMember(*symbol);
    }
}

CompilationUnitSymbol::CompilationUnitSymbol(SymbolList symbols, const Symbol& parent) :
    ScopeSymbol(SymbolKind::CompilationUnit, parent)
{
    for (auto symbol : symbols)
        addMember(*symbol);
}

ModuleSymbol::ModuleSymbol(const ModuleDeclarationSyntax& decl, const Symbol& parent) :
    Symbol(SymbolKind::Module, decl.header.name, parent), decl(decl),
    syntax(decl)
{
}

const ParameterizedModuleSymbol& ModuleSymbol::parameterize(const ParameterValueAssignmentSyntax* assignments, const ScopeSymbol* instanceScope) const {
    ASSERT(!assignments || instanceScope);

    // If we were given a set of parameter assignments, build up some data structures to
    // allow us to easily index them. We need to handle both ordered assignment as well as
    // named assignment (though a specific instance can only use one method or the other).
    bool hasParamAssignments = false;
    bool orderedAssignments = true;
    SmallVectorSized<const OrderedArgumentSyntax*, 8> orderedParams;
    SmallHashMap<StringRef, std::pair<const NamedArgumentSyntax*, bool>, 8> namedParams;

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
    SmallHashMap<StringRef, ConstantValue, 8> paramMap;
    if (orderedAssignments) {
        // We take this branch if we had ordered parameter assignments,
        // or if we didn't have any parameter assignments at all.
        uint32_t orderedIndex = 0;
        for (const auto& info : getDeclaredParams()) {
            if (orderedIndex >= orderedParams.count())
                break;

            if (info.local)
                continue;

            paramMap[info.name] = evaluate(info.paramDecl, *instanceScope, orderedParams[orderedIndex++]->expr, info.location);
        }

        // Make sure there aren't extra param assignments for non-existent params.
        if (orderedIndex < orderedParams.count()) {
            auto& diag = addError(DiagCode::TooManyParamAssignments, orderedParams[orderedIndex]->getFirstToken().location());
            diag << decl.header.name.valueText();
            diag << orderedParams.count();
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
                addError(DiagCode::NoteDeclarationHere, info.location) << StringRef("parameter");
                continue;
            }

            // It's allowed to have no initializer in the assignment; it means to just use the default
            if (!arg->expr)
                continue;

            paramMap[info.name] = evaluate(info.paramDecl, *instanceScope, *arg->expr, info.location);
        }

        for (const auto& pair : namedParams) {
            // We marked all the args that we used, so anything left over is a param assignment
            // for a non-existent parameter.
            if (!pair.second.second) {
                auto& diag = addError(DiagCode::ParameterDoesNotExist, pair.second.first->name.location());
                diag << pair.second.first->name.valueText();
                diag << decl.header.name.valueText();
            }
        }
    }

    // TODO: containing symbol is wrong
    return allocate<ParameterizedModuleSymbol>(*this, *this, paramMap);
}

ConstantValue ModuleSymbol::evaluate(const ParameterDeclarationSyntax& paramDecl, const ScopeSymbol& scope,
                                     const ExpressionSyntax& expr, SourceLocation declLocation) const {
    // If no type is given, infer the type from the initializer
    if (paramDecl.type.kind == SyntaxKind::ImplicitType)
        return scope.evaluateConstant(expr);
    else {
        const TypeSymbol& type = scope.getType(paramDecl.type);
        return scope.evaluateConstantAndConvert(expr, type, declLocation);
    }
}

const std::vector<ModuleSymbol::ParameterInfo>& ModuleSymbol::getDeclaredParams() const {
    if (!paramInfoCache) {
        // Discover all of the element's parameters. If we have a parameter port list, the only
        // publicly visible parameters are the ones in that list. Otherwise, parameters declared
        // in the module body are publicly visible.
        const ModuleHeaderSyntax& header = decl.header;
        SmallHashMap<StringRef, SourceLocation, 16> nameDupMap;
        std::vector<ParameterInfo> buffer;

        bool overrideLocal = false;
        if (header.parameters) {
            bool lastLocal = false;
            for (const ParameterDeclarationSyntax* paramDecl : header.parameters->declarations)
                lastLocal = getParamDecls(*paramDecl, buffer, nameDupMap, lastLocal, false, false);
            overrideLocal = true;
        }

        // also find direct body parameters
        for (const MemberSyntax* member : decl.members) {
            if (member->kind == SyntaxKind::ParameterDeclarationStatement)
                getParamDecls(member->as<ParameterDeclarationStatementSyntax>().parameter, buffer,
                              nameDupMap, false, overrideLocal, true);
        }

        paramInfoCache = std::move(buffer);
    }
    return *paramInfoCache;
}

bool ModuleSymbol::getParamDecls(const ParameterDeclarationSyntax& syntax, std::vector<ParameterInfo>& buffer,
                                 HashMapBase<StringRef, SourceLocation>& nameDupMap,
                                 bool lastLocal, bool overrideLocal, bool bodyParam) const {
    // It's legal to leave off the parameter keyword in the parameter port list.
    // If you do so, we "inherit" the parameter or localparam keyword from the previous entry.
    // This isn't allowed in a module body, but the parser will take care of the error for us.
    bool local = false;
    if (!syntax.keyword)
        local = lastLocal;
    else {
        // In the body of a module that has a parameter port list in its header, parameters are
        // actually just localparams. overrideLocal will be true in this case.
        local = syntax.keyword.kind == TokenKind::LocalParamKeyword || overrideLocal;
    }

    for (const VariableDeclaratorSyntax* declarator : syntax.declarators) {
        auto declName = declarator->name.valueText();
        if (!declName)
            continue;

        auto declLocation = declarator->name.location();
        auto pair = nameDupMap.emplace(declName, declLocation);
        if (!pair.second) {
            addError(DiagCode::DuplicateDefinition, declLocation) << StringRef("parameter") << declName;
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
            buffer.push_back({ syntax, *declarator, declName, declLocation, init, local, bodyParam });
        }
    }
    return local;
}

ParameterizedModuleSymbol::ParameterizedModuleSymbol(const ModuleSymbol& module, const Symbol& parent,
                                                     const HashMapBase<StringRef, ConstantValue>& parameterAssignments) :
    ScopeSymbol(SymbolKind::Module, parent, module.name, module.location), module(module)
{
}

void ParameterizedModuleSymbol::initMembers() const {
    ParameterPortListSyntax* parameterList = module.syntax.header.parameters;
    if (parameterList) {
        for (const ParameterDeclarationSyntax* declaration : parameterList->declarations) {
            for (const VariableDeclaratorSyntax* decl : declaration->declarators) {
                // TODO: hack to get param values working
                const ConstantValue& cv = evaluateConstant(decl->initializer->expr);

                addMember(allocate<ParameterSymbol>(decl->name.valueText(), decl->name.location(),
                                                    getRoot().getKnownType(SyntaxKind::IntType), cv, *this));
            }
        }
    }

    for (const MemberSyntax* node : module.syntax.members) {
        switch (node->kind) {
            case SyntaxKind::ParameterDeclarationStatement: {
                const ParameterDeclarationSyntax& declaration = node->as<ParameterDeclarationStatementSyntax>().parameter;
                for (const VariableDeclaratorSyntax* decl : declaration.declarators) {

                    // TODO: hack to get param values working
                    const ConstantValue& cv = evaluateConstant(decl->initializer->expr);

                    addMember(allocate<ParameterSymbol>(decl->name.valueText(), decl->name.location(),
                                                        getRoot().getErrorType(), cv, *this));
                }
                break;
            }
            default: {
                for (auto symbol : createSymbols(*node, *this))
                    addMember(*symbol);
                break;
            }
        }
    }
}

ModuleInstanceSymbol::ModuleInstanceSymbol(StringRef name, SourceLocation location,
                                           const ParameterizedModuleSymbol& module, const Symbol& parent) :
    Symbol(SymbolKind::ModuleInstance, parent, name, location),
    module(module)
{
}

GenerateBlockSymbol::GenerateBlockSymbol(StringRef name, SourceLocation location, const Symbol& parent) :
    ScopeSymbol(SymbolKind::GenerateBlock, parent, name, location)
{
}

void GenerateBlockSymbol::initMembers() const {
    if (syntax) {
        for (auto member : syntax->members) {
            for (auto symbol : createSymbols(*member, *this))
                addMember(*symbol);
        }
    }
}

void GenerateBlockSymbol::fromSyntax(const ScopeSymbol& parent, const IfGenerateSyntax& syntax,
                                     SmallVector<const GenerateBlockSymbol*>& results) {
    // TODO: better error checking
    const auto& cv = parent.evaluateConstant(syntax.condition);
    if (!cv)
        return;

    const DesignRootSymbol& root = parent.getRoot();
    auto& block = root.allocate<GenerateBlockSymbol>("", SourceLocation(), parent);
    results.append(&block);

    const SVInt& value = cv.integer();
    if ((logic_t)value)
        block.handleBlock(syntax.block);
    else if (syntax.elseClause)
        block.handleBlock(syntax.elseClause->clause);
}

void GenerateBlockSymbol::fromSyntax(const ScopeSymbol& parent, const LoopGenerateSyntax& syntax,
                                     SmallVector<const GenerateBlockSymbol*>& results) {
    // If the loop initializer has a genvar keyword, we can use it directly. Otherwise
    // we need to do a lookup to make sure we have the actual genvar.
    // TODO: do the actual lookup
    
    // Initialize the genvar
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
    ConstantEvaluator ce;
    auto& genvar = ce.createTemporary(local);
    
    // Generate blocks!
    for (genvar = initial; ce.evaluateBool(stopExpr); ce.evaluateExpr(iterExpr)) {
        // Spec: each generate block gets their own scope, with an implicit
        // localparam of the same name as the genvar.
        // TODO: scope name

        auto& block = root.allocate<GenerateBlockSymbol>("", SourceLocation(), parent);
        block.addMember(root.allocate<ParameterSymbol>(syntax.identifier.valueText(),
                                                       syntax.identifier.location(),
                                                       root.getKnownType(SyntaxKind::IntType),
                                                       genvar, block));
        block.handleBlock(syntax.block);
    }
}

void GenerateBlockSymbol::handleBlock(const SyntaxNode& node) {
    if (node.kind == SyntaxKind::GenerateBlock)
        syntax = &node.as<GenerateBlockSyntax>();
    else {
        for (auto symbol : createSymbols(node, *this))
            addMember(*symbol);
    }
}

}