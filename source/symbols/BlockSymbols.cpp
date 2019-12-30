//------------------------------------------------------------------------------
// BlockSymbols.cpp
// Contains block-related hierarchy symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/BlockSymbols.h"

#include <nlohmann/json.hpp>

#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/symbols/ParameterSymbols.h"
#include "slang/symbols/Type.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/StackContainer.h"

namespace slang {

const Statement& StatementBlockSymbol::getBody() const {
    return binder.getStatement(
        BindContext(*this, LookupLocation::max, BindFlags::ProceduralStatement));
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const BlockStatementSyntax& syntax) {
    string_view name;
    SourceLocation loc;
    if (syntax.blockName) {
        auto token = syntax.blockName->name;
        name = token.valueText();
        loc = token.location();
    }
    else if (syntax.label) {
        auto token = syntax.label->name;
        name = token.valueText();
        loc = token.location();
    }
    else {
        name = "";
        loc = syntax.begin.location();
    }

    StatementBlockKind blockKind = SemanticFacts::getStatementBlockKind(syntax);

    auto& comp = scope.getCompilation();
    auto result = comp.emplace<StatementBlockSymbol>(comp, name, loc, blockKind);
    result->binder.setItems(*result, syntax.items, syntax.sourceRange());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    return *result;
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const ForLoopStatementSyntax& syntax) {
    string_view name;
    SourceLocation loc;
    if (syntax.label) {
        auto token = syntax.label->name;
        name = token.valueText();
        loc = token.location();
    }
    else {
        name = "";
        loc = syntax.forKeyword.location();
    }

    auto& comp = scope.getCompilation();
    auto result =
        comp.emplace<StatementBlockSymbol>(comp, name, loc, StatementBlockKind::Sequential);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    // If one entry is a variable declaration, they must all be.
    const VariableSymbol* lastVar = nullptr;
    for (auto init : syntax.initializers) {
        auto& var =
            VariableSymbol::fromSyntax(comp, init->as<ForVariableDeclarationSyntax>(), lastVar);

        lastVar = &var;
        result->addMember(var);
    }

    result->binder.setSyntax(*result, syntax);
    for (auto block : result->binder.getBlocks())
        result->addMember(*block);

    return *result;
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const ForeachLoopStatementSyntax& syntax) {
    string_view name;
    SourceLocation loc;
    if (syntax.label) {
        auto token = syntax.label->name;
        name = token.valueText();
        loc = token.location();
    }
    else {
        name = "";
        loc = syntax.keyword.location();
    }

    auto& comp = scope.getCompilation();
    auto result =
        comp.emplace<StatementBlockSymbol>(comp, name, loc, StatementBlockKind::Sequential);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    // Get the name of the array variable.
    auto nameSyntax = syntax.loopList->arrayName;
    while (nameSyntax->kind == SyntaxKind::ScopedName)
        nameSyntax = nameSyntax->as<ScopedNameSyntax>().right;

    string_view arrayName;
    if (nameSyntax->kind == SyntaxKind::IdentifierName)
        arrayName = nameSyntax->as<IdentifierNameSyntax>().identifier.valueText();

    // Creates loop iteration variables.
    for (auto loopVar : syntax.loopList->loopVariables) {
        if (loopVar->kind == SyntaxKind::EmptyIdentifierName)
            continue;

        auto& idName = loopVar->as<IdentifierNameSyntax>();
        auto varName = idName.identifier.valueText();
        if (varName.empty())
            continue;

        if (varName == arrayName) {
            scope.addDiag(diag::LoopVarShadowsArray, loopVar->sourceRange()) << varName;
            continue;
        }

        result->addMember(VariableSymbol::fromForeachVar(comp, idName));
    }

    result->binder.setSyntax(*result, syntax);
    for (auto block : result->binder.getBlocks())
        result->addMember(*block);

    return *result;
}

StatementBlockSymbol& StatementBlockSymbol::fromLabeledStmt(const Scope& scope,
                                                            const StatementSyntax& syntax) {
    auto token = syntax.label->name;
    string_view name = token.valueText();
    SourceLocation loc = token.location();

    auto& comp = scope.getCompilation();
    auto result =
        comp.emplace<StatementBlockSymbol>(comp, name, loc, StatementBlockKind::Sequential);
    result->binder.setSyntax(*result, syntax, /* labelHandled */ true);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    return *result;
}

const Statement& ProceduralBlockSymbol::getBody() const {
    return binder.getStatement(BindContext(*getParentScope(), LookupLocation::after(*this),
                                           BindFlags::ProceduralStatement));
}

ProceduralBlockSymbol& ProceduralBlockSymbol::fromSyntax(
    const Scope& scope, const ProceduralBlockSyntax& syntax,
    span<const StatementBlockSymbol* const>& additionalBlocks) {

    auto& comp = scope.getCompilation();
    auto kind = SemanticFacts::getProceduralBlockKind(syntax.kind);
    auto result = comp.emplace<ProceduralBlockSymbol>(syntax.keyword.location(), kind);

    result->binder.setSyntax(scope, *syntax.statement, /* labelHandled */ false);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    additionalBlocks = result->binder.getBlocks();

    return *result;
}

void ProceduralBlockSymbol::toJson(json& j) const {
    j["procedureKind"] = toString(procedureKind);
}

static string_view getGenerateBlockName(const SyntaxNode& node) {
    if (node.kind != SyntaxKind::GenerateBlock)
        return "";

    // Try to find a name for this block. Generate blocks allow the name to be specified twice
    // (for no good reason) so check both locations.
    const GenerateBlockSyntax& block = node.as<GenerateBlockSyntax>();
    if (block.label)
        return block.label->name.valueText();

    if (block.beginName)
        return block.beginName->name.valueText();

    return "";
}

static void addBlockMembers(Compilation& compilation, GenerateBlockSymbol& block,
                            const SyntaxNode& syntax, bool isInstantiated) {
    if (!isInstantiated) {
        compilation.noteUninstantiatedGenerateBlock(syntax);
        return;
    }

    if (syntax.kind != SyntaxKind::GenerateBlock) {
        block.addMembers(syntax);
    }
    else {
        for (auto member : syntax.as<GenerateBlockSyntax>().members)
            block.addMembers(*member);
    }
}

static void createCondGenBlock(Compilation& compilation, const SyntaxNode& syntax,
                               LookupLocation location, const Scope& parent,
                               uint32_t constructIndex, bool isInstantiated,
                               const SyntaxList<AttributeInstanceSyntax>& attributes,
                               SmallVector<GenerateBlockSymbol*>& results) {
    // [27.5] If a generate block in a conditional generate construct consists of only one item
    // that is itself a conditional generate construct and if that item is not surrounded by
    // begin-end keywords, then this generate block is not treated as a separate scope. The
    // generate construct within this block is said to be directly nested. The generate blocks
    // of the directly nested construct are treated as if they belong to the outer construct.
    switch (syntax.kind) {
        case SyntaxKind::IfGenerate:
            GenerateBlockSymbol::fromSyntax(compilation, syntax.as<IfGenerateSyntax>(), location,
                                            parent, constructIndex, isInstantiated, results);
            return;
        case SyntaxKind::CaseGenerate:
            GenerateBlockSymbol::fromSyntax(compilation, syntax.as<CaseGenerateSyntax>(), location,
                                            parent, constructIndex, isInstantiated, results);
            return;
        default:
            break;
    }

    string_view name = getGenerateBlockName(syntax);
    SourceLocation loc = syntax.getFirstToken().location();

    auto block = compilation.emplace<GenerateBlockSymbol>(compilation, name, loc, constructIndex,
                                                          isInstantiated);
    block->setSyntax(syntax);
    block->setAttributes(parent, attributes);
    results.append(block);

    addBlockMembers(compilation, *block, syntax, isInstantiated);
}

void GenerateBlockSymbol::fromSyntax(Compilation& compilation, const IfGenerateSyntax& syntax,
                                     LookupLocation location, const Scope& parent,
                                     uint32_t constructIndex, bool isInstantiated,
                                     SmallVector<GenerateBlockSymbol*>& results) {
    optional<bool> selector;
    if (isInstantiated) {
        BindContext bindContext(parent, location, BindFlags::Constant);
        const auto& cond = Expression::bind(*syntax.condition, bindContext);
        if (cond.constant && bindContext.requireBooleanConvertible(cond))
            selector = cond.constant->isTrue();
    }

    createCondGenBlock(compilation, *syntax.block, location, parent, constructIndex,
                       selector.has_value() && selector.value(), syntax.attributes, results);
    if (syntax.elseClause) {
        createCondGenBlock(compilation, *syntax.elseClause->clause, location, parent,
                           constructIndex, selector.has_value() && !selector.value(),
                           syntax.attributes, results);
    }
}

void GenerateBlockSymbol::fromSyntax(Compilation& compilation, const CaseGenerateSyntax& syntax,
                                     LookupLocation location, const Scope& parent,
                                     uint32_t constructIndex, bool isInstantiated,
                                     SmallVector<GenerateBlockSymbol*>& results) {

    SmallVectorSized<const ExpressionSyntax*, 8> expressions;
    const SyntaxNode* defBlock = nullptr;
    for (auto item : syntax.items) {
        switch (item->kind) {
            case SyntaxKind::StandardCaseItem: {
                auto& sci = item->as<StandardCaseItemSyntax>();
                for (auto es : sci.expressions)
                    expressions.append(es);
                break;
            }
            case SyntaxKind::DefaultCaseItem:
                // The parser already errored for duplicate defaults,
                // so just ignore if it happens here.
                defBlock = item->as<DefaultCaseItemSyntax>().clause;
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    BindContext bindContext(parent, location, BindFlags::Constant);
    SmallVectorSized<const Expression*, 8> bound;
    if (!Expression::bindMembershipExpressions(
            bindContext, TokenKind::CaseKeyword, /* wildcard */ false,
            /* unwrapUnpacked */ false, *syntax.condition, expressions, bound)) {
        return;
    }

    auto boundIt = bound.begin();
    auto condExpr = *boundIt++;
    if (!condExpr->constant)
        return;

    SourceRange matchRange;
    bool found = false;
    bool warned = false;

    for (auto item : syntax.items) {
        if (item->kind != SyntaxKind::StandardCaseItem)
            continue;

        // Check each case expression to see if it matches the condition value.
        bool currentFound = false;
        SourceRange currentMatchRange;
        auto& sci = item->as<StandardCaseItemSyntax>();
        for (size_t i = 0; i < sci.expressions.size(); i++) {
            // Have to keep incrementing the iterator here so that we stay in sync.
            auto expr = *boundIt++;
            auto val = expr->constant;
            if (!currentFound && val && val->equivalentTo(*condExpr->constant)) {
                currentFound = true;
                currentMatchRange = expr->sourceRange;
            }
        }

        if (currentFound && !found) {
            // This is the first match for this entire case generate.
            found = true;
            matchRange = currentMatchRange;
            createCondGenBlock(compilation, *sci.clause, location, parent, constructIndex,
                               isInstantiated, syntax.attributes, results);
        }
        else {
            // If we previously found a block, this block also matched, which we should warn about.
            if (currentFound && !warned) {
                auto& diag = parent.addDiag(diag::CaseGenerateDup, currentMatchRange);
                diag << *condExpr->constant;
                diag.addNote(diag::NotePreviousMatch, matchRange.start());
                warned = true;
            }

            // This block is not taken, so create it as uninstantiated.
            createCondGenBlock(compilation, *sci.clause, location, parent, constructIndex, false,
                               syntax.attributes, results);
        }
    }

    if (defBlock) {
        // Only instantiated if no other blocks were instantiated.
        createCondGenBlock(compilation, *defBlock, location, parent, constructIndex,
                           isInstantiated && !found, syntax.attributes, results);
    }
    else if (!found) {
        auto& diag = parent.addDiag(diag::CaseGenerateNoBlock, condExpr->sourceRange);
        diag << *condExpr->constant;
    }
}

GenerateBlockSymbol& GenerateBlockSymbol::fromSyntax(const Scope& scope,
                                                     const GenerateBlockSyntax& syntax,
                                                     uint32_t constructIndex) {
    // This overload is only called for the illegal case of a generate block
    // without a condition attached.
    string_view name = getGenerateBlockName(syntax);
    SourceLocation loc = syntax.getFirstToken().location();

    auto& comp = scope.getCompilation();
    auto block = comp.emplace<GenerateBlockSymbol>(comp, name, loc, constructIndex,
                                                   /* isInstantiated */ true);
    block->setSyntax(syntax);
    block->setAttributes(scope, syntax.attributes);

    for (auto member : syntax.members)
        block->addMembers(*member);

    return *block;
}

void GenerateBlockSymbol::toJson(json& j) const {
    j["constructIndex"] = constructIndex;
    j["isInstantiated"] = isInstantiated;
}

static uint64_t getGenerateLoopCount(const Scope& parent) {
    uint64_t count = 0;
    const Scope* cur = &parent;
    do {
        const Symbol& sym = cur->asSymbol();
        if (sym.kind == SymbolKind::GenerateBlockArray) {
            auto& gba = sym.as<GenerateBlockArraySymbol>();
            if (!count)
                count = gba.entries.size();
            else
                count *= gba.entries.size();
        }
        else if (sym.kind != SymbolKind::GenerateBlock) {
            break;
        }

        cur = sym.getParentScope();
    } while (cur);

    return count ? count : 1;
}

GenerateBlockArraySymbol& GenerateBlockArraySymbol::fromSyntax(
    Compilation& compilation, const LoopGenerateSyntax& syntax, SymbolIndex scopeIndex,
    LookupLocation location, const Scope& parent, uint32_t constructIndex) {

    string_view name = getGenerateBlockName(*syntax.block);
    SourceLocation loc = syntax.block->getFirstToken().location();
    auto result =
        compilation.emplace<GenerateBlockArraySymbol>(compilation, name, loc, constructIndex);
    result->setSyntax(syntax);
    result->setAttributes(parent, syntax.attributes);

    auto genvar = syntax.identifier;
    if (genvar.isMissing())
        return *result;

    // Walk up the tree a bit to see if we're nested inside another generate loop.
    // If we are, we'll include that parent's array size in our decision about
    // wether we've looped too many times within one generate block.
    const uint64_t baseCount = getGenerateLoopCount(parent);
    const uint64_t loopLimit = compilation.getOptions().maxGenerateSteps;

    // If the loop initializer has a `genvar` keyword, we can use the name directly
    // Otherwise we need to do a lookup to make sure we have the actual genvar somewhere.
    if (!syntax.genvar) {
        auto symbol = parent.lookupUnqualifiedName(genvar.valueText(), location, genvar.range());
        if (!symbol)
            return *result;

        if (symbol->kind != SymbolKind::Genvar) {
            auto& diag = parent.addDiag(diag::NotAGenvar, genvar.range());
            diag << genvar.valueText();
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
        }
    }

    SmallVectorSized<ArrayEntry, 8> entries;
    auto createBlock = [&](ConstantValue value, bool isInstantiated) {
        // Spec: each generate block gets their own scope, with an implicit
        // localparam of the same name as the genvar.
        auto block =
            compilation.emplace<GenerateBlockSymbol>(compilation, "", loc, 1u, isInstantiated);
        auto implicitParam = compilation.emplace<ParameterSymbol>(
            genvar.valueText(), genvar.location(), true /* isLocal */, false /* isPort */);

        block->addMember(*implicitParam);
        block->setSyntax(*syntax.block);

        addBlockMembers(compilation, *block, *syntax.block, isInstantiated);

        implicitParam->setType(compilation.getIntegerType());
        implicitParam->setValue(std::move(value));

        entries.append({ &implicitParam->getValue().integer(), block });
    };

    // Bind the initialization expression.
    BindContext bindContext(parent, location, BindFlags::Constant);
    const auto& initial = Expression::bindRValue(compilation.getIntegerType(), *syntax.initialExpr,
                                                 syntax.equals.location(), bindContext);
    if (!initial.constant)
        return *result;

    // Fabricate a local variable that will serve as the loop iteration variable.
    auto& iterScope = *compilation.emplace<StatementBlockSymbol>(compilation, "", loc,
                                                                 StatementBlockKind::Sequential);
    auto& local = *compilation.emplace<VariableSymbol>(genvar.valueText(), genvar.location());
    local.setType(compilation.getIntegerType());

    iterScope.setTemporaryParent(parent, scopeIndex);
    iterScope.addMember(local);

    // Bind the stop and iteration expressions so we can reuse them on each iteration.
    BindContext iterContext(iterScope, LookupLocation::max, BindFlags::NoHierarchicalNames);
    const auto& stopExpr = Expression::bind(*syntax.stopExpr, iterContext);
    const auto& iterExpr =
        Expression::bind(*syntax.iterationExpr, iterContext, BindFlags::AssignmentAllowed);
    if (stopExpr.bad() || iterExpr.bad())
        return *result;

    if (!bindContext.requireBooleanConvertible(stopExpr))
        return *result;

    EvalContext stopVerifyContext(iterScope, EvalFlags::IsVerifying);
    bool canBeConst = stopExpr.verifyConstant(stopVerifyContext);
    stopVerifyContext.reportDiags(iterContext, stopExpr.sourceRange);
    if (!canBeConst)
        return *result;

    EvalContext iterVerifyContext(iterScope, EvalFlags::IsVerifying);
    canBeConst = iterExpr.verifyConstant(iterVerifyContext);
    iterVerifyContext.reportDiags(iterContext, iterExpr.sourceRange);
    if (!canBeConst)
        return *result;

    // Create storage for the iteration variable.
    EvalContext evalContext(iterScope);
    auto loopVal = evalContext.createLocal(&local, *initial.constant);

    if (loopVal->integer().hasUnknown())
        iterContext.addDiag(diag::GenvarUnknownBits, genvar.range()) << *loopVal;

    // Generate blocks!
    uint64_t loopCount = 0;
    SmallSet<SVInt, 8> usedValues;
    while (true) {
        loopCount += baseCount;
        if (loopCount > loopLimit) {
            parent.addDiag(diag::MaxGenerateStepsExceeded, syntax.keyword.range());
            return *result;
        }

        auto stop = stopExpr.eval(evalContext);
        if (stop.bad() || !stop.isTrue())
            break;

        auto pair = usedValues.emplace(loopVal->integer());
        if (!pair.second) {
            iterContext.addDiag(diag::GenvarDuplicate, genvar.range()) << *loopVal;
            break;
        }

        createBlock(*loopVal, true);

        if (!iterExpr.eval(evalContext))
            break;

        if (loopVal->integer().hasUnknown())
            iterContext.addDiag(diag::GenvarUnknownBits, genvar.range()) << *loopVal;
    }

    evalContext.reportDiags(iterContext, syntax.sourceRange());

    result->entries = entries.copy(compilation);
    if (entries.empty())
        createBlock(SVInt(32, 0, true), false);
    else {
        for (auto& entry : entries)
            result->addMember(*entry.block);
    }

    return *result;
}

void GenerateBlockArraySymbol::toJson(json& j) const {
    j["constructIndex"] = constructIndex;
}

} // namespace slang