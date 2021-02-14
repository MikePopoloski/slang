//------------------------------------------------------------------------------
// BlockSymbols.cpp
// Contains block-related hierarchy symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/BlockSymbols.h"

#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/ParameterSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/Type.h"
#include "slang/util/StackContainer.h"

namespace slang {

const Statement& StatementBlockSymbol::getBody() const {
    ensureElaborated();
    return binder.getStatement(BindContext(*this, LookupLocation::max));
}

static std::pair<string_view, SourceLocation> getLabel(const StatementSyntax& syntax,
                                                       SourceLocation defaultLoc) {
    if (syntax.label) {
        auto token = syntax.label->name;
        return { token.valueText(), token.location() };
    }

    return { ""sv, defaultLoc };
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const BlockStatementSyntax& syntax,
                                                       bool inLoop) {
    string_view name;
    SourceLocation loc;
    if (syntax.blockName) {
        auto token = syntax.blockName->name;
        name = token.valueText();
        loc = token.location();
    }
    else {
        std::tie(name, loc) = getLabel(syntax, syntax.begin.location());
    }

    StatementBlockKind blockKind = SemanticFacts::getStatementBlockKind(syntax);

    auto& comp = scope.getCompilation();
    auto result =
        comp.emplace<StatementBlockSymbol>(comp, name, loc, blockKind, scope.getDefaultLifetime());
    result->binder.setItems(*result, syntax.items, syntax.sourceRange(), inLoop);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    return *result;
}

static StatementBlockSymbol* createBlock(const Scope& scope, const StatementSyntax& syntax,
                                         string_view name, SourceLocation loc) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<StatementBlockSymbol>(
        comp, name, loc, StatementBlockKind::Sequential, scope.getDefaultLifetime());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);
    return result;
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const ForLoopStatementSyntax& syntax,
                                                       bool inLoop) {
    auto [name, loc] = getLabel(syntax, syntax.forKeyword.location());
    auto result = createBlock(scope, syntax, name, loc);

    // If one entry is a variable declaration, they must all be.
    auto& comp = scope.getCompilation();
    const VariableSymbol* lastVar = nullptr;
    for (auto init : syntax.initializers) {
        auto& var =
            VariableSymbol::fromSyntax(comp, init->as<ForVariableDeclarationSyntax>(), lastVar);

        lastVar = &var;
        result->addMember(var);
    }

    result->binder.setSyntax(*result, syntax, inLoop);
    for (auto block : result->binder.getBlocks())
        result->addMember(*block);

    return *result;
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const ForeachLoopStatementSyntax& syntax,
                                                       bool inLoop) {
    auto [name, loc] = getLabel(syntax, syntax.keyword.location());
    auto result = createBlock(scope, syntax, name, loc);

    result->binder.setSyntax(*result, syntax, /* labelHandled */ true, inLoop);
    for (auto block : result->binder.getBlocks())
        result->addMember(*block);

    // This block needs elaboration to collect iteration variables.
    result->setNeedElaboration();

    return *result;
}

StatementBlockSymbol& StatementBlockSymbol::fromLabeledStmt(const Scope& scope,
                                                            const StatementSyntax& syntax,
                                                            bool inLoop) {
    auto [name, loc] = getLabel(syntax, {});
    auto result = createBlock(scope, syntax, name, loc);

    result->binder.setSyntax(*result, syntax, /* labelHandled */ true, inLoop);
    for (auto block : result->binder.getBlocks())
        result->addMember(*block);

    return *result;
}

void StatementBlockSymbol::elaborateVariables(function_ref<void(const Symbol&)> insertCB) const {
    auto stmtSyntax = binder.getSyntax();
    if (!stmtSyntax || stmtSyntax->kind != SyntaxKind::ForeachLoopStatement)
        return;

    const Statement* body = &getBody();
    if (body->kind == StatementKind::Invalid) {
        // Unwrap invalid statements here so that we still get foreach loop
        // variables added even if its body had a problem somewhere.
        body = body->as<InvalidStatement>().child;
        if (!body)
            return;
    }

    for (auto& dim : body->as<ForeachLoopStatement>().loopDims) {
        if (dim.loopVar)
            insertCB(*dim.loopVar);
    }
}

const Statement& ProceduralBlockSymbol::getBody() const {
    return binder.getStatement(BindContext(*getParentScope(), LookupLocation::after(*this)));
}

ProceduralBlockSymbol& ProceduralBlockSymbol::fromSyntax(
    const Scope& scope, const ProceduralBlockSyntax& syntax,
    span<const StatementBlockSymbol* const>& additionalBlocks) {

    auto& comp = scope.getCompilation();
    auto kind = SemanticFacts::getProceduralBlockKind(syntax.kind);
    auto result = comp.emplace<ProceduralBlockSymbol>(syntax.keyword.location(), kind);

    result->binder.setSyntax(scope, *syntax.statement, /* labelHandled */ false,
                             /* inLoop */ false);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    additionalBlocks = result->binder.getBlocks();

    return *result;
}

void ProceduralBlockSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("procedureKind", toString(procedureKind));
    serializer.write("body", getBody());
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

static void addBlockMembers(GenerateBlockSymbol& block, const SyntaxNode& syntax) {
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

    if (isInstantiated)
        addBlockMembers(*block, syntax);
}

void GenerateBlockSymbol::fromSyntax(Compilation& compilation, const IfGenerateSyntax& syntax,
                                     LookupLocation location, const Scope& parent,
                                     uint32_t constructIndex, bool isInstantiated,
                                     SmallVector<GenerateBlockSymbol*>& results) {
    optional<bool> selector;
    if (isInstantiated) {
        BindContext bindContext(parent, location, BindFlags::Constant);
        const auto& cond = Expression::bind(*syntax.condition, bindContext);
        ConstantValue cv = bindContext.eval(cond);
        if (cv && bindContext.requireBooleanConvertible(cond))
            selector = cv.isTrue();
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
    ConstantValue condVal = bindContext.eval(*condExpr);
    if (!condVal)
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
            ConstantValue val = bindContext.eval(*expr);
            if (!currentFound && val && val == condVal) {
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
                diag << condVal;
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
        diag << condVal;
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

static std::string createGenBlkName(uint32_t constructIndex, const Scope& parent) {
    std::string base = "genblk";
    std::string index = std::to_string(constructIndex);
    std::string current = base + index;
    while (parent.find(current)) {
        base += '0';
        current = base + index;
    }

    return current;
}

std::string GenerateBlockSymbol::getExternalName() const {
    if (!name.empty())
        return std::string(name);

    auto parent = getParentScope();
    ASSERT(parent);

    return createGenBlkName(constructIndex, *parent);
}

void GenerateBlockSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("constructIndex", constructIndex);
    serializer.write("isInstantiated", isInstantiated);
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
        auto symbol = Lookup::unqualifiedAt(parent, genvar.valueText(), location, genvar.range());
        if (!symbol)
            return *result;

        if (symbol->kind != SymbolKind::Genvar) {
            auto& diag = parent.addDiag(diag::NotAGenvar, genvar.range());
            diag << genvar.valueText();
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            return *result;
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

        if (isInstantiated)
            addBlockMembers(*block, *syntax.block);

        implicitParam->setType(compilation.getIntegerType());
        implicitParam->setValue(std::move(value));

        entries.append({ &implicitParam->getValue().integer(), block });
    };

    // Bind the initialization expression.
    BindContext bindContext(parent, location, BindFlags::Constant);
    auto& initial = Expression::bindRValue(compilation.getIntegerType(), *syntax.initialExpr,
                                           syntax.equals.location(), bindContext);
    ConstantValue initialVal = bindContext.eval(initial);
    if (!initialVal)
        return *result;

    // Fabricate a local variable that will serve as the loop iteration variable.
    auto& iterScope = *compilation.emplace<StatementBlockSymbol>(
        compilation, "", loc, StatementBlockKind::Sequential, VariableLifetime::Automatic);
    auto& local = *compilation.emplace<VariableSymbol>(genvar.valueText(), genvar.location(),
                                                       VariableLifetime::Automatic);
    local.setType(compilation.getIntegerType());
    local.isCompilerGenerated = true;

    iterScope.setTemporaryParent(parent, scopeIndex);
    iterScope.addMember(local);

    // Bind the stop and iteration expressions so we can reuse them on each iteration.
    BindContext iterContext(iterScope, LookupLocation::max, BindFlags::Constant);
    const auto& stopExpr = Expression::bind(*syntax.stopExpr, iterContext);
    const auto& iterExpr =
        Expression::bind(*syntax.iterationExpr, iterContext, BindFlags::AssignmentAllowed);
    if (stopExpr.bad() || iterExpr.bad())
        return *result;

    if (!bindContext.requireBooleanConvertible(stopExpr))
        return *result;

    // Create storage for the iteration variable.
    EvalContext evalContext(compilation);
    auto loopVal = evalContext.createLocal(&local, initialVal);

    if (loopVal->integer().hasUnknown())
        iterContext.addDiag(diag::GenvarUnknownBits, genvar.range()) << *loopVal;

    // Generate blocks! In the first pass we evaluate all indices for correctness,
    // letting us enforce the loop limit to detect infinite loops before trying
    // to generate more hierarchy.
    uint64_t loopCount = 0;
    SmallSet<SVInt, 8> usedValues;
    SmallVectorSized<SVInt, 8> indices;
    while (true) {
        loopCount += baseCount;
        if (loopCount > loopLimit) {
            parent.addDiag(diag::MaxGenerateStepsExceeded, syntax.keyword.range());
            return *result;
        }

        auto stop = stopExpr.eval(evalContext);
        if (stop.bad() || !stop.isTrue()) {
            result->valid = !stop.bad();
            break;
        }

        indices.emplace(loopVal->integer());
        auto pair = usedValues.emplace(loopVal->integer());
        if (!pair.second) {
            iterContext.addDiag(diag::GenvarDuplicate, genvar.range()) << *loopVal;
            break;
        }

        if (!iterExpr.eval(evalContext))
            break;

        if (loopVal->integer().hasUnknown()) {
            iterContext.addDiag(diag::GenvarUnknownBits, genvar.range()) << *loopVal;
            break;
        }
    }

    evalContext.reportDiags(iterContext);

    // If the generate loop completed successfully, go through and create blocks.
    if (result->valid) {
        for (auto& index : indices)
            createBlock(index, true);
    }

    result->entries = entries.copy(compilation);
    if (entries.empty())
        createBlock(SVInt(32, 0, true), false);
    else {
        for (auto& entry : entries)
            result->addMember(*entry.block);
    }

    return *result;
}

std::string GenerateBlockArraySymbol::getExternalName() const {
    if (!name.empty())
        return std::string(name);

    auto parent = getParentScope();
    ASSERT(parent);

    return createGenBlkName(constructIndex, *parent);
}

void GenerateBlockArraySymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("constructIndex", constructIndex);
}

} // namespace slang
