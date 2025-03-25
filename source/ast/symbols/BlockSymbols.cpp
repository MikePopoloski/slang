//------------------------------------------------------------------------------
// BlockSymbols.cpp
// Contains block-related hierarchy symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/BlockSymbols.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/Expression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/statements/LoopStatements.h"
#include "slang/ast/statements/MiscStatements.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

const Statement& StatementBlockSymbol::getStatement(const ASTContext& parentContext,
                                                    Statement::StatementContext& stmtCtx) const {
    if (!stmt) {
        ensureElaborated();
        if (stmt)
            return *stmt;

        auto syntax = getSyntax();
        if (!syntax || syntax->kind == SyntaxKind::RsRule ||
            syntax->kind == SyntaxKind::ConditionalPattern) {

            auto& bs = BlockStatement::makeEmpty(parentContext.getCompilation());
            bs.blockSymbol = this;
            stmt = &bs;
        }
        else {
            ASTContext context = parentContext;
            context.scope = this;
            context.lookupIndex = SymbolIndex(UINT32_MAX);

            auto oldBlocks = std::exchange(stmtCtx.blocks, blocks);
            auto guard = ScopeGuard([&] { stmtCtx.blocks = oldBlocks; });

            stmt = &Statement::bindBlock(*this, *syntax, context, stmtCtx);
        }
    }
    return *stmt;
}

static std::pair<std::string_view, SourceLocation> getLabel(const StatementSyntax& syntax,
                                                            SourceLocation defaultLoc) {
    if (syntax.label) {
        auto token = syntax.label->name;
        return {token.valueText(), token.location()};
    }

    return {""sv, defaultLoc};
}

static StatementBlockSymbol* createBlock(
    const Scope& scope, const StatementSyntax& syntax, std::string_view name, SourceLocation loc,
    StatementBlockKind blockKind = StatementBlockKind::Sequential,
    std::optional<VariableLifetime> lifetime = {}) {

    if (!lifetime.has_value()) {
        auto& scopeSym = scope.asSymbol();
        switch (scopeSym.kind) {
            case SymbolKind::StatementBlock:
                lifetime = scopeSym.as<StatementBlockSymbol>().defaultLifetime;
                break;
            case SymbolKind::Subroutine:
                lifetime = scopeSym.as<SubroutineSymbol>().defaultLifetime;
                break;
            default:
                lifetime = VariableLifetime::Static;
                if (auto def = scopeSym.getDeclaringDefinition())
                    lifetime = def->defaultLifetime;
                break;
        }
    }

    auto& comp = scope.getCompilation();
    auto result = comp.emplace<StatementBlockSymbol>(comp, name, loc, blockKind, *lifetime);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);
    return result;
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const BlockStatementSyntax& syntax) {
    std::string_view name;
    SourceLocation loc;
    if (syntax.blockName) {
        auto token = syntax.blockName->name;
        name = token.valueText();
        loc = token.location();
    }
    else {
        std::tie(name, loc) = getLabel(syntax, syntax.begin.location());
    }

    auto result = createBlock(scope, syntax, name, loc,
                              SemanticFacts::getStatementBlockKind(syntax));

    result->blocks = Statement::createAndAddBlockItems(*result, syntax.items);
    return *result;
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const ForLoopStatementSyntax& syntax) {
    auto [name, loc] = getLabel(syntax, syntax.forKeyword.location());
    auto result = createBlock(scope, syntax, name, loc);

    // If one entry is a variable declaration, they must all be.
    // We'll only enter this function if we have variable decls.
    auto& comp = scope.getCompilation();
    const VariableSymbol* lastVar = nullptr;
    for (auto init : syntax.initializers) {
        if (init->previewNode)
            result->addMembers(*init->previewNode);

        auto& var = VariableSymbol::fromSyntax(comp, init->as<ForVariableDeclarationSyntax>(),
                                               lastVar);

        lastVar = &var;
        result->addMember(var);
    }

    result->blocks = Statement::createAndAddBlockItems(*result, *syntax.statement,
                                                       /* labelHandled */ false);
    return *result;
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const ForeachLoopStatementSyntax& syntax) {
    auto [name, loc] = getLabel(syntax, syntax.keyword.location());
    auto result = createBlock(scope, syntax, name, loc);
    result->blocks = Statement::createAndAddBlockItems(*result, *syntax.statement,
                                                       /* labelHandled */ false);

    // This block needs elaboration to collect iteration variables.
    result->setNeedElaboration();

    return *result;
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const ConditionalStatementSyntax& syntax) {
    // Each matches clause gets its own block with its own variables.
    auto& comp = scope.getCompilation();
    StatementBlockSymbol* first = nullptr;
    StatementBlockSymbol* curr = nullptr;

    for (auto cond : syntax.predicate->conditions) {
        if (cond->matchesClause) {
            auto block = comp.emplace<StatementBlockSymbol>(
                comp, ""sv, cond->matchesClause->getFirstToken().location(),
                StatementBlockKind::Sequential, VariableLifetime::Automatic);

            // Each block needs elaboration to collect pattern variables.
            block->setNeedElaboration();
            block->setSyntax(*cond);

            if (!first) {
                first = curr = block;
            }
            else {
                curr->addMember(*block);
                curr = block;
            }
        }
    }

    // The most nested block gets the actual statement items. If it's already a sequential
    // block we can just use that, otherwise we need to fabricate one.
    StatementBlockSymbol* block;
    if (syntax.statement->kind == SyntaxKind::SequentialBlockStatement ||
        syntax.statement->kind == SyntaxKind::ParallelBlockStatement) {

        block = &StatementBlockSymbol::fromSyntax(scope,
                                                  syntax.statement->as<BlockStatementSyntax>());
    }
    else {
        block = comp.emplace<StatementBlockSymbol>(comp, ""sv,
                                                   syntax.statement->getFirstToken().location(),
                                                   StatementBlockKind::Sequential,
                                                   VariableLifetime::Automatic);
        block->setSyntax(*syntax.statement);
        block->setAttributes(scope, syntax.attributes);
        block->blocks = Statement::createAndAddBlockItems(*block, *syntax.statement,
                                                          /* labelHandled */ false);
    }

    SLANG_ASSERT(curr && first);
    curr->addMember(*block);

    return *first;
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const PatternCaseItemSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<StatementBlockSymbol>(comp, ""sv, syntax.getFirstToken().location(),
                                                     StatementBlockKind::Sequential,
                                                     VariableLifetime::Automatic);
    result->setSyntax(syntax);
    result->blocks = Statement::createAndAddBlockItems(*result, *syntax.statement,
                                                       /* labelHandled */ false);

    // This block needs elaboration to collect pattern variables.
    result->setNeedElaboration();

    return *result;
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const RandSequenceStatementSyntax& syntax) {
    auto [name, loc] = getLabel(syntax, syntax.randsequence.location());
    auto result = createBlock(scope, syntax, name, loc, StatementBlockKind::Sequential,
                              VariableLifetime::Automatic);

    for (auto prod : syntax.productions) {
        if (prod->previewNode)
            result->addMembers(*prod->previewNode);

        if (prod->name.valueText().empty())
            continue;

        auto& symbol = RandSeqProductionSymbol::fromSyntax(scope, *prod);
        result->addMember(symbol);
    }

    return *result;
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const RsRuleSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<StatementBlockSymbol>(comp, ""sv, syntax.getFirstToken().location(),
                                                     StatementBlockKind::Sequential,
                                                     VariableLifetime::Automatic);
    result->setSyntax(syntax);
    result->setNeedElaboration();

    for (auto prod : syntax.prods) {
        if (prod->previewNode)
            result->addMembers(*prod->previewNode);

        if (prod->kind == SyntaxKind::RsCodeBlock) {
            result->addMember(
                StatementBlockSymbol::fromSyntax(scope, prod->as<RsCodeBlockSyntax>()));
        }

        if (syntax.weightClause && syntax.weightClause->codeBlock) {
            result->addMember(StatementBlockSymbol::fromSyntax(
                scope, syntax.weightClause->codeBlock->as<RsCodeBlockSyntax>()));
        }
    }

    return *result;
}

StatementBlockSymbol& StatementBlockSymbol::fromSyntax(const Scope& scope,
                                                       const RsCodeBlockSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<StatementBlockSymbol>(comp, ""sv, syntax.getFirstToken().location(),
                                                     StatementBlockKind::Sequential,
                                                     VariableLifetime::Automatic);
    result->setSyntax(syntax);
    result->blocks = Statement::createAndAddBlockItems(*result, syntax.items);
    return *result;
}

StatementBlockSymbol& StatementBlockSymbol::fromLabeledStmt(const Scope& scope,
                                                            const StatementSyntax& syntax) {
    auto [name, loc] = getLabel(syntax, {});
    auto result = createBlock(scope, syntax, name, loc);
    result->blocks = Statement::createAndAddBlockItems(*result, syntax, /* labelHandled */ true);
    return *result;
}

void StatementBlockSymbol::elaborateVariables(function_ref<void(const Symbol&)> insertCB) const {
    SLANG_ASSERT(!stmt);

    auto syntax = getSyntax();
    if (!syntax)
        return;

    if (syntax->kind == SyntaxKind::RsRule) {
        // Create variables to hold results from all non-void productions
        // invoked by this rule.
        SmallVector<const Symbol*> vars;
        RandSeqProductionSymbol::createRuleVariables(syntax->as<RsRuleSyntax>(), *this, vars);
        for (auto var : vars)
            insertCB(*var);
    }
    else if (syntax->kind == SyntaxKind::ForeachLoopStatement) {
        SmallVector<ForeachLoopStatement::LoopDim, 4> dims;
        ASTContext context(*this, LookupLocation::max);

        if (!ForeachLoopStatement::buildLoopDims(*syntax->as<ForeachLoopStatementSyntax>().loopList,
                                                 context, dims)) {
            // If building loop dims failed we don't want to later proceed with trying to
            // bind the statement again, so just set to invalid here.
            stmt = &InvalidStatement::Instance;
        }

        for (auto& dim : dims) {
            if (dim.loopVar)
                insertCB(*dim.loopVar);
        }
    }
    else if (syntax->kind == SyntaxKind::ConditionalPattern) {
        ASTContext context(*this, LookupLocation::max);

        auto& cond = syntax->as<ConditionalPatternSyntax>();
        SLANG_ASSERT(cond.matchesClause);

        SmallVector<const PatternVarSymbol*> vars;
        if (!Pattern::createPatternVars(context, *cond.matchesClause->pattern, *cond.expr, vars))
            stmt = &InvalidStatement::Instance;

        for (auto var : vars)
            insertCB(*var);
    }
    else if (syntax->kind == SyntaxKind::PatternCaseItem) {
        ASTContext context(*this, LookupLocation::max);
        SLANG_ASSERT(syntax->parent);
        auto& caseSyntax = syntax->parent->as<CaseStatementSyntax>();

        SmallVector<const PatternVarSymbol*> vars;
        if (!Pattern::createPatternVars(context, *syntax->as<PatternCaseItemSyntax>().pattern,
                                        *caseSyntax.expr, vars)) {
            stmt = &InvalidStatement::Instance;
        }

        for (auto var : vars)
            insertCB(*var);
    }
}

ProceduralBlockSymbol::ProceduralBlockSymbol(SourceLocation loc, ProceduralBlockKind procedureKind,
                                             bool isFromAssertion) :
    Symbol(SymbolKind::ProceduralBlock, "", loc), procedureKind(procedureKind),
    isFromAssertion(isFromAssertion) {
}

const Statement& ProceduralBlockSymbol::getBody() const {
    if (!stmt) {
        SLANG_ASSERT(!isConstructing);

        isConstructing = true;
        auto guard = ScopeGuard([this] { isConstructing = false; });

        auto scope = getParentScope();
        SLANG_ASSERT(scope && stmtSyntax);

        ASTContext context(*scope, LookupLocation::after(*this));
        context.setProceduralBlock(*this);

        if (procedureKind == ProceduralBlockKind::Final)
            context.flags |= ASTFlags::Final;

        Statement::StatementContext stmtCtx(context);
        stmtCtx.blocks = blocks;

        stmt = &Statement::bind(*stmtSyntax, context, stmtCtx);
    }
    return *stmt;
}

ProceduralBlockSymbol& ProceduralBlockSymbol::createProceduralBlock(
    Scope& scope, ProceduralBlockKind kind, SourceLocation location, bool isFromAssertion,
    const MemberSyntax& syntax, const StatementSyntax& stmtSyntax) {

    auto& comp = scope.getCompilation();
    auto result = comp.emplace<ProceduralBlockSymbol>(location, kind, isFromAssertion);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);
    result->stmtSyntax = &stmtSyntax;

    SmallVector<const SyntaxNode*> extraMembers;
    result->blocks = Statement::createBlockItems(scope, stmtSyntax, /* labelHandled */ false,
                                                 extraMembers);

    for (auto b : result->blocks)
        scope.addMember(*b);
    for (auto member : extraMembers)
        scope.addMembers(*member);

    return *result;
}

ProceduralBlockSymbol& ProceduralBlockSymbol::fromSyntax(Scope& scope,
                                                         const ProceduralBlockSyntax& syntax) {
    return createProceduralBlock(scope, SemanticFacts::getProceduralBlockKind(syntax.kind),
                                 syntax.keyword.location(), /* isFromAssertion */ false, syntax,
                                 *syntax.statement);
}

ProceduralBlockSymbol& ProceduralBlockSymbol::fromSyntax(
    Scope& scope, const ImmediateAssertionMemberSyntax& syntax) {
    return createProceduralBlock(scope, ProceduralBlockKind::Always,
                                 syntax.getFirstToken().location(), /* isFromAssertion */ true,
                                 syntax, *syntax.statement);
}

ProceduralBlockSymbol& ProceduralBlockSymbol::fromSyntax(
    Scope& scope, const ConcurrentAssertionMemberSyntax& syntax) {
    return createProceduralBlock(scope, ProceduralBlockKind::Always,
                                 syntax.getFirstToken().location(), /* isFromAssertion */ true,
                                 syntax, *syntax.statement);
}

void ProceduralBlockSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("procedureKind", toString(procedureKind));
    serializer.write("body", getBody());
}

static std::pair<std::string_view, SourceLocation> getGenerateBlockName(const SyntaxNode& node) {
    if (node.kind == SyntaxKind::GenerateBlock) {
        // Try to find a name for this block. Generate blocks allow the name to be specified twice
        // (for no good reason) so check both locations.
        const GenerateBlockSyntax& block = node.as<GenerateBlockSyntax>();
        if (block.label) {
            auto token = block.label->name;
            return {token.valueText(), token.location()};
        }

        if (block.beginName) {
            auto token = block.beginName->name;
            return {token.valueText(), token.location()};
        }
    }

    return {""sv, node.getFirstToken().location()};
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
                               const ASTContext& context, uint32_t constructIndex,
                               bool isUninstantiated,
                               const SyntaxList<AttributeInstanceSyntax>& attributes,
                               SmallVectorBase<GenerateBlockSymbol*>& results) {
    // [27.5] If a generate block in a conditional generate construct consists of only one item
    // that is itself a conditional generate construct and if that item is not surrounded by
    // begin-end keywords, then this generate block is not treated as a separate scope. The
    // generate construct within this block is said to be directly nested. The generate blocks
    // of the directly nested construct are treated as if they belong to the outer construct.
    switch (syntax.kind) {
        case SyntaxKind::IfGenerate:
            GenerateBlockSymbol::fromSyntax(compilation, syntax.as<IfGenerateSyntax>(), context,
                                            constructIndex, isUninstantiated, results);
            return;
        case SyntaxKind::CaseGenerate:
            GenerateBlockSymbol::fromSyntax(compilation, syntax.as<CaseGenerateSyntax>(), context,
                                            constructIndex, isUninstantiated, results);
            return;
        default:
            break;
    }

    auto [name, loc] = getGenerateBlockName(syntax);

    auto block = compilation.emplace<GenerateBlockSymbol>(compilation, name, loc, constructIndex,
                                                          isUninstantiated);
    block->setSyntax(syntax);
    block->setAttributes(*context.scope, attributes);
    results.push_back(block);

    addBlockMembers(*block, syntax);
}

void GenerateBlockSymbol::fromSyntax(Compilation& compilation, const IfGenerateSyntax& syntax,
                                     const ASTContext& context, uint32_t constructIndex,
                                     bool isUninstantiated,
                                     SmallVectorBase<GenerateBlockSymbol*>& results) {
    std::optional<bool> selector;
    auto& cond = Expression::bind(*syntax.condition, context);
    ConstantValue cv = context.eval(cond);
    if (cv && context.requireBooleanConvertible(cond) && !isUninstantiated)
        selector = cv.isTrue();

    createCondGenBlock(compilation, *syntax.block, context, constructIndex,
                       !selector.has_value() || !selector.value(), syntax.attributes, results);
    if (syntax.elseClause) {
        createCondGenBlock(compilation, *syntax.elseClause->clause, context, constructIndex,
                           !selector.has_value() || selector.value(), syntax.attributes, results);
    }
}

void GenerateBlockSymbol::fromSyntax(Compilation& compilation, const CaseGenerateSyntax& syntax,
                                     const ASTContext& context, uint32_t constructIndex,
                                     bool isUninstantiated,
                                     SmallVectorBase<GenerateBlockSymbol*>& results) {

    SmallVector<const ExpressionSyntax*> expressions;
    const SyntaxNode* defBlock = nullptr;
    for (auto item : syntax.items) {
        switch (item->kind) {
            case SyntaxKind::StandardCaseItem: {
                auto& sci = item->as<StandardCaseItemSyntax>();
                for (auto es : sci.expressions)
                    expressions.push_back(es);
                break;
            }
            case SyntaxKind::DefaultCaseItem:
                // The parser already errored for duplicate defaults,
                // so just ignore if it happens here.
                defBlock = item->as<DefaultCaseItemSyntax>().clause;
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    SmallVector<const Expression*> bound;
    if (!Expression::bindMembershipExpressions(
            context, TokenKind::CaseKeyword, /* requireIntegral */ false,
            /* unwrapUnpacked */ false, /* allowTypeReferences */ true, /* allowValueRange */ true,
            *syntax.condition, expressions, bound)) {
        return;
    }

    auto boundIt = bound.begin();
    auto condExpr = *boundIt++;

    const Type* condType = nullptr;
    ConstantValue condVal = context.eval(*condExpr);
    if (!condVal) {
        if (condExpr->kind == ExpressionKind::TypeReference)
            condType = &condExpr->as<TypeReferenceExpression>().targetType;
        else
            return;
    }

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
            ConstantValue val = context.eval(*expr);

            bool match = val && val == condVal;
            if (!val && condType && expr->kind == ExpressionKind::TypeReference)
                match = expr->as<TypeReferenceExpression>().targetType.isMatching(*condType);

            if (!currentFound && match) {
                currentFound = true;
                currentMatchRange = expr->sourceRange;
            }
        }

        if (currentFound && !found) {
            // This is the first match for this entire case generate.
            found = true;
            matchRange = currentMatchRange;
            createCondGenBlock(compilation, *sci.clause, context, constructIndex, isUninstantiated,
                               syntax.attributes, results);
        }
        else {
            // If we previously found a block, this block also matched, which we should warn about.
            if (currentFound && !warned) {
                auto& diag = context.addDiag(diag::CaseGenerateDup, currentMatchRange);
                diag << condVal;
                diag.addNote(diag::NotePreviousMatch, matchRange);
                warned = true;
            }

            // This block is not taken, so create it as uninstantiated.
            createCondGenBlock(compilation, *sci.clause, context, constructIndex, true,
                               syntax.attributes, results);
        }
    }

    if (defBlock) {
        // Only instantiated if no other blocks were instantiated.
        createCondGenBlock(compilation, *defBlock, context, constructIndex,
                           isUninstantiated || found, syntax.attributes, results);
    }
    else if (!found) {
        auto& diag = context.addDiag(diag::CaseGenerateNoBlock, condExpr->sourceRange);
        diag << condVal;
    }
}

GenerateBlockSymbol& GenerateBlockSymbol::fromSyntax(const Scope& scope,
                                                     const GenerateBlockSyntax& syntax,
                                                     uint32_t constructIndex) {
    // This overload is only called for the illegal case of a generate block
    // without a condition attached.
    auto [name, loc] = getGenerateBlockName(syntax);
    auto& comp = scope.getCompilation();
    auto block = comp.emplace<GenerateBlockSymbol>(comp, name, loc, constructIndex,
                                                   scope.isUninstantiated());
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
    SLANG_ASSERT(parent);

    return createGenBlkName(constructIndex, *parent);
}

void GenerateBlockSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("constructIndex", constructIndex);
    serializer.write("isUninstantiated", isUninstantiated);
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

GenerateBlockArraySymbol& GenerateBlockArraySymbol::fromSyntax(Compilation& comp,
                                                               const LoopGenerateSyntax& syntax,
                                                               SymbolIndex scopeIndex,
                                                               const ASTContext& context,
                                                               uint32_t constructIndex) {
    auto [name, loc] = getGenerateBlockName(*syntax.block);
    auto result = comp.emplace<GenerateBlockArraySymbol>(comp, name, loc, constructIndex);
    result->setSyntax(syntax);
    result->setAttributes(*context.scope, syntax.attributes);

    auto genvar = syntax.identifier;
    if (genvar.isMissing())
        return *result;

    auto genvarSyntax = comp.emplace<IdentifierNameSyntax>(genvar);

    // Walk up the tree a bit to see if we're nested inside another generate loop.
    // If we are, we'll include that parent's array size in our decision about
    // wether we've looped too many times within one generate block.
    const uint64_t baseCount = getGenerateLoopCount(*context.scope);
    const uint64_t loopLimit = comp.getOptions().maxGenerateSteps;

    // If the loop initializer has a `genvar` keyword, we can use the name directly
    // Otherwise we need to do a lookup to make sure we have the actual genvar somewhere.
    if (!syntax.genvar) {
        auto symbol = Lookup::unqualifiedAt(*context.scope, genvar.valueText(),
                                            context.getLocation(), genvar.range());
        if (!symbol)
            return *result;

        if (symbol->kind != SymbolKind::Genvar) {
            auto& diag = context.addDiag(diag::NotAGenvar, genvar.range());
            diag << genvar.valueText();
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            return *result;
        }

        comp.noteReference(*symbol);
    }
    else {
        // Fabricate a genvar symbol to live in this array since it was declared inline.
        auto genvarSymbol = comp.emplace<GenvarSymbol>(genvar.valueText(), genvar.location());
        genvarSymbol->setSyntax(*genvarSyntax);
        result->addMember(*genvarSymbol);
    }

    SmallVector<const GenerateBlockSymbol*> entries;
    auto createBlock = [&, blockLoc = loc](ConstantValue value, bool isUninstantiated) {
        // Spec: each generate block gets their own scope, with an implicit
        // localparam of the same name as the genvar.
        auto block = comp.emplace<GenerateBlockSymbol>(comp, "", blockLoc, (uint32_t)entries.size(),
                                                       isUninstantiated);
        auto implicitParam = comp.emplace<ParameterSymbol>(genvar.valueText(), genvar.location(),
                                                           true /* isLocal */, false /* isPort */);
        implicitParam->setSyntax(*genvarSyntax);
        comp.noteReference(*implicitParam);

        block->addMember(*implicitParam);
        block->setSyntax(*syntax.block);

        addBlockMembers(*block, *syntax.block);

        implicitParam->setType(comp.getIntegerType());
        implicitParam->setValue(comp, std::move(value), /* needsCoercion */ false);
        implicitParam->setIsFromGenvar(true);

        block->arrayIndex = &implicitParam->getValue().integer();
        entries.push_back(block);
    };

    // Bind the initialization expression.
    auto& initial = Expression::bindRValue(comp.getIntegerType(), *syntax.initialExpr,
                                           syntax.equals.range(), context);
    ConstantValue initialVal = context.eval(initial);
    if (!initialVal)
        return *result;

    // Fabricate a local variable that will serve as the loop iteration variable.
    auto& iterScope = *comp.emplace<StatementBlockSymbol>(comp, "", loc,
                                                          StatementBlockKind::Sequential,
                                                          VariableLifetime::Automatic);
    auto& local = *comp.emplace<VariableSymbol>(genvar.valueText(), genvar.location(),
                                                VariableLifetime::Automatic);
    local.setType(comp.getIntegerType());
    local.flags |= VariableFlags::CompilerGenerated;

    iterScope.setTemporaryParent(*context.scope, scopeIndex);
    iterScope.addMember(local);

    // Bind the stop and iteration expressions so we can reuse them on each iteration.
    ASTContext iterContext(iterScope, LookupLocation::max);
    auto& stopExpr = Expression::bind(*syntax.stopExpr, iterContext);
    auto& iterExpr = Expression::bind(*syntax.iterationExpr, iterContext,
                                      ASTFlags::AssignmentAllowed);
    if (stopExpr.bad() || iterExpr.bad())
        return *result;

    if (!context.requireBooleanConvertible(stopExpr))
        return *result;

    // Create storage for the iteration variable.
    EvalContext evalContext(iterContext);
    evalContext.pushEmptyFrame();

    auto loopVal = evalContext.createLocal(&local, initialVal);
    if (loopVal->integer().hasUnknown())
        iterContext.addDiag(diag::GenvarUnknownBits, genvar.range()) << *loopVal;

    // Generate blocks! In the first pass we evaluate all indices for correctness,
    // letting us enforce the loop limit to detect infinite loops before trying
    // to generate more hierarchy.
    uint64_t loopCount = 0;
    SmallSet<SVInt, 8> usedValues;
    SmallVector<SVInt, 8> indices;
    while (true) {
        loopCount += baseCount;
        if (loopCount > loopLimit) {
            context.addDiag(diag::MaxGenerateStepsExceeded, syntax.keyword.range());
            return *result;
        }

        auto stop = stopExpr.eval(evalContext);
        if (stop.bad() || !stop.isTrue()) {
            result->valid = !stop.bad();
            break;
        }

        indices.emplace_back(loopVal->integer());
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

    // If we never ran the iteration expression, run it once to ensure
    // we've collected all errors.
    if (indices.empty())
        iterExpr.eval(evalContext);

    evalContext.reportAllDiags();

    // If the generate loop completed successfully, go through and create blocks.
    if (result->valid) {
        bool isUninstantiated = context.scope->isUninstantiated();
        for (auto& index : indices)
            createBlock(index, isUninstantiated);
    }

    result->entries = entries.copy(comp);
    if (entries.empty()) {
        createBlock(SVInt(32, 0, true), true);
    }
    else {
        for (auto entry : entries)
            result->addMember(*entry);
    }

    return *result;
}

std::string GenerateBlockArraySymbol::getExternalName() const {
    if (!name.empty())
        return std::string(name);

    auto parent = getParentScope();
    SLANG_ASSERT(parent);

    return createGenBlkName(constructIndex, *parent);
}

void GenerateBlockArraySymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("constructIndex", constructIndex);
}

} // namespace slang::ast
