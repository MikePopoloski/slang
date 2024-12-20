//------------------------------------------------------------------------------
// Statement.cpp
// Statement creation and analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Statement.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/Expression.h"
#include "slang/ast/TimingControl.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace {

using namespace slang;
using namespace slang::ast;

using ER = Statement::EvalResult;

struct EvalVisitor {
    template<typename T>
    ER visit(const T& stmt, EvalContext& context) {
        if (stmt.bad())
            return ER::Fail;

        if (!context.step(stmt.sourceRange.start()))
            return ER::Fail;

        return stmt.evalImpl(context);
    }
};

} // namespace

namespace slang::ast {

using namespace parsing;
using namespace syntax;

const InvalidStatement InvalidStatement::Instance(nullptr);

void InvalidStatement::serializeTo(ASTSerializer& serializer) const {
    if (child)
        serializer.write("child", *child);
}

ER Statement::eval(EvalContext& context) const {
    EvalVisitor visitor;
    return visit(visitor, context);
}

Statement::StatementContext::~StatementContext() {
    if (!lastEventControl.start()) {
        auto proc = rootAstContext.getProceduralBlock();
        if (proc && proc->procedureKind == ProceduralBlockKind::AlwaysFF && !proc->getBody().bad())
            rootAstContext.addDiag(diag::AlwaysFFEventControl, proc->location);
    }
    SLANG_ASSERT(blocks.empty());
}

const Statement* Statement::StatementContext::tryGetBlock(const ASTContext& context,
                                                          const SyntaxNode& target) {
    if (!blocks.empty() && blocks[0]->getSyntax() == &target) {
        auto& result = blocks[0]->getStatement(context, *this);
        blocks = blocks.subspan(1);
        return &result;
    }
    return nullptr;
}

void Statement::StatementContext::observeTiming(const TimingControl& timing) {
    auto proc = rootAstContext.getProceduralBlock();
    if (!proc || proc->procedureKind != ProceduralBlockKind::AlwaysFF || timing.bad())
        return;

    if (timing.kind != TimingControlKind::SignalEvent &&
        timing.kind != TimingControlKind::EventList &&
        timing.kind != TimingControlKind::ImplicitEvent) {
        rootAstContext.addDiag(diag::BlockingInAlwaysFF, timing.sourceRange);
        return;
    }

    if (lastEventControl.start() && !flags.has(StatementFlags::HasTimingError)) {
        auto& diag = rootAstContext.addDiag(diag::AlwaysFFEventControl, timing.sourceRange);
        diag.addNote(diag::NotePreviousUsage, lastEventControl);

        flags |= StatementFlags::HasTimingError;
    }

    lastEventControl = timing.sourceRange;
}

static bool hasSimpleLabel(const StatementSyntax& syntax) {
    if (!syntax.label)
        return false;

    return syntax.kind != SyntaxKind::SequentialBlockStatement &&
           syntax.kind != SyntaxKind::ParallelBlockStatement &&
           syntax.kind != SyntaxKind::ForLoopStatement &&
           syntax.kind != SyntaxKind::ForeachLoopStatement &&
           syntax.kind != SyntaxKind::RandSequenceStatement;
}

const Statement& Statement::bind(const StatementSyntax& syntax, const ASTContext& context,
                                 StatementContext& stmtCtx, bool inList, bool labelHandled) {
    auto& comp = context.getCompilation();

    if (!labelHandled && hasSimpleLabel(syntax)) {
        auto block = stmtCtx.tryGetBlock(context, syntax);
        SLANG_ASSERT(block);
        return *block;
    }

    Statement* result;
    switch (syntax.kind) {
        case SyntaxKind::EmptyStatement:
            result = comp.emplace<EmptyStatement>(syntax.sourceRange());
            if (inList && syntax.attributes.empty())
                context.addDiag(diag::EmptyStatement, syntax.sourceRange());
            break;
        case SyntaxKind::ReturnStatement:
            result = &ReturnStatement::fromSyntax(comp, syntax.as<ReturnStatementSyntax>(), context,
                                                  stmtCtx);
            break;
        case SyntaxKind::JumpStatement: {
            auto& jump = syntax.as<JumpStatementSyntax>();
            if (jump.breakOrContinue.kind == TokenKind::BreakKeyword)
                result = &BreakStatement::fromSyntax(comp, jump, context, stmtCtx);
            else
                result = &ContinueStatement::fromSyntax(comp, jump, context, stmtCtx);
            break;
        }
        case SyntaxKind::DisableStatement:
            result = &DisableStatement::fromSyntax(comp, syntax.as<DisableStatementSyntax>(),
                                                   context);
            break;
        case SyntaxKind::ConditionalStatement:
            result = &ConditionalStatement::fromSyntax(comp,
                                                       syntax.as<ConditionalStatementSyntax>(),
                                                       context, stmtCtx);
            break;
        case SyntaxKind::CaseStatement:
            result = &CaseStatement::fromSyntax(comp, syntax.as<CaseStatementSyntax>(), context,
                                                stmtCtx);
            break;
        case SyntaxKind::ForLoopStatement:
            // We might have an implicit block here; check for that first.
            if (auto block = stmtCtx.tryGetBlock(context, syntax))
                return *block;

            result = &ForLoopStatement::fromSyntax(comp, syntax.as<ForLoopStatementSyntax>(),
                                                   context, stmtCtx);
            break;
        case SyntaxKind::LoopStatement: {
            auto& loop = syntax.as<LoopStatementSyntax>();
            if (loop.repeatOrWhile.kind == TokenKind::RepeatKeyword)
                result = &RepeatLoopStatement::fromSyntax(comp, loop, context, stmtCtx);
            else
                result = &WhileLoopStatement::fromSyntax(comp, loop, context, stmtCtx);
            break;
        }
        case SyntaxKind::ForeachLoopStatement:
            // We might have an implicit block here; check for that first.
            if (auto block = stmtCtx.tryGetBlock(context, syntax))
                return *block;

            result = &ForeachLoopStatement::fromSyntax(comp,
                                                       syntax.as<ForeachLoopStatementSyntax>(),
                                                       context, stmtCtx);
            break;
        case SyntaxKind::DoWhileStatement:
            result = &DoWhileLoopStatement::fromSyntax(comp, syntax.as<DoWhileStatementSyntax>(),
                                                       context, stmtCtx);
            break;
        case SyntaxKind::ForeverStatement:
            result = &ForeverLoopStatement::fromSyntax(comp, syntax.as<ForeverStatementSyntax>(),
                                                       context, stmtCtx);
            break;
        case SyntaxKind::ExpressionStatement:
            result = &ExpressionStatement::fromSyntax(comp, syntax.as<ExpressionStatementSyntax>(),
                                                      context, stmtCtx);
            break;
        case SyntaxKind::VoidCastedCallStatement:
            result = &ExpressionStatement::fromSyntax(comp,
                                                      syntax.as<VoidCastedCallStatementSyntax>(),
                                                      context);
            break;
        case SyntaxKind::SequentialBlockStatement:
        case SyntaxKind::ParallelBlockStatement:
            // A block statement may or may not match up with a hierarchy node. Handle both cases
            // here. We traverse statements in the same order as the findBlocks call below, so this
            // should always sync up exactly.
            if (auto block = stmtCtx.tryGetBlock(context, syntax))
                return *block;

            result = &BlockStatement::fromSyntax(comp, syntax.as<BlockStatementSyntax>(), context,
                                                 stmtCtx);
            break;
        case SyntaxKind::TimingControlStatement:
            result = &TimedStatement::fromSyntax(comp, syntax.as<TimingControlStatementSyntax>(),
                                                 context, stmtCtx);
            break;
        case SyntaxKind::ImmediateAssertStatement:
        case SyntaxKind::ImmediateAssumeStatement:
        case SyntaxKind::ImmediateCoverStatement:
            result = &ImmediateAssertionStatement::fromSyntax(
                comp, syntax.as<ImmediateAssertionStatementSyntax>(), context, stmtCtx);
            break;
        case SyntaxKind::DisableForkStatement:
            result = &DisableForkStatement::fromSyntax(comp,
                                                       syntax.as<DisableForkStatementSyntax>());
            break;
        case SyntaxKind::WaitStatement:
            result = &WaitStatement::fromSyntax(comp, syntax.as<WaitStatementSyntax>(), context,
                                                stmtCtx);
            break;
        case SyntaxKind::WaitForkStatement:
            result = &WaitForkStatement::fromSyntax(comp, syntax.as<WaitForkStatementSyntax>(),
                                                    context);
            break;
        case SyntaxKind::WaitOrderStatement:
            result = &WaitOrderStatement::fromSyntax(comp, syntax.as<WaitOrderStatementSyntax>(),
                                                     context, stmtCtx);
            break;
        case SyntaxKind::BlockingEventTriggerStatement:
        case SyntaxKind::NonblockingEventTriggerStatement:
            result = &EventTriggerStatement::fromSyntax(comp,
                                                        syntax.as<EventTriggerStatementSyntax>(),
                                                        context, stmtCtx);
            break;
        case SyntaxKind::ProceduralAssignStatement:
        case SyntaxKind::ProceduralForceStatement:
            result = &ProceduralAssignStatement::fromSyntax(
                comp, syntax.as<ProceduralAssignStatementSyntax>(), context);
            break;
        case SyntaxKind::ProceduralDeassignStatement:
        case SyntaxKind::ProceduralReleaseStatement:
            result = &ProceduralDeassignStatement::fromSyntax(
                comp, syntax.as<ProceduralDeassignStatementSyntax>(), context);
            break;
        case SyntaxKind::AssertPropertyStatement:
        case SyntaxKind::AssumePropertyStatement:
        case SyntaxKind::CoverPropertyStatement:
        case SyntaxKind::ExpectPropertyStatement:
        case SyntaxKind::CoverSequenceStatement:
        case SyntaxKind::RestrictPropertyStatement:
            result = &ConcurrentAssertionStatement::fromSyntax(
                comp, syntax.as<ConcurrentAssertionStatementSyntax>(), context, stmtCtx);
            break;
        case SyntaxKind::RandCaseStatement:
            result = &RandCaseStatement::fromSyntax(comp, syntax.as<RandCaseStatementSyntax>(),
                                                    context, stmtCtx);
            break;
        case SyntaxKind::RandSequenceStatement:
            // We might have an implicit block here; check for that first.
            if (auto block = stmtCtx.tryGetBlock(context, syntax))
                return *block;

            result = &RandSequenceStatement::fromSyntax(comp,
                                                        syntax.as<RandSequenceStatementSyntax>(),
                                                        context);
            break;
        case SyntaxKind::CheckerInstanceStatement:
            result = &ProceduralCheckerStatement::fromSyntax(
                comp, syntax.as<CheckerInstanceStatementSyntax>(), context);
            break;
        default:
            SLANG_UNREACHABLE;
    }

    result->syntax = &syntax;
    context.setAttributes(*result, syntax.attributes);
    return *result;
}

static BlockStatement* createBlockStatement(
    Compilation& comp, SmallVectorBase<const Statement*>& buffer, const SyntaxNode& syntax,
    StatementBlockKind blocKind = StatementBlockKind::Sequential) {

    const Statement* body;
    if (buffer.size() == 1)
        body = buffer[0];
    else
        body = comp.emplace<StatementList>(buffer.copy(comp), syntax.sourceRange());

    return comp.emplace<BlockStatement>(*body, blocKind, body->sourceRange);
}

const Statement& Statement::bindBlock(const StatementBlockSymbol& block, const SyntaxNode& syntax,
                                      const ASTContext& context, StatementContext& stmtCtx) {
    BlockStatement* result;
    bool anyBad = false;
    auto& comp = context.getCompilation();

    if (syntax.kind == SyntaxKind::SequentialBlockStatement ||
        syntax.kind == SyntaxKind::ParallelBlockStatement) {
        auto& bss = syntax.as<BlockStatementSyntax>();
        auto& bs = BlockStatement::fromSyntax(comp, bss, context, stmtCtx,
                                              /* addInitializers */ true);
        if (bs.bad())
            return bs;

        result = &bs.as<BlockStatement>();
        result->syntax = &bss;
        context.setAttributes(*result, bss.attributes);
    }
    else if (syntax.kind == SyntaxKind::RsCodeBlock) {
        SmallVector<const Statement*> buffer;
        bindScopeInitializers(context, buffer);

        for (auto item : syntax.as<RsCodeBlockSyntax>().items) {
            if (StatementSyntax::isKind(item->kind)) {
                auto& stmt = bind(item->as<StatementSyntax>(), context, stmtCtx,
                                  /* inList */ true);
                buffer.push_back(&stmt);
                anyBad |= stmt.bad();
            }
        }

        result = createBlockStatement(comp, buffer, syntax);
    }
    else {
        SmallVector<const Statement*> buffer;
        bindScopeInitializers(context, buffer);

        const StatementSyntax* ss;
        if (syntax.kind == SyntaxKind::PatternCaseItem)
            ss = syntax.as<PatternCaseItemSyntax>().statement;
        else
            ss = &syntax.as<StatementSyntax>();
        auto& stmt = bind(*ss, context, stmtCtx, /* inList */ false,
                          /* labelHandled */ true);
        buffer.push_back(&stmt);
        anyBad |= stmt.bad();

        result = createBlockStatement(comp, buffer, syntax);
        result->syntax = ss;
        context.setAttributes(*result, ss->attributes);
    }

    result->blockSymbol = &block;
    if (anyBad)
        return badStmt(comp, result);

    return *result;
}

const Statement& Statement::bindItems(const SyntaxList<SyntaxNode>& items,
                                      const ASTContext& context, StatementContext& stmtCtx) {
    SmallVector<const Statement*> buffer;
    bindScopeInitializers(context, buffer);

    for (auto item : items) {
        if (StatementSyntax::isKind(item->kind)) {
            buffer.push_back(&bind(item->as<StatementSyntax>(), context, stmtCtx,
                                   /* inList */ true));
        }
    }

    if (buffer.size() == 1)
        return *buffer[0];

    auto& comp = context.getCompilation();
    return *comp.emplace<StatementList>(buffer.copy(comp), SourceRange());
}

void Statement::bindScopeInitializers(const ASTContext& context,
                                      SmallVectorBase<const Statement*>& results) {
    // This relies on the language requiring all declarations be at the
    // start of a statement block. Additional work would be required to
    // support declarations anywhere in the block, because as written all
    // of the initialization will happen at the start of the block, which
    // might have different side-effects than if they were initialized in
    // the middle somewhere. The parser currently enforces this for us.
    auto& scope = *context.scope;
    auto& comp = scope.getCompilation();
    for (auto& member : scope.members()) {
        if (member.kind != SymbolKind::Variable)
            continue;

        // Filter out implicitly generated function return type variables -- they are
        // initialized elsewhere. Note that we manufacture a somewhat reasonable
        // source range here, since we don't have the real one.
        auto& var = member.as<VariableSymbol>();
        if (!var.flags.has(VariableFlags::CompilerGenerated)) {
            SourceRange range{var.location, var.location + var.name.length()};
            results.push_back(comp.emplace<VariableDeclStatement>(var, range));
        }
    }
}

Statement& Statement::badStmt(Compilation& compilation, const Statement* stmt) {
    return *compilation.emplace<InvalidStatement>(stmt);
}

static void findBlocks(const Scope& scope, const StatementSyntax& syntax,
                       SmallVectorBase<const StatementBlockSymbol*>& results,
                       SmallVector<const SyntaxNode*>& extraMembers, bool labelHandled) {
    if (!labelHandled && hasSimpleLabel(syntax)) {
        results.push_back(&StatementBlockSymbol::fromLabeledStmt(scope, syntax));
        return;
    }

    auto recurse = [&](auto stmt) {
        findBlocks(scope, *stmt, results, extraMembers, /* lableHandled */ false);
    };

    switch (syntax.kind) {
        case SyntaxKind::ReturnStatement:
        case SyntaxKind::JumpStatement:
        case SyntaxKind::ProceduralAssignStatement:
        case SyntaxKind::ProceduralForceStatement:
        case SyntaxKind::ProceduralDeassignStatement:
        case SyntaxKind::ProceduralReleaseStatement:
        case SyntaxKind::DisableStatement:
        case SyntaxKind::DisableForkStatement:
        case SyntaxKind::EmptyStatement:
        case SyntaxKind::BlockingEventTriggerStatement:
        case SyntaxKind::NonblockingEventTriggerStatement:
        case SyntaxKind::ExpressionStatement:
        case SyntaxKind::WaitForkStatement:
        case SyntaxKind::VoidCastedCallStatement:
            // These statements don't have child statements within them.
            return;

        case SyntaxKind::SequentialBlockStatement:
        case SyntaxKind::ParallelBlockStatement: {
            // Block statements form their own hierarchy scope if:
            // - They have a name (or a label)
            // - They are unnamed but have variable declarations within them
            auto& block = syntax.as<BlockStatementSyntax>();
            if (block.blockName || block.label) {
                results.push_back(&StatementBlockSymbol::fromSyntax(scope, block));
                return;
            }

            for (auto item : block.items) {
                // If we find any decls at all, this block gets its own scope.
                if (!StatementSyntax::isKind(item->kind)) {
                    results.push_back(&StatementBlockSymbol::fromSyntax(scope, block));
                    return;
                }
            }

            for (auto item : block.items)
                recurse(&item->as<StatementSyntax>());
            return;
        }

        case SyntaxKind::CaseStatement:
            for (auto item : syntax.as<CaseStatementSyntax>().items) {
                switch (item->kind) {
                    case SyntaxKind::StandardCaseItem:
                        recurse(&item->as<StandardCaseItemSyntax>().clause->as<StatementSyntax>());
                        break;
                    case SyntaxKind::PatternCaseItem:
                        // Pattern case items always create a block.
                        results.push_back(&StatementBlockSymbol::fromSyntax(
                            scope, item->as<PatternCaseItemSyntax>()));
                        break;
                    case SyntaxKind::DefaultCaseItem:
                        recurse(&item->as<DefaultCaseItemSyntax>().clause->as<StatementSyntax>());
                        break;
                    default:
                        SLANG_UNREACHABLE;
                }
            }
            return;
        case SyntaxKind::ConditionalStatement: {
            auto& cond = syntax.as<ConditionalStatementSyntax>();
            bool hasPattern = false;
            for (auto condSyntax : cond.predicate->conditions) {
                if (condSyntax->matchesClause) {
                    hasPattern = true;
                    break;
                }
            }

            // If any condition has a pattern, we need a block.
            if (hasPattern)
                results.push_back(&StatementBlockSymbol::fromSyntax(scope, cond));
            else
                recurse(cond.statement);

            if (cond.elseClause)
                recurse(&cond.elseClause->clause->as<StatementSyntax>());
            return;
        }
        case SyntaxKind::ForeverStatement:
            recurse(syntax.as<ForeverStatementSyntax>().statement);
            return;
        case SyntaxKind::LoopStatement:
            recurse(syntax.as<LoopStatementSyntax>().statement);
            return;
        case SyntaxKind::DoWhileStatement:
            recurse(syntax.as<DoWhileStatementSyntax>().statement);
            return;
        case SyntaxKind::ForLoopStatement: {
            // For loops are special; if they declare variables, they get
            // wrapped in an implicit block. Otherwise they are transparent.
            auto& forLoop = syntax.as<ForLoopStatementSyntax>();
            if (!forLoop.initializers.empty() &&
                forLoop.initializers[0]->kind == SyntaxKind::ForVariableDeclaration) {
                results.push_back(&StatementBlockSymbol::fromSyntax(scope, forLoop));
            }
            else if (syntax.label) {
                results.push_back(&StatementBlockSymbol::fromLabeledStmt(scope, syntax));
            }
            else {
                recurse(forLoop.statement);
            }
            return;
        }
        case SyntaxKind::ForeachLoopStatement:
            // A foreach loop always creates a block, but we need to check labelHandled
            // here to make sure we don't infinitely recurse.
            if (!labelHandled) {
                results.push_back(&StatementBlockSymbol::fromSyntax(
                    scope, syntax.as<ForeachLoopStatementSyntax>()));
            }
            else {
                recurse(syntax.as<ForeachLoopStatementSyntax>().statement);
            }
            return;
        case SyntaxKind::TimingControlStatement:
            recurse(syntax.as<TimingControlStatementSyntax>().statement);
            return;
        case SyntaxKind::WaitStatement:
            recurse(syntax.as<WaitStatementSyntax>().statement);
            return;
        case SyntaxKind::RandCaseStatement:
            for (auto item : syntax.as<RandCaseStatementSyntax>().items)
                recurse(item->statement);
            return;
        case SyntaxKind::ImmediateAssertStatement:
        case SyntaxKind::ImmediateAssumeStatement:
        case SyntaxKind::ImmediateCoverStatement: {
            auto& ias = syntax.as<ImmediateAssertionStatementSyntax>();
            if (ias.action->statement)
                recurse(ias.action->statement);
            if (ias.action->elseClause)
                recurse(&ias.action->elseClause->clause->as<StatementSyntax>());
            return;
        }
        case SyntaxKind::AssertPropertyStatement:
        case SyntaxKind::AssumePropertyStatement:
        case SyntaxKind::CoverPropertyStatement:
        case SyntaxKind::CoverSequenceStatement:
        case SyntaxKind::RestrictPropertyStatement:
        case SyntaxKind::ExpectPropertyStatement: {
            auto& ias = syntax.as<ConcurrentAssertionStatementSyntax>();
            if (ias.action->statement)
                recurse(ias.action->statement);
            if (ias.action->elseClause)
                recurse(&ias.action->elseClause->clause->as<StatementSyntax>());
            return;
        }
        case SyntaxKind::WaitOrderStatement: {
            auto& wos = syntax.as<WaitOrderStatementSyntax>();
            if (wos.action->statement)
                recurse(wos.action->statement);
            if (wos.action->elseClause)
                recurse(&wos.action->elseClause->clause->as<StatementSyntax>());
            return;
        }
        case SyntaxKind::RandSequenceStatement:
            // A randsequence statement always creates a block, but we need to check
            // labelHandled here to make sure we don't infinitely recurse.
            if (!labelHandled) {
                results.push_back(&StatementBlockSymbol::fromSyntax(
                    scope, syntax.as<RandSequenceStatementSyntax>()));
            }
            return;
        case SyntaxKind::CheckerInstanceStatement:
            // We have an extra parameter just for collecting these checker syntax
            // nodes; the caller will handle adding them to the parent scope.
            extraMembers.push_back(syntax.as<CheckerInstanceStatementSyntax>().instance);
            break;
        default:
            SLANG_UNREACHABLE;
    }
}

std::span<const StatementBlockSymbol* const> Statement::createAndAddBlockItems(
    Scope& scope, const SyntaxList<SyntaxNode>& items) {

    SmallVector<const StatementBlockSymbol*> buffer;
    SmallVector<const SyntaxNode*> extraMembers;
    for (auto item : items) {
        switch (item->kind) {
            case SyntaxKind::DataDeclaration:
            case SyntaxKind::TypedefDeclaration:
            case SyntaxKind::ForwardTypedefDeclaration:
            case SyntaxKind::PackageImportDeclaration:
            case SyntaxKind::ParameterDeclarationStatement:
            case SyntaxKind::LetDeclaration:
            case SyntaxKind::NetTypeDeclaration:
                scope.addMembers(*item);
                break;
            case SyntaxKind::PortDeclaration:
                if (item->previewNode)
                    scope.addMembers(*item->previewNode);

                if (scope.asSymbol().kind == SymbolKind::Subroutine) {
                    SmallVector<const FormalArgumentSymbol*> args;
                    FormalArgumentSymbol::fromSyntax(scope, item->as<PortDeclarationSyntax>(),
                                                     args);
                    for (auto arg : args)
                        scope.addMember(*arg);
                }
                else {
                    scope.addDiag(diag::UnexpectedPortDecl, item->sourceRange());
                }
                break;
            default:
                findBlocks(scope, item->as<StatementSyntax>(), buffer, extraMembers, false);
                break;
        }
    }

    auto blocks = buffer.copy(scope.getCompilation());
    for (auto block : blocks)
        scope.addMember(*block);
    for (auto member : extraMembers)
        scope.addMembers(*member);

    return blocks;
}

std::span<const StatementBlockSymbol* const> Statement::createBlockItems(
    const Scope& scope, const StatementSyntax& syntax, bool labelHandled,
    SmallVector<const SyntaxNode*>& extraMembers) {

    SmallVector<const StatementBlockSymbol*> buffer;
    findBlocks(scope, syntax, buffer, extraMembers, labelHandled);
    return buffer.copy(scope.getCompilation());
}

std::span<const StatementBlockSymbol* const> Statement::createAndAddBlockItems(
    Scope& scope, const StatementSyntax& syntax, bool labelHandled) {

    SmallVector<const SyntaxNode*> extraMembers;
    auto blocks = createBlockItems(scope, syntax, labelHandled, extraMembers);
    for (auto block : blocks)
        scope.addMember(*block);
    for (auto member : extraMembers)
        scope.addMembers(*member);

    return blocks;
}

ER StatementList::evalImpl(EvalContext& context) const {
    for (auto item : list) {
        ER result = item->eval(context);
        if (result != ER::Success)
            return result;
    }

    return ER::Success;
}

void StatementList::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("list");
    for (auto stmt : list) {
        serializer.serialize(*stmt);
    }
    serializer.endArray();
}

Statement& StatementList::makeEmpty(Compilation& compilation) {
    return *compilation.emplace<StatementList>(std::span<const Statement* const>(),
                                               SourceRange(SourceLocation::NoLocation,
                                                           SourceLocation::NoLocation));
}

Statement& BlockStatement::fromSyntax(Compilation& comp, const BlockStatementSyntax& syntax,
                                      const ASTContext& sourceCtx, StatementContext& stmtCtx,
                                      bool addInitializers) {
    ASTContext context = sourceCtx;
    auto blockKind = SemanticFacts::getStatementBlockKind(syntax);
    if (context.flags.has(ASTFlags::Function | ASTFlags::Final)) {
        if (blockKind == StatementBlockKind::JoinAll || blockKind == StatementBlockKind::JoinAny) {
            context.addDiag(diag::TimingInFuncNotAllowed, syntax.end.range());
            return badStmt(comp, nullptr);
        }
        else if (blockKind == StatementBlockKind::JoinNone) {
            // The "function body" flag does not propagate through fork-join_none
            // blocks, as all statements are allowed in those.
            context.flags &= ~ASTFlags::Function & ~ASTFlags::Final;
        }
    }
    else if (blockKind != StatementBlockKind::Sequential && context.inAlwaysCombLatch()) {
        auto proc = context.getProceduralBlock();
        SLANG_ASSERT(proc);
        context.addDiag(diag::ForkJoinAlwaysComb, syntax.begin.range())
            << SemanticFacts::getProcedureKindStr(proc->procedureKind);
        return badStmt(comp, nullptr);
    }

    // When entering a fork-join we clear any active loop flags, since the new
    // forked processes are effectively not in that loop (and statements like
    // continue and break do not apply to the outer loop).
    auto guard = ScopeGuard([&stmtCtx, savedFlags = stmtCtx.flags] {
        const auto savableFlags = StatementFlags::InLoop | StatementFlags::InForLoop |
                                  StatementFlags::InForkJoin;
        stmtCtx.flags &= ~savableFlags;
        stmtCtx.flags |= savedFlags & savableFlags;
    });

    if (blockKind != StatementBlockKind::Sequential) {
        stmtCtx.flags |= StatementFlags::InForkJoin;
        stmtCtx.flags &= ~(StatementFlags::InLoop | StatementFlags::InForLoop);
    }

    bool anyBad = false;
    SmallVector<const Statement*> buffer;

    if (addInitializers)
        bindScopeInitializers(context, buffer);

    if (blockKind == StatementBlockKind::JoinAny || blockKind == StatementBlockKind::JoinNone)
        context.flags |= ASTFlags::ForkJoinAnyNone;

    for (auto item : syntax.items) {
        if (StatementSyntax::isKind(item->kind)) {
            auto& stmt = Statement::bind(item->as<StatementSyntax>(), context, stmtCtx,
                                         /* inList */ true);
            buffer.push_back(&stmt);
            anyBad |= stmt.bad();
        }
    }

    auto result = createBlockStatement(comp, buffer, syntax, blockKind);
    if (anyBad)
        return badStmt(comp, result);

    return *result;
}

BlockStatement& BlockStatement::makeEmpty(Compilation& compilation) {
    return *compilation.emplace<BlockStatement>(
        StatementList::makeEmpty(compilation), StatementBlockKind::Sequential,
        SourceRange(SourceLocation::NoLocation, SourceLocation::NoLocation));
}

void BlockStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("blockKind", toString(blockKind));
    if (blockSymbol)
        serializer.writeLink("block", *blockSymbol);
    serializer.write("body", body);
}

ER BlockStatement::evalImpl(EvalContext& context) const {
    if (blockKind != StatementBlockKind::Sequential) {
        context.addDiag(diag::ConstEvalParallelBlockNotConst, sourceRange);
        return ER::Fail;
    }

    ER result = body.eval(context);
    if (result == ER::Disable) {
        // Check if the disable statement we evaluated was targeting this block.
        // If it was, we've already skipped enough statements, so just clear out
        // the target and continue on.
        auto target = context.getDisableTarget();
        SLANG_ASSERT(target);
        if (target == blockSymbol) {
            result = ER::Success;
            context.setDisableTarget(nullptr, {});
        }
    }

    return result;
}

} // namespace slang::ast
