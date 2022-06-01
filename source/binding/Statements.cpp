//------------------------------------------------------------------------------
// Statements.cpp
// Statement creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/Statements.h"

#include "slang/binding/CallExpression.h"
#include "slang/binding/Expression.h"
#include "slang/binding/SystemSubroutine.h"
#include "slang/binding/TimingControl.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/ASTVisitor.h"
#include "slang/syntax/AllSyntax.h"

namespace {

using namespace slang;
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

    ER visitInvalid(const Statement&, EvalContext&) { return ER::Fail; }
};

} // namespace

namespace slang {

const InvalidStatement InvalidStatement::Instance(nullptr);

void InvalidStatement::serializeTo(ASTSerializer& serializer) const {
    if (child)
        serializer.write("child", *child);
}

ER Statement::eval(EvalContext& context) const {
    EvalVisitor visitor;
    return visit(visitor, context);
}

const Statement* Statement::StatementContext::tryGetBlock(const BindContext& context,
                                                          StatementContext& stmtCtx,
                                                          const SyntaxNode& syntax) {
    if (!blocks.empty() && blocks[0]->getSyntax() == &syntax) {
        auto& result = blocks[0]->getStatement(context, stmtCtx);
        blocks = blocks.subspan(1);
        return &result;
    }
    return nullptr;
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

const Statement& Statement::bind(const StatementSyntax& syntax, const BindContext& context,
                                 StatementContext& stmtCtx, bool inList, bool labelHandled) {
    auto& comp = context.getCompilation();

    if (!labelHandled && hasSimpleLabel(syntax)) {
        auto block = stmtCtx.tryGetBlock(context, stmtCtx, syntax);
        ASSERT(block);
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
            result =
                &DisableStatement::fromSyntax(comp, syntax.as<DisableStatementSyntax>(), context);
            break;
        case SyntaxKind::ConditionalStatement:
            result = &ConditionalStatement::fromSyntax(
                comp, syntax.as<ConditionalStatementSyntax>(), context, stmtCtx);
            break;
        case SyntaxKind::CaseStatement:
            result = &CaseStatement::fromSyntax(comp, syntax.as<CaseStatementSyntax>(), context,
                                                stmtCtx);
            break;
        case SyntaxKind::ForLoopStatement:
            // We might have an implicit block here; check for that first.
            if (auto block = stmtCtx.tryGetBlock(context, stmtCtx, syntax))
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
            if (auto block = stmtCtx.tryGetBlock(context, stmtCtx, syntax))
                return *block;

            result = &ForeachLoopStatement::fromSyntax(
                comp, syntax.as<ForeachLoopStatementSyntax>(), context, stmtCtx);
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
            result = &ExpressionStatement::fromSyntax(
                comp, syntax.as<VoidCastedCallStatementSyntax>(), context);
            break;
        case SyntaxKind::SequentialBlockStatement:
        case SyntaxKind::ParallelBlockStatement:
            // A block statement may or may not match up with a hierarchy node. Handle both cases
            // here. We traverse statements in the same order as the findBlocks call below, so this
            // should always sync up exactly.
            if (auto block = stmtCtx.tryGetBlock(context, stmtCtx, syntax))
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
            result =
                &DisableForkStatement::fromSyntax(comp, syntax.as<DisableForkStatementSyntax>());
            break;
        case SyntaxKind::WaitStatement:
            result = &WaitStatement::fromSyntax(comp, syntax.as<WaitStatementSyntax>(), context,
                                                stmtCtx);
            break;
        case SyntaxKind::WaitForkStatement:
            result = &WaitForkStatement::fromSyntax(comp, syntax.as<WaitForkStatementSyntax>());
            break;
        case SyntaxKind::WaitOrderStatement:
            result = &WaitOrderStatement::fromSyntax(comp, syntax.as<WaitOrderStatementSyntax>(),
                                                     context, stmtCtx);
            break;
        case SyntaxKind::BlockingEventTriggerStatement:
        case SyntaxKind::NonblockingEventTriggerStatement:
            result = &EventTriggerStatement::fromSyntax(
                comp, syntax.as<EventTriggerStatementSyntax>(), context);
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
            if (auto block = stmtCtx.tryGetBlock(context, stmtCtx, syntax))
                return *block;

            result = &RandSequenceStatement::fromSyntax(
                comp, syntax.as<RandSequenceStatementSyntax>(), context);
            break;
        default:
            THROW_UNREACHABLE;
    }

    result->syntax = &syntax;
    context.setAttributes(*result, syntax.attributes);
    return *result;
}

static BlockStatement* createBlockStatement(
    Compilation& comp, SmallVector<const Statement*>& buffer, const SyntaxNode& syntax,
    StatementBlockKind blocKind = StatementBlockKind::Sequential) {

    const Statement* body;
    if (buffer.size() == 1)
        body = buffer[0];
    else
        body = comp.emplace<StatementList>(buffer.copy(comp), syntax.sourceRange());

    return comp.emplace<BlockStatement>(*body, blocKind, body->sourceRange);
}

const Statement& Statement::bindBlock(const StatementBlockSymbol& block, const SyntaxNode& syntax,
                                      const BindContext& context, StatementContext& stmtCtx) {
    BlockStatement* result;
    auto& comp = context.getCompilation();

    if (syntax.kind == SyntaxKind::SequentialBlockStatement ||
        syntax.kind == SyntaxKind::ParallelBlockStatement) {
        auto& bss = syntax.as<BlockStatementSyntax>();
        auto& bs =
            BlockStatement::fromSyntax(comp, bss, context, stmtCtx, /* addInitializers */ true);
        if (bs.bad())
            return bs;

        result = &bs.as<BlockStatement>();
        result->syntax = &bss;
        context.setAttributes(*result, bss.attributes);
    }
    else if (syntax.kind == SyntaxKind::RsCodeBlock) {
        SmallVectorSized<const Statement*, 8> buffer;
        bindScopeInitializers(context, buffer);

        for (auto item : syntax.as<RsCodeBlockSyntax>().items) {
            if (StatementSyntax::isKind(item->kind)) {
                buffer.append(&bind(item->as<StatementSyntax>(), context, stmtCtx,
                                    /* inList */ true));
            }
        }

        result = createBlockStatement(comp, buffer, syntax);
    }
    else {
        SmallVectorSized<const Statement*, 8> buffer;
        bindScopeInitializers(context, buffer);

        auto& ss = syntax.as<StatementSyntax>();
        buffer.append(&bind(ss, context, stmtCtx, /* inList */ false,
                            /* labelHandled */ true));

        result = createBlockStatement(comp, buffer, syntax);
        result->syntax = &ss;
        context.setAttributes(*result, ss.attributes);
    }

    result->blockSymbol = &block;
    return *result;
}

void Statement::bindScopeInitializers(const BindContext& context,
                                      SmallVector<const Statement*>& results) {
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
            SourceRange range{ var.location, var.location + var.name.length() };
            results.append(comp.emplace<VariableDeclStatement>(var, range));
        }
    }
}

Statement& Statement::badStmt(Compilation& compilation, const Statement* stmt) {
    return *compilation.emplace<InvalidStatement>(stmt);
}

static void findBlocks(const Scope& scope, const StatementSyntax& syntax,
                       SmallVector<const StatementBlockSymbol*>& results, bool labelHandled,
                       bitmask<StatementFlags> flags) {
    if (!labelHandled && hasSimpleLabel(syntax)) {
        results.append(&StatementBlockSymbol::fromLabeledStmt(scope, syntax, flags));
        return;
    }

    auto recurse = [&](auto stmt) {
        findBlocks(scope, *stmt, results, /* lableHandled */ false, flags);
    };

    auto recurseF = [&](auto stmt, auto extraFlags) {
        findBlocks(scope, *stmt, results, /* lableHandled */ false, flags | extraFlags);
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
                results.append(&StatementBlockSymbol::fromSyntax(scope, block, flags));
                return;
            }

            for (auto item : block.items) {
                // If we find any decls at all, this block gets its own scope.
                if (!StatementSyntax::isKind(item->kind)) {
                    results.append(&StatementBlockSymbol::fromSyntax(scope, block, flags));
                    return;
                }
            }

            StatementFlags extra = StatementFlags::None;
            if (SemanticFacts::getStatementBlockKind(block) == StatementBlockKind::JoinNone)
                extra = StatementFlags::InForkJoinNone;

            for (auto item : block.items)
                recurseF(&item->as<StatementSyntax>(), extra);
            return;
        }

        case SyntaxKind::CaseStatement:
            for (auto item : syntax.as<CaseStatementSyntax>().items) {
                switch (item->kind) {
                    case SyntaxKind::StandardCaseItem:
                        recurse(&item->as<StandardCaseItemSyntax>().clause->as<StatementSyntax>());
                        break;
                    case SyntaxKind::PatternCaseItem:
                        recurse(item->as<PatternCaseItemSyntax>().statement);
                        break;
                    case SyntaxKind::DefaultCaseItem:
                        recurse(&item->as<DefaultCaseItemSyntax>().clause->as<StatementSyntax>());
                        break;
                    default:
                        THROW_UNREACHABLE;
                }
            }
            return;
        case SyntaxKind::ConditionalStatement: {
            auto& cond = syntax.as<ConditionalStatementSyntax>();
            recurse(cond.statement);
            if (cond.elseClause)
                recurse(&cond.elseClause->clause->as<StatementSyntax>());
            return;
        }
        case SyntaxKind::ForeverStatement:
            recurseF(syntax.as<ForeverStatementSyntax>().statement, StatementFlags::InLoop);
            return;
        case SyntaxKind::LoopStatement:
            recurseF(syntax.as<LoopStatementSyntax>().statement, StatementFlags::InLoop);
            return;
        case SyntaxKind::DoWhileStatement:
            recurseF(syntax.as<DoWhileStatementSyntax>().statement, StatementFlags::InLoop);
            return;
        case SyntaxKind::ForLoopStatement: {
            // For loops are special; if they declare variables, they get
            // wrapped in an implicit block. Otherwise they are transparent.
            auto& forLoop = syntax.as<ForLoopStatementSyntax>();
            if (!forLoop.initializers.empty() &&
                forLoop.initializers[0]->kind == SyntaxKind::ForVariableDeclaration) {
                results.append(&StatementBlockSymbol::fromSyntax(scope, forLoop, flags));
            }
            else if (syntax.label) {
                results.append(&StatementBlockSymbol::fromLabeledStmt(scope, syntax, flags));
            }
            else {
                recurseF(forLoop.statement, StatementFlags::InLoop);
            }
            return;
        }
        case SyntaxKind::ForeachLoopStatement:
            // A foreach loop always creates a block, but we need to check labelHandled
            // here to make sure we don't infinitely recurse.
            if (!labelHandled) {
                results.append(&StatementBlockSymbol::fromSyntax(
                    scope, syntax.as<ForeachLoopStatementSyntax>(), flags));
            }
            else {
                recurseF(syntax.as<ForeachLoopStatementSyntax>().statement, StatementFlags::InLoop);
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
                results.append(&StatementBlockSymbol::fromSyntax(
                    scope, syntax.as<RandSequenceStatementSyntax>()));
            }
            return;
        default:
            THROW_UNREACHABLE;
    }
}

span<const StatementBlockSymbol* const> Statement::createBlockItems(
    Scope& scope, const SyntaxList<SyntaxNode>& items, bitmask<StatementFlags> flags) {

    SmallVectorSized<const StatementBlockSymbol*, 8> buffer;
    for (auto item : items) {
        switch (item->kind) {
            case SyntaxKind::DataDeclaration:
            case SyntaxKind::TypedefDeclaration:
            case SyntaxKind::ForwardTypedefDeclaration:
            case SyntaxKind::ForwardInterfaceClassTypedefDeclaration:
            case SyntaxKind::PackageImportDeclaration:
            case SyntaxKind::ParameterDeclarationStatement:
            case SyntaxKind::LetDeclaration:
            case SyntaxKind::NetTypeDeclaration:
                scope.addMembers(*item);
                break;
            case SyntaxKind::PortDeclaration:
                if (scope.asSymbol().kind == SymbolKind::Subroutine) {
                    SmallVectorSized<const FormalArgumentSymbol*, 8> args;
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
                findBlocks(scope, item->as<StatementSyntax>(), buffer, false, flags);
                break;
        }
    }

    auto blocks = buffer.copy(scope.getCompilation());
    for (auto block : blocks)
        scope.addMember(*block);

    return blocks;
}

span<const StatementBlockSymbol* const> Statement::createBlockItems(Scope& scope,
                                                                    const StatementSyntax& syntax,
                                                                    bool labelHandled,
                                                                    bitmask<StatementFlags> flags) {
    SmallVectorSized<const StatementBlockSymbol*, 8> buffer;
    findBlocks(scope, syntax, buffer, labelHandled, flags);

    auto blocks = buffer.copy(scope.getCompilation());
    for (auto block : blocks)
        scope.addMember(*block);

    return blocks;
}

void StatementBinder::setSyntax(const Scope& scope, const StatementSyntax& syntax_,
                                bool labelHandled_, bitmask<StatementFlags> flags_) {
    stmt = nullptr;
    syntax = &syntax_;
    labelHandled = labelHandled_;
    flags = flags_;

    SmallVectorSized<const StatementBlockSymbol*, 8> buffer;
    findBlocks(scope, syntax_, buffer, labelHandled, flags);
    blocks = buffer.copy(scope.getCompilation());
}

void StatementBinder::setSyntax(const StatementBlockSymbol& scope,
                                const ForLoopStatementSyntax& syntax_,
                                bitmask<StatementFlags> flags_) {
    stmt = nullptr;
    syntax = &syntax_;
    labelHandled = false;
    flags = flags_;

    SmallVectorSized<const StatementBlockSymbol*, 8> buffer;
    findBlocks(scope, *syntax_.statement, buffer, labelHandled,
               flags | StatementFlags::InLoop | StatementFlags::InForLoop);

    blocks = buffer.copy(scope.getCompilation());
}

void StatementBinder::setItems(Scope& scope, const SyntaxNode& syntax_,
                               const SyntaxList<SyntaxNode>& items,
                               bitmask<StatementFlags> flags_) {
    stmt = nullptr;
    syntax = &syntax_;
    labelHandled = false;
    isItems = true;
    flags = flags_;
    blocks = Statement::createBlockItems(scope, items, flags);
}

const Statement& StatementBinder::getStatement(const BindContext& context) const {
    if (!stmt) {
        // Avoid issues with recursive function calls re-entering this
        // method while we're still binding.
        if (isBinding)
            return InvalidStatement::Instance;

        isBinding = true;
        auto guard = ScopeGuard([this] { isBinding = false; });

        BindContext ctx = context;
        if (!flags.has(StatementFlags::InForkJoinNone)) {
            if (flags.has(StatementFlags::Func))
                ctx.flags |= BindFlags::Function;
            if (flags.has(StatementFlags::Final))
                ctx.flags |= BindFlags::Final;
        }

        stmt = &bindStatement(ctx);
    }

    return *stmt;
}

const Statement& StatementBinder::bindStatement(const BindContext& context) const {
    auto& scope = *context.scope;
    auto& comp = scope.getCompilation();
    SmallVectorSized<const Statement*, 8> buffer;

    auto scopeKind = scope.asSymbol().kind;
    if (scopeKind == SymbolKind::StatementBlock || scopeKind == SymbolKind::Subroutine) {
        // This relies on the language requiring all declarations be at the
        // start of a statement block. Additional work would be required to
        // support declarations anywhere in the block, because as written all
        // of the initialization will happen at the start of the block, which
        // might have different side-effects than if they were initialized in
        // the middle somewhere. The parser currently enforces this for us.
        for (auto& member : scope.members()) {
            if (member.kind != SymbolKind::Variable)
                continue;

            // Filter out implicitly generated function return type variables -- they are
            // initialized elsewhere. Note that we manufacture a somewhat reasonable
            // source range here, since we don't have the real one.
            auto& var = member.as<VariableSymbol>();
            SourceRange range{ var.location, var.location + var.name.length() };
            if (!var.flags.has(VariableFlags::CompilerGenerated))
                buffer.append(comp.emplace<VariableDeclStatement>(var, range));
        }
    }

    bool anyBad = false;
    SourceRange sourceRange;
    Statement::StatementContext stmtCtx;
    stmtCtx.blocks = blocks;
    stmtCtx.flags = flags;

    if (isItems) {
        ASSERT(syntax);
        sourceRange = syntax->sourceRange();

        const SyntaxList<SyntaxNode>* items;
        switch (syntax->kind) {
            case SyntaxKind::RsCodeBlock:
                items = &syntax->as<RsCodeBlockSyntax>().items;
                break;
            case SyntaxKind::ParallelBlockStatement:
            case SyntaxKind::SequentialBlockStatement:
                items = &syntax->as<BlockStatementSyntax>().items;
                break;
            case SyntaxKind::FunctionDeclaration:
            case SyntaxKind::TaskDeclaration:
                items = &syntax->as<FunctionDeclarationSyntax>().items;
                break;
            default:
                THROW_UNREACHABLE;
        }

        for (auto item : *items) {
            if (StatementSyntax::isKind(item->kind)) {
                buffer.append(&Statement::bind(item->as<StatementSyntax>(), context, stmtCtx,
                                               /* inList */ true));
                anyBad |= buffer.back()->bad();
            }
        }
    }
    else if (syntax) {
        sourceRange = syntax->sourceRange();
        buffer.append(&Statement::bind(syntax->as<StatementSyntax>(), context, stmtCtx,
                                       /* inList */ false, labelHandled));
        anyBad |= buffer.back()->bad();
    }
    else {
        sourceRange = { SourceLocation::NoLocation, SourceLocation::NoLocation };
    }

    ASSERT(anyBad || stmtCtx.blocks.empty());

    if (buffer.size() == 1)
        return *buffer[0];

    if (anyBad)
        return InvalidStatement::Instance;

    return *comp.emplace<StatementList>(buffer.copy(comp), sourceRange);
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

Statement& BlockStatement::fromSyntax(Compilation& comp, const BlockStatementSyntax& syntax,
                                      const BindContext& sourceCtx, StatementContext& stmtCtx,
                                      bool addInitializers) {
    BindContext context = sourceCtx;
    auto blockKind = SemanticFacts::getStatementBlockKind(syntax);
    if (context.flags.has(BindFlags::Function | BindFlags::Final)) {
        if (blockKind == StatementBlockKind::JoinAll || blockKind == StatementBlockKind::JoinAny) {
            context.addDiag(diag::TimingInFuncNotAllowed, syntax.end.range());
            return badStmt(comp, nullptr);
        }
        else if (blockKind == StatementBlockKind::JoinNone) {
            // The "function body" flag does not propagate through fork-join_none
            // blocks, as all statements are allowed in those.
            context.flags &= ~BindFlags::Function & ~BindFlags::Final;
        }
    }
    else if (blockKind != StatementBlockKind::Sequential && context.inAlwaysCombLatch()) {
        auto proc = context.getProceduralBlock();
        ASSERT(proc);
        context.addDiag(diag::ForkJoinAlwaysComb, syntax.begin.range())
            << SemanticFacts::getProcedureKindStr(proc->procedureKind);
        return badStmt(comp, nullptr);
    }

    bool wasInForkJoin = stmtCtx.flags.has(StatementFlags::InForkJoin);
    if (blockKind != StatementBlockKind::Sequential)
        stmtCtx.flags |= StatementFlags::InForkJoin;

    bool anyBad = false;
    SmallVectorSized<const Statement*, 8> buffer;

    if (addInitializers)
        bindScopeInitializers(context, buffer);

    for (auto item : syntax.items) {
        if (StatementSyntax::isKind(item->kind)) {
            auto& stmt =
                Statement::bind(item->as<StatementSyntax>(), context, stmtCtx, /* inList */ true);
            buffer.append(&stmt);
            anyBad |= stmt.bad();
        }
    }

    auto result = createBlockStatement(comp, buffer, syntax, blockKind);

    if (blockKind != StatementBlockKind::Sequential && !wasInForkJoin)
        stmtCtx.flags &= ~StatementFlags::InForkJoin;

    if (anyBad)
        return badStmt(comp, result);

    return *result;
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
        ASSERT(target);
        if (target == blockSymbol) {
            result = ER::Success;
            context.setDisableTarget(nullptr, {});
        }
    }

    return result;
}

Statement& ReturnStatement::fromSyntax(Compilation& compilation,
                                       const ReturnStatementSyntax& syntax,
                                       const BindContext& context, StatementContext& stmtCtx) {
    if (stmtCtx.flags.has(StatementFlags::InForkJoin)) {
        context.addDiag(diag::ReturnInParallel, syntax.sourceRange());
        return badStmt(compilation, nullptr);
    }

    // Find the parent subroutine or randsequence production.
    const Scope* scope = context.scope;
    while (scope->asSymbol().kind == SymbolKind::StatementBlock)
        scope = scope->asSymbol().getParentScope();

    auto stmtLoc = syntax.returnKeyword.location();
    auto& symbol = scope->asSymbol();
    if (symbol.kind != SymbolKind::Subroutine && symbol.kind != SymbolKind::RandSeqProduction) {
        context.addDiag(diag::ReturnNotInSubroutine, stmtLoc);
        return badStmt(compilation, nullptr);
    }

    auto& returnType = symbol.getDeclaredType()->getType();
    const Expression* retExpr = nullptr;
    if (syntax.returnValue) {
        retExpr = &Expression::bindRValue(returnType, *syntax.returnValue, stmtLoc, context);
    }
    else if (!returnType.isVoid()) {
        DiagCode code = symbol.kind == SymbolKind::Subroutine ? diag::MissingReturnValue
                                                              : diag::MissingReturnValueProd;
        context.addDiag(code, syntax.sourceRange());
        return badStmt(compilation, nullptr);
    }

    auto result = compilation.emplace<ReturnStatement>(retExpr, syntax.sourceRange());
    if (retExpr && retExpr->bad())
        return badStmt(compilation, result);

    return *result;
}

ER ReturnStatement::evalImpl(EvalContext& context) const {
    if (expr) {
        const SubroutineSymbol* subroutine = context.topFrame().subroutine;
        ASSERT(subroutine);

        ConstantValue* storage = context.findLocal(subroutine->returnValVar);
        ASSERT(storage);

        *storage = expr->eval(context);
    }
    return ER::Return;
}

void ReturnStatement::serializeTo(ASTSerializer& serializer) const {
    if (expr)
        serializer.write("expr", *expr);
}

Statement& BreakStatement::fromSyntax(Compilation& compilation, const JumpStatementSyntax& syntax,
                                      const BindContext& context, StatementContext& stmtCtx) {
    auto result = compilation.emplace<BreakStatement>(syntax.sourceRange());
    if (!stmtCtx.flags.has(StatementFlags::InLoop | StatementFlags::InRandSeq)) {
        context.addDiag(diag::StatementNotInLoop, syntax.sourceRange());
        return badStmt(compilation, result);
    }
    return *result;
}

ER BreakStatement::evalImpl(EvalContext&) const {
    return ER::Break;
}

Statement& ContinueStatement::fromSyntax(Compilation& compilation,
                                         const JumpStatementSyntax& syntax,
                                         const BindContext& context, StatementContext& stmtCtx) {
    auto result = compilation.emplace<ContinueStatement>(syntax.sourceRange());
    if (!stmtCtx.flags.has(StatementFlags::InLoop)) {
        context.addDiag(diag::StatementNotInLoop, syntax.sourceRange());
        return badStmt(compilation, result);
    }
    return *result;
}

ER ContinueStatement::evalImpl(EvalContext&) const {
    return ER::Continue;
}

Statement& DisableStatement::fromSyntax(Compilation& compilation,
                                        const DisableStatementSyntax& syntax,
                                        const BindContext& context) {
    LookupResult result;
    Lookup::name(*syntax.name, context, LookupFlags::ForceHierarchical | LookupFlags::NoSelectors,
                 result);
    result.reportDiags(context);

    const Symbol* symbol = result.found;
    if (!symbol)
        return badStmt(compilation, nullptr);

    if (symbol->kind != SymbolKind::StatementBlock &&
        (symbol->kind != SymbolKind::Subroutine ||
         symbol->as<SubroutineSymbol>().subroutineKind != SubroutineKind::Task)) {
        context.addDiag(diag::InvalidDisableTarget, syntax.name->sourceRange());
        return badStmt(compilation, nullptr);
    }

    return *compilation.emplace<DisableStatement>(*symbol, result.isHierarchical,
                                                  syntax.sourceRange());
}

ER DisableStatement::evalImpl(EvalContext& context) const {
    // Hierarchical names are disallowed in constant expressions and constant functions
    if (isHierarchical) {
        context.addDiag(diag::ConstEvalHierarchicalName, sourceRange) << target.name;
        return ER::Fail;
    }

    ASSERT(!context.getDisableTarget());
    context.setDisableTarget(&target, sourceRange);
    return ER::Disable;
}

void DisableStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.writeLink("target", target);
}

ER VariableDeclStatement::evalImpl(EvalContext& context) const {
    // Figure out the initial value for the variable.
    ConstantValue initial;
    if (auto initializer = symbol.getInitializer()) {
        // Initialization of static variables is skipped in constant functions.
        // This is confusing so issue a warning.
        if (symbol.lifetime == VariableLifetime::Static && !initializer->bad()) {
            context.addDiag(diag::ConstEvalStaticSkipped, initializer->sourceRange);
        }
        else {
            initial = initializer->eval(context);
            if (!initial)
                return ER::Fail;
        }
    }

    if (!initial)
        initial = symbol.getType().getDefaultValue();

    // Create storage for the variable.
    context.createLocal(&symbol, initial);
    return ER::Success;
}

void VariableDeclStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.writeLink("symbol", symbol);
}

Statement& ConditionalStatement::fromSyntax(Compilation& compilation,
                                            const ConditionalStatementSyntax& syntax,
                                            const BindContext& context, StatementContext& stmtCtx) {
    bool bad = false;
    auto& conditions = syntax.predicate->conditions;
    if (conditions.size() == 0) {
        bad = true;
    }
    else if (conditions.size() > 1) {
        context.addDiag(diag::NotYetSupported, conditions[1]->sourceRange());
        bad = true;
    }
    else if (conditions[0]->matchesClause) {
        context.addDiag(diag::NotYetSupported, conditions[0]->matchesClause->sourceRange());
        bad = true;
    }

    BindFlags ifFlags = BindFlags::None;
    BindFlags elseFlags = BindFlags::None;
    auto& cond = Expression::bind(*conditions[0]->expr, context);
    bad |= cond.bad();

    if (!bad && !context.requireBooleanConvertible(cond))
        bad = true;

    ConstantValue condVal = context.tryEval(cond);
    if (condVal) {
        // If the condition is constant, we know which branch will be taken.
        if (condVal.isTrue())
            elseFlags = BindFlags::UnevaluatedBranch;
        else
            ifFlags = BindFlags::UnevaluatedBranch;
    }

    auto& ifTrue = Statement::bind(*syntax.statement, context.resetFlags(ifFlags), stmtCtx);
    const Statement* ifFalse = nullptr;
    if (syntax.elseClause) {
        ifFalse = &Statement::bind(syntax.elseClause->clause->as<StatementSyntax>(),
                                   context.resetFlags(elseFlags), stmtCtx);
    }

    auto result =
        compilation.emplace<ConditionalStatement>(cond, ifTrue, ifFalse, syntax.sourceRange());
    if (bad || ifTrue.bad() || (ifFalse && ifFalse->bad()))
        return badStmt(compilation, result);

    return *result;
}

ER ConditionalStatement::evalImpl(EvalContext& context) const {
    auto result = cond.eval(context);
    if (result.bad())
        return ER::Fail;

    if (result.isTrue())
        return ifTrue.eval(context);
    if (ifFalse)
        return ifFalse->eval(context);

    return ER::Success;
}

void ConditionalStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("cond", cond);
    serializer.write("ifTrue", ifTrue);
    if (ifFalse)
        serializer.write("ifFalse", *ifFalse);
}

Statement& CaseStatement::fromSyntax(Compilation& compilation, const CaseStatementSyntax& syntax,
                                     const BindContext& context, StatementContext& stmtCtx) {
    bool bad = false;
    if (syntax.matchesOrInside.kind == TokenKind::MatchesKeyword) {
        context.addDiag(diag::NotYetSupported, syntax.matchesOrInside.range());
        bad = true;
    }

    CaseStatementCondition condition;
    switch (syntax.caseKeyword.kind) {
        case TokenKind::CaseKeyword:
            condition = CaseStatementCondition::Normal;
            break;
        case TokenKind::CaseXKeyword:
            condition = CaseStatementCondition::WildcardXOrZ;
            break;
        case TokenKind::CaseZKeyword:
            condition = CaseStatementCondition::WildcardJustZ;
            break;
        default:
            THROW_UNREACHABLE;
    }

    CaseStatementCheck check;
    switch (syntax.uniqueOrPriority.kind) {
        case TokenKind::Unknown:
            check = CaseStatementCheck::None;
            break;
        case TokenKind::UniqueKeyword:
            check = CaseStatementCheck::Unique;
            break;
        case TokenKind::Unique0Keyword:
            check = CaseStatementCheck::Unique0;
            break;
        case TokenKind::PriorityKeyword:
            check = CaseStatementCheck::Priority;
            break;
        default:
            THROW_UNREACHABLE;
    }

    SmallVectorSized<const ExpressionSyntax*, 8> expressions;
    SmallVectorSized<const Statement*, 8> statements;
    const Statement* defStmt = nullptr;

    for (auto item : syntax.items) {
        switch (item->kind) {
            case SyntaxKind::StandardCaseItem: {
                auto& sci = item->as<StandardCaseItemSyntax>();
                auto& stmt = Statement::bind(sci.clause->as<StatementSyntax>(), context, stmtCtx);
                for (auto es : sci.expressions) {
                    expressions.append(es);
                    statements.append(&stmt);
                }

                bad |= stmt.bad();
                break;
            }
            case SyntaxKind::PatternCaseItem:
                // TODO: support pattern case statements
                break;
            case SyntaxKind::DefaultCaseItem:
                // The parser already errored for duplicate defaults,
                // so just ignore if it happens here.
                if (!defStmt) {
                    defStmt = &Statement::bind(
                        item->as<DefaultCaseItemSyntax>().clause->as<StatementSyntax>(), context,
                        stmtCtx);
                    bad |= defStmt->bad();
                }
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    SmallVectorSized<const Expression*, 8> bound;
    TokenKind keyword = syntax.caseKeyword.kind;
    bool isInside = syntax.matchesOrInside.kind == TokenKind::InsideKeyword;
    bool wildcard = !isInside && keyword != TokenKind::CaseKeyword;
    bool allowTypeRefs = !isInside && keyword == TokenKind::CaseKeyword;
    bool allowOpenRange = !wildcard;

    bad |=
        !Expression::bindMembershipExpressions(context, keyword, wildcard, isInside, allowTypeRefs,
                                               allowOpenRange, *syntax.expr, expressions, bound);

    if (isInside && condition != CaseStatementCondition::Normal) {
        context.addDiag(diag::CaseInsideKeyword, syntax.matchesOrInside.range())
            << LexerFacts::getTokenKindText(keyword) << syntax.caseKeyword.range();
        bad = true;
    }
    else if (isInside) {
        condition = CaseStatementCondition::Inside;
    }

    SmallVectorSized<ItemGroup, 8> items;
    SmallVectorSized<const Expression*, 8> group;
    auto boundIt = bound.begin();
    auto stmtIt = statements.begin();

    auto expr = *boundIt++;
    bad |= expr->bad();

    for (auto item : syntax.items) {
        switch (item->kind) {
            case SyntaxKind::StandardCaseItem: {
                auto& sci = item->as<StandardCaseItemSyntax>();
                for (size_t i = 0; i < sci.expressions.size(); i++) {
                    bad |= (*boundIt)->bad();
                    group.append(*boundIt++);
                }

                items.append({ group.copy(compilation), *stmtIt++ });
                group.clear();
                break;
            }
            default:
                break;
        }
    }

    auto result = compilation.emplace<CaseStatement>(
        condition, check, *expr, items.copy(compilation), defStmt, syntax.sourceRange());
    if (bad)
        return badStmt(compilation, result);

    return *result;
}

static bool checkMatch(CaseStatementCondition condition, const ConstantValue& cvl,
                       const ConstantValue& cvr) {
    if (condition == CaseStatementCondition::Inside) {
        // Unpacked arrays get unwrapped into their members for comparison.
        if (cvr.isContainer()) {
            for (auto& elem : cvr) {
                if (checkMatch(condition, cvl, elem))
                    return true;
            }
            return false;
        }

        // Otherwise, we do a wildcard comparison if both sides are integers
        // and an equivalence comparison if not.
        if (cvl.isInteger() && cvr.isInteger())
            return (bool)condWildcardEqual(cvl.integer(), cvr.integer());
    }
    else if (condition != CaseStatementCondition::Normal) {
        const SVInt& l = cvl.integer();
        const SVInt& r = cvr.integer();
        if (condition == CaseStatementCondition::WildcardJustZ)
            return caseZWildcardEqual(l, r);
        else
            return caseXWildcardEqual(l, r);
    }

    return cvl == cvr;
}

ER CaseStatement::evalImpl(EvalContext& context) const {
    const Type* condType = nullptr;
    auto cv = expr.eval(context);
    if (!cv) {
        if (expr.kind == ExpressionKind::TypeReference)
            condType = &expr.as<TypeReferenceExpression>().targetType;
        else
            return ER::Fail;
    }

    const Statement* matchedStmt = nullptr;
    SourceRange matchRange;
    bool unique = check == CaseStatementCheck::Unique || check == CaseStatementCheck::Unique0;

    for (auto& group : items) {
        for (auto item : group.expressions) {
            bool matched;
            if (item->kind == ExpressionKind::OpenRange) {
                ConstantValue val = item->as<OpenRangeExpression>().checkInside(context, cv);
                if (!val)
                    return ER::Fail;

                matched = (bool)(logic_t)val.integer();
            }
            else {
                auto val = item->eval(context);
                if (val)
                    matched = checkMatch(condition, cv, val);
                else if (condType && item->kind == ExpressionKind::TypeReference)
                    matched = item->as<TypeReferenceExpression>().targetType.isMatching(*condType);
                else
                    return ER::Fail;
            }

            if (matched) {
                // If we already matched with a previous item, the only we reason
                // we'd still get here is to check for uniqueness. The presence of
                // another match means we failed the uniqueness check.
                if (matchedStmt) {
                    auto& diag =
                        context.addDiag(diag::ConstEvalCaseItemsNotUnique, item->sourceRange) << cv;
                    diag.addNote(diag::NotePreviousMatch, matchRange);
                    unique = false;
                }
                else {
                    // Always break out of the item group once we find a match -- even when
                    // checking uniqueness, expressions in a single group are not required
                    // to be unique.
                    matchedStmt = group.stmt;
                    matchRange = item->sourceRange;
                }
                break;
            }
        }

        if (matchedStmt && !unique)
            break;
    }

    if (!matchedStmt)
        matchedStmt = defaultCase;

    if (matchedStmt)
        return matchedStmt->eval(context);

    if (check == CaseStatementCheck::Priority || check == CaseStatementCheck::Unique) {
        auto& diag = context.addDiag(diag::ConstEvalNoCaseItemsMatched, expr.sourceRange);
        diag << (check == CaseStatementCheck::Priority ? "priority"sv : "unique"sv);
        diag << cv;
    }

    return ER::Success;
}

void CaseStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("condition", toString(condition));
    serializer.write("check", toString(check));
    serializer.write("expr", expr);
    serializer.startArray("items");
    for (auto const& item : items) {
        serializer.startObject();

        serializer.startArray("expressions");
        for (auto ex : item.expressions) {
            serializer.serialize(*ex);
        }
        serializer.endArray();

        serializer.write("stmt", *item.stmt);

        serializer.endObject();
    }
    serializer.endArray();

    if (defaultCase) {
        serializer.write("defaultCase", *defaultCase);
    }
}

class UnrollVisitor : public ASTVisitor<UnrollVisitor, true, false> {
public:
    bool anyErrors = false;

    explicit UnrollVisitor(const BindContext& bindCtx) :
        bindCtx(bindCtx.resetFlags({})), evalCtx(bindCtx.getCompilation()) {
        evalCtx.pushEmptyFrame();
    }

    void handle(const ForLoopStatement& loop) {
        if (loop.loopVars.empty() || !loop.stopExpr || loop.steps.empty() || anyErrors) {
            loop.body.visit(*this);
            return;
        }

        // Attempt to unroll the loop. If we are unable to collect constant values
        // for all loop variables across all iterations, we won't unroll at all.
        auto handleFail = [&] {
            for (auto var : loop.loopVars)
                evalCtx.deleteLocal(var);
            loop.body.visit(*this);
        };

        SmallVectorSized<ConstantValue*, 2> localPtrs;
        for (auto var : loop.loopVars) {
            auto init = var->getInitializer();
            if (!init) {
                handleFail();
                return;
            }

            auto cv = init->eval(evalCtx);
            if (!cv) {
                handleFail();
                return;
            }

            localPtrs.append(evalCtx.createLocal(var, std::move(cv)));
        }

        SmallVectorSized<ConstantValue, 16> values;
        while (true) {
            auto cv = step() ? loop.stopExpr->eval(evalCtx) : ConstantValue();
            if (!cv) {
                handleFail();
                return;
            }

            if (!cv.isTrue())
                break;

            for (auto local : localPtrs)
                values.emplace(*local);

            for (auto step : loop.steps) {
                if (!step->eval(evalCtx)) {
                    handleFail();
                    return;
                }
            }
        }

        // We have all the loop iteration values. Go back through
        // and visit the loop body for each iteration.
        for (size_t i = 0; i < values.size();) {
            for (auto local : localPtrs)
                *local = std::move(values[i++]);

            loop.body.visit(*this);
            if (anyErrors)
                return;
        }
    }

    void handle(const ConditionalStatement& stmt) {
        // Evaluate the condition; if not constant visit both sides,
        // otherwise visit only the side that matches the condition.
        auto cond = step() ? stmt.cond.eval(evalCtx) : ConstantValue();
        if (!cond) {
            stmt.ifTrue.visit(*this);
            if (stmt.ifFalse)
                stmt.ifFalse->visit(*this);
        }
        else if (cond.isTrue()) {
            stmt.ifTrue.visit(*this);
        }
        else if (stmt.ifFalse) {
            stmt.ifFalse->visit(*this);
        }
    }

    void handle(const ExpressionStatement& stmt) {
        step();
        if (stmt.expr.kind == ExpressionKind::Assignment) {
            auto& assign = stmt.expr.as<AssignmentExpression>();
            auto flags = assign.isNonBlocking() ? AssignFlags::NonBlocking : AssignFlags::None;
            anyErrors |= !assign.left().requireLValue(bindCtx, {}, flags, nullptr, &evalCtx);
        }
    }

private:
    bool step() {
        if (anyErrors || !evalCtx.step(SourceLocation::NoLocation)) {
            anyErrors = true;
            return false;
        }
        return true;
    }

    BindContext bindCtx;
    EvalContext evalCtx;
};

Statement& ForLoopStatement::fromSyntax(Compilation& compilation,
                                        const ForLoopStatementSyntax& syntax,
                                        const BindContext& context, StatementContext& stmtCtx) {
    SmallVectorSized<const Expression*, 4> initializers;
    SmallVectorSized<const VariableSymbol*, 4> loopVars;
    bool anyBad = false;

    const bool hasVarDecls = !syntax.initializers.empty() &&
                             syntax.initializers[0]->kind == SyntaxKind::ForVariableDeclaration;
    if (hasVarDecls) {
        // The block should have already been created for us containing the
        // variable declarations.
        for (auto& var : context.scope->membersOfType<VariableSymbol>())
            loopVars.append(&var);
    }
    else {
        for (auto initializer : syntax.initializers) {
            auto& init = Expression::bind(initializer->as<ExpressionSyntax>(), context,
                                          BindFlags::AssignmentAllowed);
            initializers.append(&init);
            anyBad |= init.bad();
        }
    }

    const Expression* stopExpr = nullptr;
    if (syntax.stopExpr)
        stopExpr = &Expression::bind(*syntax.stopExpr, context);

    SmallVectorSized<const Expression*, 2> steps;
    for (auto step : syntax.steps) {
        auto& expr = Expression::bind(*step, context, BindFlags::AssignmentAllowed);
        steps.append(&expr);
        anyBad |= expr.bad();

        bool stepOk;
        switch (expr.kind) {
            case ExpressionKind::Invalid:
            case ExpressionKind::Assignment:
            case ExpressionKind::Call:
                stepOk = true;
                break;
            case ExpressionKind::UnaryOp: {
                auto op = expr.as<UnaryExpression>().op;
                stepOk = op == UnaryOperator::Preincrement || op == UnaryOperator::Postincrement ||
                         op == UnaryOperator::Predecrement || op == UnaryOperator::Postdecrement;
                break;
            }
            default:
                stepOk = false;
                break;
        }

        if (!stepOk) {
            anyBad = true;
            context.addDiag(diag::InvalidForStepExpression, expr.sourceRange);
        }
    }

    if (anyBad || (stopExpr && stopExpr->bad()))
        return badStmt(compilation, nullptr);

    // For purposes of checking for multiple drivers to variables, we want to
    // "unroll" this for loop if possible to allow finer grained checking of
    // longest static prefixes involving the loop variables(s).
    const bool wasFirst = !stmtCtx.flags.has(StatementFlags::InForLoop);
    auto guard = stmtCtx.enterLoop(true);
    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);

    auto result = compilation.emplace<ForLoopStatement>(initializers.copy(compilation), stopExpr,
                                                        steps.copy(compilation), bodyStmt,
                                                        syntax.sourceRange());
    result->loopVars = loopVars.copy(compilation);

    if (bodyStmt.bad())
        return badStmt(compilation, result);

    // If this is the top-level unrollable for loop, attempt the unrolling now.
    // If not top-level, just pop up the stack and let the parent loop handle us.
    if (wasFirst && !compilation.getOptions().strictDriverChecking) {
        UnrollVisitor visitor(context);
        visitor.visit(*result);
    }

    return *result;
}

ER ForLoopStatement::evalImpl(EvalContext& context) const {
    for (auto init : initializers) {
        if (!init->eval(context))
            return ER::Fail;
    }

    while (true) {
        if (stopExpr) {
            auto result = stopExpr->eval(context);
            if (result.bad())
                return ER::Fail;

            if (!result.isTrue())
                break;
        }

        ER result = body.eval(context);
        if (result != ER::Success) {
            if (result == ER::Break)
                break;
            else if (result != ER::Continue)
                return result;
        }

        for (auto step : steps) {
            if (!step->eval(context))
                return ER::Fail;
        }
    }

    return ER::Success;
}

void ForLoopStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("initializers");
    for (auto ini : initializers) {
        serializer.serialize(*ini);
    }
    serializer.endArray();

    if (stopExpr)
        serializer.write("stopExpr", *stopExpr);

    serializer.startArray("steps");
    for (auto step : steps) {
        serializer.serialize(*step);
    }
    serializer.endArray();

    serializer.write("body", body);
}

Statement& RepeatLoopStatement::fromSyntax(Compilation& compilation,
                                           const LoopStatementSyntax& syntax,
                                           const BindContext& context, StatementContext& stmtCtx) {
    auto guard = stmtCtx.enterLoop();
    auto& countExpr = Expression::bind(*syntax.expr, context);

    bool bad = countExpr.bad();
    if (!bad && !countExpr.type->isNumeric()) {
        context.addDiag(diag::RepeatNotNumeric, countExpr.sourceRange);
        bad = true;
    }

    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result =
        compilation.emplace<RepeatLoopStatement>(countExpr, bodyStmt, syntax.sourceRange());

    if (bad || bodyStmt.bad())
        return badStmt(compilation, result);
    return *result;
}

ER RepeatLoopStatement::evalImpl(EvalContext& context) const {
    auto cv = count.eval(context);
    if (cv.bad())
        return ER::Fail;

    optional<int64_t> oc = cv.integer().as<int64_t>();
    if (!oc || oc < 0) {
        if (cv.integer().hasUnknown())
            oc = 0;
        else {
            auto& diag = context.addDiag(diag::ValueOutOfRange, count.sourceRange);
            diag << cv << 0 << INT64_MAX;
            return ER::Fail;
        }
    }

    int64_t c = *oc;
    for (int64_t i = 0; i < c; i++) {
        ER result = body.eval(context);
        if (result != ER::Success) {
            if (result == ER::Break)
                break;
            else if (result != ER::Continue)
                return result;
        }
    }

    return ER::Success;
}

void RepeatLoopStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("count", count);
    serializer.write("body", body);
}

const Expression* ForeachLoopStatement::buildLoopDims(const ForeachLoopListSyntax& loopList,
                                                      BindContext& context,
                                                      SmallVector<LoopDim>& dims) {
    // Find the array over which we are looping. Make sure it's actually iterable:
    // - Must be a referenceable variable, class property, etc.
    // - Type can be:
    //    - Any kind of array
    //    - Any multi-dimensional integral type
    //    - A string
    auto& comp = context.getCompilation();
    auto& arrayRef = Expression::bind(*loopList.arrayName, context);
    if (arrayRef.bad())
        return nullptr;

    const Type* type = arrayRef.type;
    auto arraySym = arrayRef.getSymbolReference();
    if (!arraySym || !type->isIterable()) {
        context.addDiag(diag::NotAnArray, arrayRef.sourceRange);
        return nullptr;
    }

    // Build iterator symbols for each loop variable.
    bool skippedAny = false;
    for (auto loopVar : loopList.loopVariables) {
        // If type is null, we've run out of dimensions so there were too many
        // loop variables supplied.
        if (!type || type->isScalar()) {
            context.addDiag(diag::TooManyForeachVars, loopList.loopVariables.sourceRange())
                << *arrayRef.type;
            return nullptr;
        }

        if (type->hasFixedRange())
            dims.append({ type->getFixedRange() });
        else
            dims.emplace();

        const Type& currType = *type;
        type = type->getArrayElementType();

        // Empty iterator names indicate that we skip this dimension.
        if (loopVar->kind == SyntaxKind::EmptyIdentifierName) {
            skippedAny = true;
            continue;
        }

        auto& idName = loopVar->as<IdentifierNameSyntax>();
        string_view name = idName.identifier.valueText();

        // If we previously had skipped dimensions this one can't be dynamically
        // sized (there would be no way to reach it during iteration).
        if (!dims.back().range && skippedAny) {
            context.addDiag(diag::ForeachDynamicDimAfterSkipped, idName.sourceRange()) << name;
            return nullptr;
        }

        if (name == arraySym->name) {
            context.addDiag(diag::LoopVarShadowsArray, loopVar->sourceRange()) << name;
            return nullptr;
        }

        // The type of the iterator is typically an int, unless this dimension
        // is an associative array in which case it's the index type.
        const Type* indexType;
        if (currType.isAssociativeArray()) {
            indexType = currType.getAssociativeIndexType();
            if (!indexType) {
                context.addDiag(diag::ForeachWildcardIndex, loopVar->sourceRange())
                    << loopList.arrayName->sourceRange();
                indexType = &comp.getErrorType();
            }
        }
        else {
            indexType = &comp.getIntType();
        }

        // Build the iterator variable and hook it up to our new context's
        // linked list of iterators.
        auto it =
            comp.emplace<IteratorSymbol>(name, idName.identifier.location(), currType, *indexType);
        it->nextIterator = std::exchange(context.firstIterator, it);
        dims.back().loopVar = it;
    }

    return &arrayRef;
}

Statement& ForeachLoopStatement::fromSyntax(Compilation& compilation,
                                            const ForeachLoopStatementSyntax& syntax,
                                            const BindContext& context, StatementContext& stmtCtx) {
    auto guard = stmtCtx.enterLoop();

    auto& arrayRef = Expression::bind(*syntax.loopList->arrayName, context);
    ASSERT(!arrayRef.bad());

    // Loop variables were already built in the containing block when it was elaborated,
    // so we just have to find them and associate them with the correct dim ranges here.
    BindContext iterCtx = context;
    SmallVectorSized<LoopDim, 4> dims;
    const Type* type = arrayRef.type;
    auto range = context.scope->membersOfType<IteratorSymbol>();
    auto itIt = range.begin();

    for (auto loopVar : syntax.loopList->loopVariables) {
        if (type->hasFixedRange())
            dims.append({ type->getFixedRange() });
        else
            dims.emplace();

        type = type->getArrayElementType();

        if (loopVar->kind == SyntaxKind::EmptyIdentifierName)
            continue;

        ASSERT(itIt != range.end());
        ASSERT(itIt->name == loopVar->as<IdentifierNameSyntax>().identifier.valueText());

        IteratorSymbol* it = const_cast<IteratorSymbol*>(&*itIt);
        it->nextIterator = std::exchange(iterCtx.firstIterator, it);
        dims.back().loopVar = it;
        itIt++;
    }

    ASSERT(itIt == range.end());

    auto& bodyStmt = Statement::bind(*syntax.statement, iterCtx, stmtCtx);
    auto result = compilation.emplace<ForeachLoopStatement>(arrayRef, dims.copy(compilation),
                                                            bodyStmt, syntax.sourceRange());
    if (bodyStmt.bad())
        return badStmt(compilation, result);
    return *result;
}

ER ForeachLoopStatement::evalImpl(EvalContext& context) const {
    // If there are no loop dimensions, this does nothing.
    if (loopDims.empty())
        return ER::Success;

    ConstantValue cv = arrayRef.eval(context);
    if (!cv)
        return ER::Fail;

    ER result = evalRecursive(context, cv, loopDims);
    if (result == ER::Break || result == ER::Continue)
        return ER::Success;

    return result;
}

ER ForeachLoopStatement::evalRecursive(EvalContext& context, const ConstantValue& cv,
                                       span<const LoopDim> currDims) const {
    // If there is no loop var just skip this index.
    auto& dim = currDims[0];
    if (!dim.loopVar) {
        // Shouldn't ever be at the end here.
        return evalRecursive(context, nullptr, currDims.subspan(1));
    }

    auto local = context.createLocal(dim.loopVar);

    // If this is an associative array, looping happens over the keys.
    if (cv.isMap()) {
        auto& map = *cv.map();
        for (auto& [key, val] : map) {
            *local = key;

            ER result;
            if (currDims.size() > 1)
                result = evalRecursive(context, val, currDims.subspan(1));
            else
                result = body.eval(context);

            if (result != ER::Success && result != ER::Continue)
                return result;
        }
    }
    else if (cv.isQueue()) {
        auto& q = *cv.queue();
        for (size_t i = 0; i < q.size(); i++) {
            *local = SVInt(32, i, true);

            ER result;
            if (currDims.size() > 1)
                result = evalRecursive(context, q[i], currDims.subspan(1));
            else
                result = body.eval(context);

            if (result != ER::Success && result != ER::Continue)
                return result;
        }
    }
    else if (cv.isString()) {
        ASSERT(currDims.size() == 1);

        auto& str = cv.str();
        for (size_t i = 0; i < str.size(); i++) {
            *local = SVInt(32, i, true);

            ER result = body.eval(context);
            if (result != ER::Success && result != ER::Continue)
                return result;
        }
    }
    else {
        span<const ConstantValue> elements;
        if (cv.isUnpacked())
            elements = cv.elements();

        ConstantRange range;
        bool isLittleEndian;
        if (dim.range) {
            range = *dim.range;
            isLittleEndian = range.isLittleEndian();
        }
        else {
            range = { 0, int32_t(elements.size()) - 1 };
            isLittleEndian = false;
        }

        for (int32_t i = range.left; isLittleEndian ? i >= range.right : i <= range.right;
             isLittleEndian ? i-- : i++) {

            *local = SVInt(32, uint64_t(i), true);

            ER result;
            if (currDims.size() > 1) {
                size_t index = size_t(i);
                if (dim.range)
                    index = (size_t)range.reverse().translateIndex(i);

                result = evalRecursive(context, elements.empty() ? nullptr : elements[index],
                                       currDims.subspan(1));
            }
            else {
                result = body.eval(context);
            }

            if (result != ER::Success && result != ER::Continue)
                return result;
        }
    }

    return ER::Success;
}

void ForeachLoopStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("arrayRef", arrayRef);

    serializer.startArray("loopDims");
    for (auto& r : loopDims) {
        serializer.startObject();
        serializer.write("range", r.range ? r.range->toString() : "[]");
        if (r.loopVar)
            serializer.write("var", *r.loopVar);
        serializer.endObject();
    }
    serializer.endArray();

    serializer.write("body", body);
}

Statement& WhileLoopStatement::fromSyntax(Compilation& compilation,
                                          const LoopStatementSyntax& syntax,
                                          const BindContext& context, StatementContext& stmtCtx) {
    auto guard = stmtCtx.enterLoop();

    bool bad = false;
    auto& condExpr = Expression::bind(*syntax.expr, context);
    if (!context.requireBooleanConvertible(condExpr))
        bad = true;

    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<WhileLoopStatement>(condExpr, bodyStmt, syntax.sourceRange());

    if (bad || bodyStmt.bad())
        return badStmt(compilation, result);
    return *result;
}

ER WhileLoopStatement::evalImpl(EvalContext& context) const {
    while (true) {
        auto cv = cond.eval(context);
        if (cv.bad())
            return ER::Fail;

        if (!cv.isTrue())
            break;

        ER result = body.eval(context);
        if (result != ER::Success) {
            if (result == ER::Break)
                break;
            else if (result != ER::Continue)
                return result;
        }
    }

    return ER::Success;
}

void WhileLoopStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("cond", cond);
    serializer.write("body", body);
}

Statement& DoWhileLoopStatement::fromSyntax(Compilation& compilation,
                                            const DoWhileStatementSyntax& syntax,
                                            const BindContext& context, StatementContext& stmtCtx) {
    auto guard = stmtCtx.enterLoop();

    bool bad = false;
    auto& condExpr = Expression::bind(*syntax.expr, context);
    if (!context.requireBooleanConvertible(condExpr))
        bad = true;

    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result =
        compilation.emplace<DoWhileLoopStatement>(condExpr, bodyStmt, syntax.sourceRange());

    if (bad || bodyStmt.bad())
        return badStmt(compilation, result);
    return *result;
}

ER DoWhileLoopStatement::evalImpl(EvalContext& context) const {
    while (true) {
        ER result = body.eval(context);
        if (result != ER::Success) {
            if (result == ER::Break)
                break;
            else if (result != ER::Continue)
                return result;
        }

        auto cv = cond.eval(context);
        if (cv.bad())
            return ER::Fail;

        if (!cv.isTrue())
            break;
    }

    return ER::Success;
}

void DoWhileLoopStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("cond", cond);
    serializer.write("body", body);
}

Statement& ForeverLoopStatement::fromSyntax(Compilation& compilation,
                                            const ForeverStatementSyntax& syntax,
                                            const BindContext& context, StatementContext& stmtCtx) {
    auto guard = stmtCtx.enterLoop();

    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<ForeverLoopStatement>(bodyStmt, syntax.sourceRange());
    if (bodyStmt.bad())
        return badStmt(compilation, result);

    return *result;
}

ER ForeverLoopStatement::evalImpl(EvalContext& context) const {
    while (true) {
        ER result = body.eval(context);
        if (result != ER::Success) {
            if (result == ER::Break)
                break;
            else if (result != ER::Continue)
                return result;
        }
    }

    return ER::Success;
}

void ForeverLoopStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("body", body);
}

Statement& ExpressionStatement::fromSyntax(Compilation& compilation,
                                           const ExpressionStatementSyntax& syntax,
                                           const BindContext& context, StatementContext& stmtCtx) {
    bitmask<BindFlags> extraFlags = BindFlags::AssignmentAllowed | BindFlags::TopLevelStatement;
    if (stmtCtx.flags.has(StatementFlags::InForLoop) &&
        BinaryExpressionSyntax::isKind(syntax.expr->kind) &&
        !compilation.getOptions().strictDriverChecking) {
        extraFlags |= BindFlags::UnrollableForLoop;
    }

    auto& expr = Expression::bind(*syntax.expr, context, extraFlags);
    auto result = compilation.emplace<ExpressionStatement>(expr, syntax.sourceRange());
    if (expr.bad())
        return badStmt(compilation, result);

    // Only a subset of expressions are allowed as statements.
    bool ok;
    switch (expr.kind) {
        case ExpressionKind::Call: {
            auto subKind = expr.as<CallExpression>().getSubroutineKind();
            if (!expr.type->isVoid() && subKind == SubroutineKind::Function) {
                context.addDiag(diag::UnusedResult, expr.sourceRange)
                    << expr.as<CallExpression>().getSubroutineName();
            }
            ok = true;
            break;
        }
        case ExpressionKind::Assignment:
        case ExpressionKind::NewClass:
            ok = true;
            break;
        case ExpressionKind::UnaryOp: {
            auto& unary = expr.as<UnaryExpression>();
            ok = unary.op == UnaryOperator::Preincrement ||
                 unary.op == UnaryOperator::Predecrement ||
                 unary.op == UnaryOperator::Postincrement ||
                 unary.op == UnaryOperator::Postdecrement;
            break;
        }
        default:
            ok = false;
            break;
    }

    if (!ok) {
        context.addDiag(diag::ExprNotStatement, expr.sourceRange);
        return badStmt(compilation, result);
    }

    return *result;
}

Statement& ExpressionStatement::fromSyntax(Compilation& compilation,
                                           const VoidCastedCallStatementSyntax& syntax,
                                           const BindContext& context) {
    auto& expr = Expression::bind(*syntax.expr, context);
    auto result = compilation.emplace<ExpressionStatement>(expr, syntax.sourceRange());
    if (expr.bad())
        return badStmt(compilation, result);

    if (expr.kind != ExpressionKind::Call ||
        (expr.as<CallExpression>().getSubroutineKind() == SubroutineKind::Task &&
         expr.type->isVoid())) {
        context.addDiag(diag::VoidCastFuncCall, expr.sourceRange);
        return badStmt(compilation, result);
    }

    if (expr.type->isVoid()) {
        context.addDiag(diag::PointlessVoidCast, expr.sourceRange)
            << expr.as<CallExpression>().getSubroutineName();
    }

    return *result;
}

ER ExpressionStatement::evalImpl(EvalContext& context) const {
    // Skip system task invocations.
    if (expr.kind == ExpressionKind::Call && expr.as<CallExpression>().isSystemCall() &&
        expr.as<CallExpression>().getSubroutineKind() == SubroutineKind::Task) {
        context.addDiag(diag::ConstSysTaskIgnored, expr.sourceRange)
            << expr.as<CallExpression>().getSubroutineName();
        return ER::Success;
    }

    return expr.eval(context) ? ER::Success : ER::Fail;
}

void ExpressionStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
}

Statement& TimedStatement::fromSyntax(Compilation& compilation,
                                      const TimingControlStatementSyntax& syntax,
                                      const BindContext& context, StatementContext& stmtCtx) {
    auto& timing = TimingControl::bind(*syntax.timingControl, context);
    auto& stmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<TimedStatement>(timing, stmt, syntax.sourceRange());

    if (timing.bad() || stmt.bad())
        return badStmt(compilation, result);

    return *result;
}

ER TimedStatement::evalImpl(EvalContext& context) const {
    if (context.flags.has(EvalFlags::IsScript))
        return stmt.eval(context);

    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

void TimedStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("timing", timing);
    serializer.write("stmt", stmt);
}

static void checkDeferredAssertAction(const Statement& stmt, const BindContext& context) {
    if (stmt.kind == StatementKind::Empty)
        return;

    // The statement inside a deferred assertion action block must be a subroutine call.
    if (stmt.kind != StatementKind::ExpressionStatement ||
        stmt.as<ExpressionStatement>().expr.kind != ExpressionKind::Call) {
        context.addDiag(diag::InvalidDeferredAssertAction, stmt.sourceRange);
        return;
    }

    // The subroutine being called has some restrictions:
    // - No output or inout arguments
    // - If a system call, must be a task
    // - Any ref arguments cannot reference automatic or dynamic variables
    auto& call = stmt.as<ExpressionStatement>().expr.as<CallExpression>();
    AssertionExpr::checkAssertionCall(call, context, diag::DeferredAssertOutArg,
                                      diag::DeferredAssertAutoRefArg, diag::DeferredAssertSysTask,
                                      stmt.sourceRange);
}

Statement& ImmediateAssertionStatement::fromSyntax(Compilation& compilation,
                                                   const ImmediateAssertionStatementSyntax& syntax,
                                                   const BindContext& context,
                                                   StatementContext& stmtCtx) {
    AssertionKind assertKind = SemanticFacts::getAssertKind(syntax.kind);
    auto& cond = Expression::bind(*syntax.expr->expression, context);
    bool bad = cond.bad();

    if (!bad && !context.requireBooleanConvertible(cond))
        bad = true;

    const Statement* ifTrue = nullptr;
    const Statement* ifFalse = nullptr;
    if (syntax.action->statement)
        ifTrue = &Statement::bind(*syntax.action->statement, context, stmtCtx);

    if (syntax.action->elseClause) {
        ifFalse = &Statement::bind(syntax.action->elseClause->clause->as<StatementSyntax>(),
                                   context, stmtCtx);
    }

    bool isDeferred = syntax.delay != nullptr;
    bool isFinal = false;
    if (isDeferred)
        isFinal = syntax.delay->finalKeyword.valid();

    bool isCover =
        assertKind == AssertionKind::CoverProperty || assertKind == AssertionKind::CoverSequence;
    if (isCover && ifFalse) {
        context.addDiag(diag::CoverStmtNoFail, syntax.action->elseClause->sourceRange());
        bad = true;
    }

    if (isDeferred) {
        if (ifTrue)
            checkDeferredAssertAction(*ifTrue, context);
        if (ifFalse)
            checkDeferredAssertAction(*ifFalse, context);
    }

    auto result = compilation.emplace<ImmediateAssertionStatement>(
        assertKind, cond, ifTrue, ifFalse, isDeferred, isFinal, syntax.sourceRange());
    if (bad || (ifTrue && ifTrue->bad()) || (ifFalse && ifFalse->bad()))
        return badStmt(compilation, result);

    return *result;
}

ER ImmediateAssertionStatement::evalImpl(EvalContext& context) const {
    auto result = cond.eval(context);
    if (result.bad())
        return ER::Fail;

    if (isDeferred) {
        context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
        return ER::Fail;
    }

    if (result.isTrue()) {
        if (ifTrue)
            return ifTrue->eval(context);
        return ER::Success;
    }

    if (ifFalse)
        return ifFalse->eval(context);

    bool isCover = assertionKind == AssertionKind::CoverProperty ||
                   assertionKind == AssertionKind::CoverSequence;
    if (isCover)
        return ER::Success;

    context.addDiag(diag::ConstEvalAssertionFailed, sourceRange);
    return ER::Fail;
}

void ImmediateAssertionStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("cond", cond);
    if (ifTrue)
        serializer.write("ifTrue", *ifTrue);
    if (ifFalse)
        serializer.write("ifFalse", *ifFalse);
    serializer.write("assertionKind", toString(assertionKind));
    serializer.write("isDeferred", isDeferred);
    serializer.write("isFinal", isFinal);
}

Statement& ConcurrentAssertionStatement::fromSyntax(
    Compilation& compilation, const ConcurrentAssertionStatementSyntax& syntax,
    const BindContext& context, StatementContext& stmtCtx) {

    if (context.flags.has(BindFlags::ConcurrentAssertActionBlock)) {
        context.addDiag(diag::ConcurrentAssertActionBlock, syntax.sourceRange())
            << syntax.keyword.valueText();
        return badStmt(compilation, nullptr);
    }

    BindContext ctx = context;
    ctx.clearInstanceAndProc();

    AssertionKind assertKind = SemanticFacts::getAssertKind(syntax.kind);
    auto& prop = AssertionExpr::bind(*syntax.propertySpec, ctx);
    bool bad = prop.bad();

    ctx.flags |= BindFlags::ConcurrentAssertActionBlock;
    const Statement* ifTrue = nullptr;
    const Statement* ifFalse = nullptr;
    if (syntax.action->statement)
        ifTrue = &Statement::bind(*syntax.action->statement, ctx, stmtCtx);

    if (syntax.action->elseClause) {
        ifFalse = &Statement::bind(syntax.action->elseClause->clause->as<StatementSyntax>(), ctx,
                                   stmtCtx);
    }

    const bool isCover =
        assertKind == AssertionKind::CoverProperty || assertKind == AssertionKind::CoverSequence;
    if (isCover && ifFalse) {
        ctx.addDiag(diag::CoverStmtNoFail, syntax.action->elseClause->sourceRange());
        bad = true;
    }
    else if (assertKind == AssertionKind::Restrict &&
             (ifFalse || (ifTrue && ifTrue->kind != StatementKind::Empty))) {
        ctx.addDiag(diag::RestrictStmtNoFail, syntax.action->sourceRange());
        bad = true;
    }

    auto result = compilation.emplace<ConcurrentAssertionStatement>(assertKind, prop, ifTrue,
                                                                    ifFalse, syntax.sourceRange());
    if (bad || (ifTrue && ifTrue->bad()) || (ifFalse && ifFalse->bad()))
        return badStmt(compilation, result);

    return *result;
}

ER ConcurrentAssertionStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

void ConcurrentAssertionStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("propertySpec", propertySpec);
    if (ifTrue)
        serializer.write("ifTrue", *ifTrue);
    if (ifFalse)
        serializer.write("ifFalse", *ifFalse);
    serializer.write("assertionKind", toString(assertionKind));
}

Statement& DisableForkStatement::fromSyntax(Compilation& compilation,
                                            const DisableForkStatementSyntax& syntax) {
    return *compilation.emplace<DisableForkStatement>(syntax.sourceRange());
}

ER DisableForkStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

Statement& WaitStatement::fromSyntax(Compilation& compilation, const WaitStatementSyntax& syntax,
                                     const BindContext& context, StatementContext& stmtCtx) {
    auto& cond = Expression::bind(*syntax.expr, context);
    auto& stmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<WaitStatement>(cond, stmt, syntax.sourceRange());
    if (cond.bad() || stmt.bad())
        return badStmt(compilation, result);

    if (!context.requireBooleanConvertible(cond))
        return badStmt(compilation, result);

    if (context.flags.has(BindFlags::Function | BindFlags::Final) || context.inAlwaysCombLatch()) {
        context.addDiag(diag::TimingInFuncNotAllowed, syntax.sourceRange());
        return badStmt(compilation, result);
    }

    return *result;
}

ER WaitStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

void WaitStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("cond", cond);
    serializer.write("stmt", stmt);
}

Statement& WaitForkStatement::fromSyntax(Compilation& compilation,
                                         const WaitForkStatementSyntax& syntax) {
    return *compilation.emplace<WaitForkStatement>(syntax.sourceRange());
}

ER WaitForkStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

Statement& WaitOrderStatement::fromSyntax(Compilation& compilation,
                                          const WaitOrderStatementSyntax& syntax,
                                          const BindContext& context, StatementContext& stmtCtx) {
    SmallVectorSized<const Expression*, 4> events;
    for (auto name : syntax.names) {
        auto& ev = Expression::bind(*name, context);
        if (ev.bad())
            return badStmt(compilation, nullptr);

        if (!ev.type->isEvent()) {
            context.addDiag(diag::NotAnEvent, name->sourceRange());
            return badStmt(compilation, nullptr);
        }

        events.append(&ev);
    }

    const Statement* ifTrue = nullptr;
    const Statement* ifFalse = nullptr;
    if (syntax.action->statement)
        ifTrue = &Statement::bind(*syntax.action->statement, context, stmtCtx);

    if (syntax.action->elseClause) {
        ifFalse = &Statement::bind(syntax.action->elseClause->clause->as<StatementSyntax>(),
                                   context, stmtCtx);
    }

    auto result = compilation.emplace<WaitOrderStatement>(events.copy(compilation), ifTrue, ifFalse,
                                                          syntax.sourceRange());
    if (context.flags.has(BindFlags::Function) || context.flags.has(BindFlags::Final) ||
        context.inAlwaysCombLatch()) {
        context.addDiag(diag::TimingInFuncNotAllowed, syntax.sourceRange());
        return badStmt(compilation, result);
    }

    return *result;
}

ER WaitOrderStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

void WaitOrderStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("events");
    for (auto ev : events) {
        serializer.startObject();
        serializer.write("target", *ev);
        serializer.endObject();
    }
    serializer.endArray();

    if (ifTrue)
        serializer.write("ifTrue", *ifTrue);
    if (ifFalse)
        serializer.write("ifFalse", *ifFalse);
}

Statement& EventTriggerStatement::fromSyntax(Compilation& compilation,
                                             const EventTriggerStatementSyntax& syntax,
                                             const BindContext& context) {
    auto& target = Expression::bind(*syntax.name, context);
    if (target.bad())
        return badStmt(compilation, nullptr);

    if (!target.type->isEvent()) {
        context.addDiag(diag::NotAnEvent, syntax.name->sourceRange());
        return badStmt(compilation, nullptr);
    }

    const TimingControl* timing = nullptr;
    if (syntax.timing)
        timing = &TimingControl::bind(*syntax.timing, context);

    bool isNonBlocking = syntax.kind == SyntaxKind::NonblockingEventTriggerStatement;

    return *compilation.emplace<EventTriggerStatement>(target, timing, isNonBlocking,
                                                       syntax.sourceRange());
}

ER EventTriggerStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

void EventTriggerStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("target", target);
    serializer.write("isNonBlocking", isNonBlocking);
    if (timing)
        serializer.write("timing", *timing);
}

static bool isValidAssignLVal(const Expression& expr) {
    switch (expr.kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue:
            if (auto sym = expr.getSymbolReference()) {
                if (!VariableSymbol::isKind(sym->kind))
                    return false;
            }
            return true;
        case ExpressionKind::Concatenation:
            for (auto op : expr.as<ConcatenationExpression>().operands()) {
                if (!isValidAssignLVal(*op))
                    return false;
            }
            return true;
        default:
            return false;
    }
}

static bool isValidForceLVal(const Expression& expr, const BindContext& context, bool inSelect) {
    switch (expr.kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue:
            if (auto sym = expr.getSymbolReference()) {
                if (inSelect && VariableSymbol::isKind(sym->kind))
                    return false;

                if (sym->kind == SymbolKind::Net && !sym->as<NetSymbol>().netType.isBuiltIn())
                    context.addDiag(diag::BadForceNetType, expr.sourceRange);
            }
            return true;
        case ExpressionKind::MemberAccess:
            return isValidForceLVal(expr.as<MemberAccessExpression>().value(), context, true);
        case ExpressionKind::ElementSelect:
            return isValidForceLVal(expr.as<ElementSelectExpression>().value(), context, true);
        case ExpressionKind::RangeSelect:
            return isValidForceLVal(expr.as<RangeSelectExpression>().value(), context, true);
        case ExpressionKind::Concatenation:
            for (auto op : expr.as<ConcatenationExpression>().operands()) {
                if (!isValidForceLVal(*op, context, false))
                    return false;
            }
            return true;
        default:
            return false;
    }
}

Statement& ProceduralAssignStatement::fromSyntax(Compilation& compilation,
                                                 const ProceduralAssignStatementSyntax& syntax,
                                                 const BindContext& context) {
    bool isForce = syntax.keyword.kind == TokenKind::ForceKeyword;
    bitmask<BindFlags> bindFlags = BindFlags::NonProcedural | BindFlags::AssignmentAllowed;
    if (isForce)
        bindFlags |= BindFlags::ProceduralForceRelease;
    else
        bindFlags |= BindFlags::ProceduralAssign;

    auto& assign = Expression::bind(*syntax.expr, context, bindFlags);
    auto result =
        compilation.emplace<ProceduralAssignStatement>(assign, isForce, syntax.sourceRange());
    if (assign.bad())
        return badStmt(compilation, result);

    if (assign.kind == ExpressionKind::Assignment) {
        auto& lval = assign.as<AssignmentExpression>().left();
        if (isForce) {
            if (!isValidForceLVal(lval, context, false)) {
                context.addDiag(diag::BadProceduralForce, lval.sourceRange);
                return badStmt(compilation, result);
            }
        }
        else {
            if (!isValidAssignLVal(lval)) {
                context.addDiag(diag::BadProceduralAssign, lval.sourceRange);
                return badStmt(compilation, result);
            }
        }
    }

    return *result;
}

ER ProceduralAssignStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalProceduralAssign, sourceRange);
    return ER::Fail;
}

void ProceduralAssignStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("assignment", assignment);
    serializer.write("isForce", isForce);
}

Statement& ProceduralDeassignStatement::fromSyntax(Compilation& compilation,
                                                   const ProceduralDeassignStatementSyntax& syntax,
                                                   const BindContext& context) {
    auto ctx = context.resetFlags(BindFlags::NonProcedural | BindFlags::ProceduralForceRelease |
                                  BindFlags::LValue);
    auto& lvalue = Expression::bind(*syntax.variable, ctx);

    bool isRelease = syntax.keyword.kind == TokenKind::ReleaseKeyword;
    auto result =
        compilation.emplace<ProceduralDeassignStatement>(lvalue, isRelease, syntax.sourceRange());
    if (lvalue.bad())
        return badStmt(compilation, result);

    if (!lvalue.requireLValue(ctx))
        return badStmt(compilation, result);

    if (isRelease) {
        if (!isValidForceLVal(lvalue, ctx, false)) {
            ctx.addDiag(diag::BadProceduralForce, lvalue.sourceRange);
            return badStmt(compilation, result);
        }
    }
    else {
        if (!isValidAssignLVal(lvalue)) {
            ctx.addDiag(diag::BadProceduralAssign, lvalue.sourceRange);
            return badStmt(compilation, result);
        }
    }

    return *result;
}

ER ProceduralDeassignStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalProceduralAssign, sourceRange);
    return ER::Fail;
}

void ProceduralDeassignStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("lvalue", lvalue);
    serializer.write("isRelease", isRelease);
}

Statement& RandCaseStatement::fromSyntax(Compilation& compilation,
                                         const RandCaseStatementSyntax& syntax,
                                         const BindContext& context, StatementContext& stmtCtx) {
    bool bad = false;
    SmallVectorSized<Item, 8> items;
    for (auto item : syntax.items) {
        auto& expr = Expression::bind(*item->expr, context);
        auto& stmt = Statement::bind(*item->statement, context, stmtCtx);
        items.append({ &expr, &stmt });

        if (stmt.bad() || !context.requireIntegral(expr)) {
            bad = true;
        }
    }

    auto result =
        compilation.emplace<RandCaseStatement>(items.copy(compilation), syntax.sourceRange());
    if (bad)
        return badStmt(compilation, result);

    return *result;
}

ER RandCaseStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalRandValue, sourceRange);
    return ER::Fail;
}

void RandCaseStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("items");
    for (auto& item : items) {
        serializer.startObject();
        serializer.write("expr", *item.expr);
        serializer.write("stmt", *item.stmt);
        serializer.endObject();
    }
    serializer.endArray();
}

Statement& RandSequenceStatement::fromSyntax(Compilation& compilation,
                                             const RandSequenceStatementSyntax& syntax,
                                             const BindContext& context) {
    SourceRange firstProdRange;
    const RandSeqProductionSymbol* firstProd = nullptr;
    if (syntax.firstProduction) {
        firstProdRange = syntax.firstProduction.range();
        firstProd = RandSeqProductionSymbol::findProduction(syntax.firstProduction.valueText(),
                                                            firstProdRange, context);
    }
    else {
        auto prodRange = context.scope->membersOfType<RandSeqProductionSymbol>();
        if (prodRange.begin() != prodRange.end()) {
            firstProd = &*prodRange.begin();
            firstProdRange = { syntax.randsequence.location(), syntax.closeParen.range().end() };
        }
    }

    if (firstProd) {
        // Make sure the first production doesn't require arguments.
        SmallVectorSized<const Expression*, 8> args;
        CallExpression::bindArgs(nullptr, firstProd->arguments, firstProd->name, firstProdRange,
                                 context, args);
    }

    // All of the logic for binding productions is in the RandSeqProduction symbol.
    auto result = compilation.emplace<RandSequenceStatement>(firstProd, syntax.sourceRange());
    return *result;
}

ER RandSequenceStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalRandValue, sourceRange);
    return ER::Fail;
}

void RandSequenceStatement::serializeTo(ASTSerializer& serializer) const {
    if (firstProduction)
        serializer.writeLink("firstProduction", *firstProduction);
}

} // namespace slang
