//------------------------------------------------------------------------------
// Statements.cpp
// Statement creation and analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/Statements.h"

#include "slang/binding/Expressions.h"
#include "slang/binding/TimingControl.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
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
        return stmt.evalImpl(context);
    }

    ER visitInvalid(const Statement&, EvalContext&) { return ER::Fail; }
};

struct VerifyVisitor {
    template<typename T>
    bool visit(const T& stmt, EvalContext& context) {
        if (stmt.bad())
            return false;

        return stmt.verifyConstantImpl(context);
    }

    bool visitInvalid(const Statement&, EvalContext&) { return false; }
};

} // namespace

namespace slang {

const InvalidStatement InvalidStatement::Instance(nullptr);
const StatementList StatementList::Empty({});

ER Statement::eval(EvalContext& context) const {
    EvalVisitor visitor;
    return visit(visitor, context);
}

bool Statement::verifyConstant(EvalContext& context) const {
    VerifyVisitor visitor;
    return visit(visitor, context);
}

BlockStatement* Statement::StatementContext::tryGetBlock(Compilation& compilation,
                                                         const SyntaxNode& node) {
    if (!blocks.empty() && blocks[0]->getSyntax() == &node) {
        auto result = compilation.emplace<BlockStatement>(*blocks[0]);
        blocks = blocks.subspan(1);
        return result;
    }
    return nullptr;
}

const Statement& Statement::bind(const StatementSyntax& syntax, const BindContext& context,
                                 StatementContext& stmtCtx, bool inList) {
    // TODO:
    /*if (syntax.label) {
        results.append(SequentialBlockSymbol::fromLabeledStmt(scope.getCompilation(), syntax));
        return;
    }*/

    auto& comp = context.scope.getCompilation();
    Statement* result;
    switch (syntax.kind) {
        case SyntaxKind::EmptyStatement:
            result = comp.emplace<EmptyStatement>();
            if (inList && syntax.attributes.empty())
                context.addDiag(diag::EmptyStatement, syntax.sourceRange());
            break;
        case SyntaxKind::ReturnStatement:
            result =
                &ReturnStatement::fromSyntax(comp, syntax.as<ReturnStatementSyntax>(), context);
            break;
        case SyntaxKind::JumpStatement: {
            auto& jump = syntax.as<JumpStatementSyntax>();
            if (jump.breakOrContinue.kind == TokenKind::BreakKeyword)
                result = &BreakStatement::fromSyntax(comp, jump, context, stmtCtx);
            else
                result = &ContinueStatement::fromSyntax(comp, jump, context, stmtCtx);
            break;
        }
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
            result = stmtCtx.tryGetBlock(comp, syntax);
            if (!result) {
                result = &ForLoopStatement::fromSyntax(comp, syntax.as<ForLoopStatementSyntax>(),
                                                       context, stmtCtx);
            }
            break;
        case SyntaxKind::LoopStatement: {
            auto& loop = syntax.as<LoopStatementSyntax>();
            if (loop.repeatOrWhile.kind == TokenKind::RepeatKeyword)
                result = &RepeatLoopStatement::fromSyntax(comp, loop, context, stmtCtx);
            else
                result = &WhileLoopStatement::fromSyntax(comp, loop, context, stmtCtx);
            break;
        }
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
                                                      context);
            break;
        case SyntaxKind::SequentialBlockStatement:
            // A block statement may or may not match up with a hierarchy node. Handle both cases
            // here. We traverse statements in the same order as the findBlocks call below, so this
            // should always sync up exactly.
            result = stmtCtx.tryGetBlock(comp, syntax);
            if (!result) {
                result = &BlockStatement::fromSyntax(comp, syntax.as<BlockStatementSyntax>(),
                                                     context, stmtCtx);
            }
            break;
        case SyntaxKind::TimingControlStatement:
            result = &TimedStatement::fromSyntax(comp, syntax.as<TimingControlStatementSyntax>(),
                                                 context, stmtCtx);
            break;
        case SyntaxKind::ImmediateAssertStatement:
        case SyntaxKind::ImmediateAssumeStatement:
        case SyntaxKind::ImmediateCoverStatement:
            result = &AssertionStatement::fromSyntax(
                comp, syntax.as<ImmediateAssertionStatementSyntax>(), context, stmtCtx);
            break;
        case SyntaxKind::ProceduralAssignStatement:
        case SyntaxKind::ProceduralForceStatement:
        case SyntaxKind::ProceduralDeassignStatement:
        case SyntaxKind::ProceduralReleaseStatement:
        case SyntaxKind::DisableStatement:
        case SyntaxKind::DisableForkStatement:
        case SyntaxKind::BlockingEventTriggerStatement:
        case SyntaxKind::NonblockingEventTriggerStatement:
        case SyntaxKind::WaitForkStatement:
        case SyntaxKind::ParallelBlockStatement:
        case SyntaxKind::ForeachLoopStatement:
        case SyntaxKind::WaitStatement:
        case SyntaxKind::RandCaseStatement:
        case SyntaxKind::AssertPropertyStatement:
        case SyntaxKind::AssumePropertyStatement:
        case SyntaxKind::CoverSequenceStatement:
        case SyntaxKind::CoverPropertyStatement:
        case SyntaxKind::RestrictPropertyStatement:
        case SyntaxKind::ExpectPropertyStatement:
        case SyntaxKind::WaitOrderStatement:
            context.addDiag(diag::NotYetSupported, syntax.sourceRange());
            result = &badStmt(comp, nullptr);
            break;
        default:
            THROW_UNREACHABLE;
    }

    result->syntax = &syntax;
    comp.addAttributes(*result, syntax.attributes);
    return *result;
}

Statement& Statement::badStmt(Compilation& compilation, const Statement* stmt) {
    return *compilation.emplace<InvalidStatement>(stmt);
}

static void findBlocks(const Scope& scope, const StatementSyntax& syntax,
                       SmallVector<const StatementBlockSymbol*>& results) {
    // TODO:
    /*if (syntax.label) {
        results.append(SequentialBlockSymbol::fromLabeledStmt(scope.getCompilation(), syntax));
        return;
    }*/

    auto recurse = [&](auto stmt) { findBlocks(scope, *stmt, results); };

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
            // These statements don't have child statements within them.
            return;

        case SyntaxKind::SequentialBlockStatement:
        case SyntaxKind::ParallelBlockStatement: {
            // Block statements form their own hierarchy scope if:
            // - They have a name
            // - They are unnamed but have variable declarations within them
            auto& block = syntax.as<BlockStatementSyntax>();
            if (block.blockName) {
                results.append(&StatementBlockSymbol::fromSyntax(scope.getCompilation(), block));
                return;
            }

            for (auto item : block.items) {
                // If we find any decls at all, this block gets its own scope.
                if (!StatementSyntax::isKind(item->kind)) {
                    results.append(
                        &StatementBlockSymbol::fromSyntax(scope.getCompilation(), block));
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

                results.append(&StatementBlockSymbol::fromSyntax(scope.getCompilation(), forLoop));
            }
            else {
                recurse(forLoop.statement);
            }
            return;
        }
        case SyntaxKind::ForeachLoopStatement:
            recurse(syntax.as<ForeachLoopStatementSyntax>().statement);
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
        case SyntaxKind::CoverSequenceStatement:
        case SyntaxKind::CoverPropertyStatement:
        case SyntaxKind::RestrictPropertyStatement:
        case SyntaxKind::ExpectPropertyStatement:
        case SyntaxKind::WaitOrderStatement:
            scope.addDiag(diag::NotYetSupported, syntax.sourceRange());
            return;
        default:
            THROW_UNREACHABLE;
    }
}

void StatementBinder::setSyntax(const Scope& scope, const StatementSyntax& syntax_) {
    stmt = nullptr;
    syntax = &syntax_;

    SmallVectorSized<const StatementBlockSymbol*, 8> buffer;
    findBlocks(scope, syntax_, buffer);
    blocks = buffer.copy(scope.getCompilation());
}

void StatementBinder::setSyntax(const StatementBlockSymbol& scope,
                                const ForLoopStatementSyntax& syntax_) {
    stmt = nullptr;
    syntax = &syntax_;

    SmallVectorSized<const StatementBlockSymbol*, 8> buffer;
    findBlocks(scope, *syntax_.statement, buffer);
    blocks = buffer.copy(scope.getCompilation());
}

void StatementBinder::setItems(Scope& scope, const SyntaxList<SyntaxNode>& items) {
    stmt = nullptr;
    syntax = &items;

    SmallVectorSized<const StatementBlockSymbol*, 8> buffer;
    for (auto item : items) {
        switch (item->kind) {
            case SyntaxKind::DataDeclaration:
            case SyntaxKind::TypedefDeclaration:
            case SyntaxKind::ForwardTypedefDeclaration:
            case SyntaxKind::ForwardInterfaceClassTypedefDeclaration:
            case SyntaxKind::PackageImportDeclaration:
            case SyntaxKind::ParameterDeclarationStatement:
                scope.addMembers(*item);
                break;
            case SyntaxKind::PortDeclaration:
            case SyntaxKind::LetDeclaration:
            case SyntaxKind::NetTypeDeclaration:
                scope.addDiag(diag::NotYetSupported, item->sourceRange());
                break;
            default:
                findBlocks(scope, item->as<StatementSyntax>(), buffer);
                break;
        }
    }

    blocks = buffer.copy(scope.getCompilation());
    for (auto block : blocks)
        scope.addMember(*block);
}

const Statement& StatementBinder::getStatement(const BindContext& context) const {
    if (!stmt)
        stmt = &bindStatement(context);
    return *stmt;
}

const Statement& StatementBinder::bindStatement(const BindContext& context) const {
    auto& scope = context.scope;
    auto& comp = scope.getCompilation();
    SmallVectorSized<const Statement*, 8> buffer;

    auto scopeKind = scope.asSymbol().kind;
    if (scopeKind == SymbolKind::StatementBlock || scopeKind == SymbolKind::Subroutine) {
        // This relies on the language requiring all declarations be at the start
        // of a statement block. Additional work would be required to support
        // declarations anywhere in the block.
        for (auto& member : scope.members()) {
            if (member.kind != SymbolKind::Variable)
                continue;

            // Filter out implicitly generated function return type variables,
            // they are initialized elsewhere.
            auto& var = member.as<VariableSymbol>();
            if (!var.isCompilerGenerated)
                buffer.append(comp.emplace<VariableDeclStatement>(var));
        }
    }

    bool anyBad = false;
    Statement::StatementContext stmtCtx;
    stmtCtx.blocks = blocks;

    if (auto stmtSyntax = std::get_if<const StatementSyntax*>(&syntax)) {
        if (auto ptr = *stmtSyntax) {
            buffer.append(&Statement::bind(*ptr, context, stmtCtx));
            anyBad |= buffer.back()->bad();
        }
    }
    else {
        auto& items = *std::get<const SyntaxList<SyntaxNode>*>(syntax);
        for (auto item : items) {
            if (StatementSyntax::isKind(item->kind)) {
                buffer.append(&Statement::bind(item->as<StatementSyntax>(), context, stmtCtx,
                                               /* inList */ true));
                anyBad |= buffer.back()->bad();
            }
        }
    }

    ASSERT(anyBad || stmtCtx.blocks.empty());

    if (anyBad)
        return InvalidStatement::Instance;

    if (buffer.size() == 1)
        return *buffer[0];

    return *comp.emplace<StatementList>(buffer.copy(comp));
}

ER StatementList::evalImpl(EvalContext& context) const {
    for (auto item : list) {
        ER result = item->eval(context);
        if (result != ER::Success)
            return result;
    }

    return ER::Success;
}

bool StatementList::verifyConstantImpl(EvalContext& context) const {
    for (auto item : list) {
        if (!item->verifyConstant(context))
            return false;
    }
    return true;
}

Statement& BlockStatement::fromSyntax(Compilation& compilation, const BlockStatementSyntax& syntax,
                                      const BindContext& context, StatementContext& stmtCtx) {
    bool anyBad = false;
    SmallVectorSized<const Statement*, 8> buffer;
    for (auto item : syntax.items) {
        auto& stmt =
            Statement::bind(item->as<StatementSyntax>(), context, stmtCtx, /* inList */ true);
        buffer.append(&stmt);
        anyBad |= stmt.bad();
    }

    auto list = compilation.emplace<StatementList>(buffer.copy(compilation));
    auto result = compilation.emplace<BlockStatement>(*list);
    if (anyBad)
        return badStmt(compilation, result);

    return *result;
}

const Statement& BlockStatement::getStatements() const {
    if (block)
        return block->getBody();
    return *list;
}

ER BlockStatement::evalImpl(EvalContext& context) const {
    return getStatements().eval(context);
}

bool BlockStatement::verifyConstantImpl(EvalContext& context) const {
    return getStatements().verifyConstant(context);
}

Statement& ReturnStatement::fromSyntax(Compilation& compilation,
                                       const ReturnStatementSyntax& syntax,
                                       const BindContext& context) {
    // Find the parent subroutine.
    const Scope* scope = &context.scope;
    while (scope->asSymbol().kind == SymbolKind::StatementBlock)
        scope = scope->asSymbol().getParentScope();

    auto stmtLoc = syntax.returnKeyword.location();
    if (scope->asSymbol().kind != SymbolKind::Subroutine) {
        context.addDiag(diag::ReturnNotInSubroutine, stmtLoc);
        return badStmt(compilation, nullptr);
    }

    auto& subroutine = scope->asSymbol().as<SubroutineSymbol>();
    auto& expr =
        Expression::bind(subroutine.getReturnType(), *syntax.returnValue, stmtLoc, context);

    auto result = compilation.emplace<ReturnStatement>(&expr);
    if (expr.bad())
        return badStmt(compilation, result);

    return *result;
}

ER ReturnStatement::evalImpl(EvalContext& context) const {
    // TODO: empty return?
    const SubroutineSymbol* subroutine = context.topFrame().subroutine;
    ASSERT(subroutine);

    ConstantValue* storage = context.findLocal(subroutine->returnValVar);
    ASSERT(storage);

    *storage = expr->eval(context);
    return ER::Return;
}

bool ReturnStatement::verifyConstantImpl(EvalContext& context) const {
    // TODO: empty return
    return expr->verifyConstant(context);
}

Statement& BreakStatement::fromSyntax(Compilation& compilation, const JumpStatementSyntax& syntax,
                                      const BindContext& context, StatementContext& stmtCtx) {
    auto result = compilation.emplace<BreakStatement>();
    if (!stmtCtx.inLoop) {
        context.addDiag(diag::StatementNotInLoop, syntax.sourceRange());
        return badStmt(compilation, result);
    }
    return *result;
}

ER BreakStatement::evalImpl(EvalContext&) const {
    return ER::Break;
}

bool BreakStatement::verifyConstantImpl(EvalContext&) const {
    return true;
}

Statement& ContinueStatement::fromSyntax(Compilation& compilation,
                                         const JumpStatementSyntax& syntax,
                                         const BindContext& context, StatementContext& stmtCtx) {
    auto result = compilation.emplace<ContinueStatement>();
    if (!stmtCtx.inLoop) {
        context.addDiag(diag::StatementNotInLoop, syntax.sourceRange());
        return badStmt(compilation, result);
    }
    return *result;
}

ER ContinueStatement::evalImpl(EvalContext&) const {
    return ER::Continue;
}

bool ContinueStatement::verifyConstantImpl(EvalContext&) const {
    return true;
}

ER VariableDeclStatement::evalImpl(EvalContext& context) const {
    // Create storage for the variable
    ConstantValue initial;
    if (auto initializer = symbol.getInitializer()) {
        initial = initializer->eval(context);
        if (!initial)
            return ER::Fail;
    }

    context.createLocal(&symbol, initial);
    return ER::Success;
}

bool VariableDeclStatement::verifyConstantImpl(EvalContext& context) const {
    if (auto initializer = symbol.getInitializer()) {
        if (!initializer->verifyConstant(context))
            return false;
    }
    return true;
}

Statement& ConditionalStatement::fromSyntax(Compilation& compilation,
                                            const ConditionalStatementSyntax& syntax,
                                            const BindContext& context, StatementContext& stmtCtx) {
    auto& conditions = syntax.predicate->conditions;
    if (conditions.size() == 0)
        return badStmt(compilation, nullptr);

    if (conditions.size() > 1) {
        context.addDiag(diag::NotYetSupported, conditions[1]->sourceRange());
        return badStmt(compilation, nullptr);
    }

    if (conditions[0]->matchesClause) {
        context.addDiag(diag::NotYetSupported, conditions[0]->matchesClause->sourceRange());
        return badStmt(compilation, nullptr);
    }

    auto& cond = Expression::bind(*conditions[0]->expr, context);
    if (cond.bad() || !context.requireBooleanConvertible(cond))
        return badStmt(compilation, nullptr);

    // If the condition is constant, we know which branch will be taken.
    BindFlags ifFlags = BindFlags::None;
    BindFlags elseFlags = BindFlags::None;
    if (cond.constant) {
        if (cond.constant->isTrue())
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

    auto result = compilation.emplace<ConditionalStatement>(cond, ifTrue, ifFalse);
    if (ifTrue.bad() || (ifFalse && ifFalse->bad()))
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

bool ConditionalStatement::verifyConstantImpl(EvalContext& context) const {
    if (!cond.verifyConstant(context) || !ifTrue.verifyConstant(context))
        return false;

    if (ifFalse)
        return ifFalse->verifyConstant(context);

    return true;
}

Statement& CaseStatement::fromSyntax(Compilation& compilation, const CaseStatementSyntax& syntax,
                                     const BindContext& context, StatementContext& stmtCtx) {
    if (syntax.matchesOrInside) {
        context.addDiag(diag::NotYetSupported, syntax.matchesOrInside.range());
        return badStmt(compilation, nullptr);
    }

    Condition condition;
    switch (syntax.caseKeyword.kind) {
        case TokenKind::CaseKeyword:
            condition = Condition::Normal;
            break;
        case TokenKind::CaseXKeyword:
            condition = Condition::WildcardXOrZ;
            break;
        case TokenKind::CaseZKeyword:
            condition = Condition::WildcardJustZ;
            break;
        default:
            THROW_UNREACHABLE;
    }

    Check check;
    switch (syntax.uniqueOrPriority.kind) {
        case TokenKind::Unknown:
            check = Check::None;
            break;
        case TokenKind::UniqueKeyword:
            check = Check::Unique;
            break;
        case TokenKind::Unique0Keyword:
            check = Check::Unique0;
            break;
        case TokenKind::PriorityKeyword:
            check = Check::Priority;
            break;
        default:
            THROW_UNREACHABLE;
    }

    SmallVectorSized<const ExpressionSyntax*, 8> expressions;
    SmallVectorSized<const Statement*, 8> statements;
    const Statement* defStmt = nullptr;
    bool bad = false;

    // TODO: check for cases we statically know we can never hit
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
    bad |= !Expression::bindCaseExpressions(context, syntax.caseKeyword.kind, *syntax.expr,
                                            expressions, bound);

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

    auto result = compilation.emplace<CaseStatement>(condition, check, *expr,
                                                     items.copy(compilation), defStmt);
    if (bad)
        return badStmt(compilation, result);

    return *result;
}

static bool checkMatch(CaseStatement::Condition condition, const ConstantValue& cvl,
                       const ConstantValue& cvr) {

    if (condition != CaseStatement::Condition::Normal) {
        const SVInt& l = cvl.integer();
        const SVInt& r = cvr.integer();
        if (condition == CaseStatement::Condition::WildcardJustZ)
            return caseZWildcardEqual(l, r);
        else
            return caseXWildcardEqual(l, r);
    }

    return cvl.equivalentTo(cvr);
}

ER CaseStatement::evalImpl(EvalContext& context) const {
    auto cv = expr.eval(context);
    if (!cv)
        return ER::Fail;

    const Statement* matchedStmt = nullptr;
    SourceRange matchRange;
    bool unique = check == Check::Unique || check == Check::Unique0;

    for (auto& group : items) {
        for (auto item : group.expressions) {
            auto val = item->eval(context);
            if (!val)
                return ER::Fail;

            if (checkMatch(condition, cv, val)) {
                // If we already matched with a previous item, the only we reason
                // we'd still get here is to check for uniqueness. The presence of
                // another match means we failed the uniqueness check.
                if (matchedStmt) {
                    context.addDiag(diag::NoteCaseItemsNotUnique, item->sourceRange) << val;
                    context.addDiag(diag::NotePreviousMatch, matchRange);
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

    if (check == Check::Priority || check == Check::Unique) {
        auto& diag = context.addDiag(diag::NoteNoCaseItemsMatched, expr.sourceRange);
        diag << (check == Check::Priority ? "priority"sv : "unique"sv);
        diag << cv;
    }

    return ER::Success;
}

bool CaseStatement::verifyConstantImpl(EvalContext& context) const {
    if (!expr.verifyConstant(context))
        return false;

    for (auto& group : items) {
        for (auto item : group.expressions) {
            if (!item->verifyConstant(context))
                return false;
        }
        if (!group.stmt->verifyConstant(context))
            return false;
    }

    if (defaultCase)
        return defaultCase->verifyConstant(context);

    return true;
}

Statement& ForLoopStatement::fromSyntax(Compilation& compilation,
                                        const ForLoopStatementSyntax& syntax,
                                        const BindContext& context, StatementContext& stmtCtx) {
    auto guard = stmtCtx.enterLoop();

    // If the initializers were variable declarations, they've already been hoisted
    // out into a parent block and will be initialized there.
    SmallVectorSized<const Expression*, 4> initializers;
    bool anyBad = false;
    if (!syntax.initializers.empty() &&
        syntax.initializers[0]->kind != SyntaxKind::ForVariableDeclaration) {

        for (auto initializer : syntax.initializers) {
            auto& init = Expression::bind(initializer->as<ExpressionSyntax>(), context);
            initializers.append(&init);
            anyBad |= init.bad();
        }
    }

    SmallVectorSized<const Expression*, 2> steps;
    auto& stopExpr = Expression::bind(*syntax.stopExpr, context);
    for (auto step : syntax.steps) {
        auto& expr = Expression::bind(*step, context);
        steps.append(&expr);
        anyBad |= expr.bad();
    }

    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<ForLoopStatement>(initializers.copy(compilation), &stopExpr,
                                                        steps.copy(compilation), bodyStmt);

    if (anyBad || stopExpr.bad() || bodyStmt.bad())
        return badStmt(compilation, result);
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
            else if (result == ER::Fail || result == ER::Return)
                return result;
        }

        for (auto step : steps) {
            if (!step->eval(context))
                return ER::Fail;
        }
    }

    return ER::Success;
}

bool ForLoopStatement::verifyConstantImpl(EvalContext& context) const {
    for (auto init : initializers) {
        if (!init->verifyConstant(context))
            return false;
    }

    if (stopExpr && !stopExpr->verifyConstant(context))
        return false;

    for (auto step : steps) {
        if (!step->verifyConstant(context))
            return false;
    }

    return body.verifyConstant(context);
}

Statement& RepeatLoopStatement::fromSyntax(Compilation& compilation,
                                           const LoopStatementSyntax& syntax,
                                           const BindContext& context, StatementContext& stmtCtx) {
    auto guard = stmtCtx.enterLoop();
    auto& countExpr = Expression::bind(*syntax.expr, context);

    bool bad = countExpr.bad();
    if (!bad && !countExpr.type->isIntegral()) {
        context.addDiag(diag::ExprMustBeIntegral, countExpr.sourceRange);
        bad = true;
    }

    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<RepeatLoopStatement>(countExpr, bodyStmt);

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
            else if (result == ER::Fail || result == ER::Return)
                return result;
        }
    }

    return ER::Success;
}

bool RepeatLoopStatement::verifyConstantImpl(EvalContext& context) const {
    return count.verifyConstant(context) && body.verifyConstant(context);
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
    auto result = compilation.emplace<WhileLoopStatement>(condExpr, bodyStmt);

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
            else if (result == ER::Fail || result == ER::Return)
                return result;
        }
    }

    return ER::Success;
}

bool WhileLoopStatement::verifyConstantImpl(EvalContext& context) const {
    return cond.verifyConstant(context) && body.verifyConstant(context);
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
    auto result = compilation.emplace<DoWhileLoopStatement>(condExpr, bodyStmt);

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
            else if (result == ER::Fail || result == ER::Return)
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

bool DoWhileLoopStatement::verifyConstantImpl(EvalContext& context) const {
    return cond.verifyConstant(context) && body.verifyConstant(context);
}

Statement& ForeverLoopStatement::fromSyntax(Compilation& compilation,
                                            const ForeverStatementSyntax& syntax,
                                            const BindContext& context, StatementContext& stmtCtx) {
    auto guard = stmtCtx.enterLoop();

    auto& bodyStmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<ForeverLoopStatement>(bodyStmt);
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
            else if (result == ER::Fail || result == ER::Return)
                return result;
        }
    }

    return ER::Success;
}

bool ForeverLoopStatement::verifyConstantImpl(EvalContext& context) const {
    return body.verifyConstant(context);
}

Statement& ExpressionStatement::fromSyntax(Compilation& compilation,
                                           const ExpressionStatementSyntax& syntax,
                                           const BindContext& context) {
    auto& expr = Expression::bind(*syntax.expr, context);
    auto result = compilation.emplace<ExpressionStatement>(expr);
    if (expr.bad())
        return badStmt(compilation, result);

    // Only a subset of expressions are allowed as statements.
    bool ok;
    switch (expr.kind) {
        case ExpressionKind::Call:
        case ExpressionKind::Assignment:
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

ER ExpressionStatement::evalImpl(EvalContext& context) const {
    return expr.eval(context) ? ER::Success : ER::Fail;
}

bool ExpressionStatement::verifyConstantImpl(EvalContext& context) const {
    return expr.verifyConstant(context);
}

Statement& TimedStatement::fromSyntax(Compilation& compilation,
                                      const TimingControlStatementSyntax& syntax,
                                      const BindContext& context, StatementContext& stmtCtx) {
    auto& timing = TimingControl::bind(*syntax.timingControl, context);
    auto& stmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<TimedStatement>(timing, stmt);

    if (timing.bad() || stmt.bad())
        return badStmt(compilation, result);

    return *result;
}

ER TimedStatement::evalImpl(EvalContext& context) const {
    if (context.isScriptEval())
        return stmt.eval(context);

    return ER::Fail;
}

bool TimedStatement::verifyConstantImpl(EvalContext& context) const {
    if (context.isScriptEval())
        return true;

    ASSERT(timing.syntax);
    context.addDiag(diag::NoteTimedStmtNotConst, timing.syntax->sourceRange());
    return false;
}

Statement& AssertionStatement::fromSyntax(Compilation& compilation,
                                          const ImmediateAssertionStatementSyntax& syntax,
                                          const BindContext& context, StatementContext& stmtCtx) {
    AssertionKind assertKind = SemanticFacts::getAssertKind(syntax.kind);
    auto& cond = Expression::bind(*syntax.expr->expression, context);
    if (cond.bad() || !context.requireBooleanConvertible(cond))
        return badStmt(compilation, nullptr);

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

    if (assertKind == AssertionKind::Cover && ifFalse)
        context.addDiag(diag::CoverStmtNoFail, syntax.action->elseClause->sourceRange());

    // TODO: add checking for requirements on deferred assertion actions

    auto result = compilation.emplace<AssertionStatement>(assertKind, cond, ifTrue, ifFalse,
                                                          isDeferred, isFinal);
    if ((ifTrue && ifTrue->bad()) || (ifFalse && ifFalse->bad()))
        return badStmt(compilation, result);

    return *result;
}

ER AssertionStatement::evalImpl(EvalContext& context) const {
    auto result = cond.eval(context);
    if (result.bad())
        return ER::Fail;

    if (result.isTrue()) {
        if (ifTrue)
            return ifTrue->eval(context);
        return ER::Success;
    }

    if (ifFalse)
        return ifFalse->eval(context);

    if (assertionKind == AssertionKind::Cover)
        return ER::Success;

    // TODO: give statements a guaranteed SourceRange member
    ASSERT(cond.syntax);
    context.addDiag(diag::NoteAssertionFailed, cond.syntax->sourceRange());
    return ER::Fail;
}

bool AssertionStatement::verifyConstantImpl(EvalContext& context) const {
    if (!cond.verifyConstant(context))
        return false;

    if (ifTrue && !ifTrue->verifyConstant(context))
        return false;

    if (ifFalse && !ifFalse->verifyConstant(context))
        return false;

    if (isDeferred) {
        // TODO: give statements a guaranteed SourceRange member
        ASSERT(syntax);
        context.addDiag(diag::NoteTimedStmtNotConst, syntax->sourceRange());
        return false;
    }

    return true;
}

} // namespace slang
