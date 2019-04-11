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
#include "slang/symbols/ASTVisitor.h"

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

const Statement& Statement::bind(const StatementSyntax& syntax, const BindContext& context,
                                 span<const SequentialBlockSymbol* const>& blocks) {
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
            break;
        case SyntaxKind::ReturnStatement:
            result =
                &ReturnStatement::fromSyntax(comp, syntax.as<ReturnStatementSyntax>(), context);
            break;
        case SyntaxKind::ConditionalStatement:
            result = &ConditionalStatement::fromSyntax(
                comp, syntax.as<ConditionalStatementSyntax>(), context, blocks);
            break;
        case SyntaxKind::CaseStatement:
            result =
                &CaseStatement::fromSyntax(comp, syntax.as<CaseStatementSyntax>(), context, blocks);
            break;
        case SyntaxKind::ForLoopStatement:
            // We might have an implicit block here; check for that first.
            if (!blocks.empty() && blocks[0]->getSyntax() == &syntax) {
                result = comp.emplace<SequentialBlockStatement>(*blocks[0]);
                blocks = blocks.subspan(1);
            }
            else {
                result = &ForLoopStatement::fromSyntax(comp, syntax.as<ForLoopStatementSyntax>(),
                                                       context, blocks);
            }
            break;
        case SyntaxKind::ExpressionStatement:
            result = &ExpressionStatement::fromSyntax(comp, syntax.as<ExpressionStatementSyntax>(),
                                                      context);
            break;
        case SyntaxKind::SequentialBlockStatement:
            // A block statement may or may not match up with a hierarchy node. Handle both cases
            // here. We traverse statements in the same order as the findScopes call below, so this
            // should always sync up exactly.
            if (!blocks.empty() && blocks[0]->getSyntax() == &syntax) {
                result = comp.emplace<SequentialBlockStatement>(*blocks[0]);
                blocks = blocks.subspan(1);
            }
            else {
                result = &SequentialBlockStatement::fromSyntax(
                    comp, syntax.as<BlockStatementSyntax>(), context, blocks);
            }
            break;
        case SyntaxKind::TimingControlStatement:
            result = &TimedStatement::fromSyntax(comp, syntax.as<TimingControlStatementSyntax>(),
                                                 context, blocks);
            break;
        case SyntaxKind::JumpStatement:
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
        case SyntaxKind::ForeverStatement:
        case SyntaxKind::LoopStatement:
        case SyntaxKind::DoWhileStatement:
        case SyntaxKind::ForeachLoopStatement:
        case SyntaxKind::WaitStatement:
        case SyntaxKind::RandCaseStatement:
        case SyntaxKind::ImmediateAssertStatement:
        case SyntaxKind::ImmediateAssumeStatement:
        case SyntaxKind::ImmediateCoverStatement:
        case SyntaxKind::AssertPropertyStatement:
        case SyntaxKind::AssumePropertyStatement:
        case SyntaxKind::CoverSequenceStatement:
        case SyntaxKind::CoverPropertyStatement:
        case SyntaxKind::RestrictPropertyStatement:
        case SyntaxKind::ExpectPropertyStatement:
        case SyntaxKind::WaitOrderStatement:
            context.addDiag(DiagCode::NotYetSupported, syntax.sourceRange());
            result = &badStmt(comp, nullptr);
            break;
        default:
            THROW_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

Statement& Statement::badStmt(Compilation& compilation, const Statement* stmt) {
    return *compilation.emplace<InvalidStatement>(stmt);
}

static void findBlocks(const Scope& scope, const StatementSyntax& syntax,
                       SmallVector<const SequentialBlockSymbol*>& results) {
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
                results.append(&SequentialBlockSymbol::fromSyntax(scope.getCompilation(), block));
                return;
            }

            for (auto item : block.items) {
                // If we find any decls at all, this block gets its own scope.
                if (!StatementSyntax::isKind(item->kind)) {
                    results.append(
                        &SequentialBlockSymbol::fromSyntax(scope.getCompilation(), block));
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

                results.append(&SequentialBlockSymbol::fromSyntax(scope.getCompilation(), forLoop));
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
        case SyntaxKind::ImmediateCoverStatement:
        case SyntaxKind::AssertPropertyStatement:
        case SyntaxKind::AssumePropertyStatement:
        case SyntaxKind::CoverSequenceStatement:
        case SyntaxKind::CoverPropertyStatement:
        case SyntaxKind::RestrictPropertyStatement:
        case SyntaxKind::ExpectPropertyStatement:
        case SyntaxKind::WaitOrderStatement:
            scope.addDiag(DiagCode::NotYetSupported, syntax.sourceRange());
            return;
        default:
            THROW_UNREACHABLE;
    }
}

void StatementBinder::setSyntax(const Scope& scope, const StatementSyntax& syntax_) {
    stmt = nullptr;
    syntax = &syntax_;

    SmallVectorSized<const SequentialBlockSymbol*, 8> buffer;
    findBlocks(scope, syntax_, buffer);
    blocks = buffer.copy(scope.getCompilation());
}

void StatementBinder::setSyntax(const SequentialBlockSymbol& scope,
                                const ForLoopStatementSyntax& syntax_) {
    stmt = nullptr;
    syntax = &syntax_;

    SmallVectorSized<const SequentialBlockSymbol*, 8> buffer;
    findBlocks(scope, *syntax_.statement, buffer);
    blocks = buffer.copy(scope.getCompilation());
}

void StatementBinder::setItems(Scope& scope, const SyntaxList<SyntaxNode>& items) {
    stmt = nullptr;
    syntax = &items;

    SmallVectorSized<const SequentialBlockSymbol*, 8> buffer;
    for (auto item : items) {
        switch (item->kind) {
            case SyntaxKind::DataDeclaration:
            case SyntaxKind::TypedefDeclaration:
            case SyntaxKind::ForwardTypedefDeclaration:
            case SyntaxKind::ForwardInterfaceClassTypedefDeclaration:
            case SyntaxKind::PackageImportDeclaration:
                scope.addMembers(*item);
                break;
            case SyntaxKind::PortDeclaration:
            case SyntaxKind::ParameterDeclarationStatement:
            case SyntaxKind::LetDeclaration:
            case SyntaxKind::NetTypeDeclaration:
                scope.addDiag(DiagCode::NotYetSupported, item->sourceRange());
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

const Statement& StatementBinder::getStatement(const Scope& scope, LookupLocation location) const {
    if (!stmt)
        stmt = &bindStatement(scope, location);
    return *stmt;
}

const Statement& StatementBinder::bindStatement(const Scope& scope, LookupLocation location) const {
    auto& comp = scope.getCompilation();
    BindContext context(scope, location);
    SmallVectorSized<const Statement*, 8> buffer;

    auto scopeKind = scope.asSymbol().kind;
    if (scopeKind == SymbolKind::SequentialBlock || scopeKind == SymbolKind::Subroutine) {
        // This relies on the language requiring all declarations be at the start
        // of a statement block. Additional work would be required to support
        // declarations anywhere in the block.
        for (auto& member : scope.members()) {
            if (member.kind != SymbolKind::Variable)
                continue;

            // Filter out implicitly generate function return type variables,
            // they are initialized elsewhere.
            auto& var = member.as<VariableSymbol>();
            if (!var.isCompilerGenerated)
                buffer.append(comp.emplace<VariableDeclStatement>(var));
        }
    }

    auto blocksCopy = blocks;
    if (auto stmtSyntax = std::get_if<const StatementSyntax*>(&syntax)) {
        if (auto ptr = *stmtSyntax)
            buffer.append(&Statement::bind(*ptr, context, blocksCopy));
    }
    else {
        auto& items = *std::get<const SyntaxList<SyntaxNode>*>(syntax);
        for (auto item : items) {
            if (StatementSyntax::isKind(item->kind))
                buffer.append(&Statement::bind(item->as<StatementSyntax>(), context, blocksCopy));
        }
    }

    ASSERT(blocksCopy.empty());

    if (buffer.empty())
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

Statement& SequentialBlockStatement::fromSyntax(Compilation& compilation,
                                                const BlockStatementSyntax& syntax,
                                                const BindContext& context, BlockList& blocks) {
    SmallVectorSized<const Statement*, 8> buffer;
    for (auto item : syntax.items)
        buffer.append(&Statement::bind(item->as<StatementSyntax>(), context, blocks));

    auto list = compilation.emplace<StatementList>(buffer.copy(compilation));
    return *compilation.emplace<SequentialBlockStatement>(*list);
}

const Statement& SequentialBlockStatement::getStatements() const {
    if (block)
        return block->getBody();
    return *list;
}

ER SequentialBlockStatement::evalImpl(EvalContext& context) const {
    return getStatements().eval(context);
}

bool SequentialBlockStatement::verifyConstantImpl(EvalContext& context) const {
    return getStatements().verifyConstant(context);
}

Statement& ReturnStatement::fromSyntax(Compilation& compilation,
                                       const ReturnStatementSyntax& syntax,
                                       const BindContext& context) {
    // Find the parent subroutine.
    const Scope* scope = &context.scope;
    while (scope->asSymbol().kind == SymbolKind::SequentialBlock)
        scope = scope->getParent();

    auto stmtLoc = syntax.returnKeyword.location();
    if (scope->asSymbol().kind != SymbolKind::Subroutine) {
        context.addDiag(DiagCode::ReturnNotInSubroutine, stmtLoc);
        return badStmt(compilation, nullptr);
    }

    auto& subroutine = scope->asSymbol().as<SubroutineSymbol>();
    auto& expr =
        Expression::bind(subroutine.getReturnType(), *syntax.returnValue, stmtLoc, context);

    return *compilation.emplace<ReturnStatement>(&expr);
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
                                            const BindContext& context, BlockList& blocks) {
    ASSERT(syntax.predicate->conditions.size() == 1);
    ASSERT(!syntax.predicate->conditions[0]->matchesClause);

    auto& cond = Expression::bind(*syntax.predicate->conditions[0]->expr, context);
    auto& ifTrue = Statement::bind(*syntax.statement, context, blocks);
    const Statement* ifFalse = nullptr;
    if (syntax.elseClause)
        ifFalse =
            &Statement::bind(syntax.elseClause->clause->as<StatementSyntax>(), context, blocks);

    return *compilation.emplace<ConditionalStatement>(cond, ifTrue, ifFalse);
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
                                     const BindContext& context, BlockList& blocks) {
    if (syntax.matchesOrInside) {
        context.addDiag(DiagCode::NotYetSupported, syntax.matchesOrInside.range());
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
                auto& stmt = Statement::bind(sci.clause->as<StatementSyntax>(), context, blocks);
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
                        blocks);
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
                for (ptrdiff_t i = 0; i < sci.expressions.size(); i++) {
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
                    context.addDiag(DiagCode::NoteCaseItemsNotUnique, item->sourceRange) << val;
                    context.addDiag(DiagCode::NotePreviousMatch, matchRange);
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
        auto& diag = context.addDiag(DiagCode::NoteNoCaseItemsMatched, expr.sourceRange);
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
                                        const BindContext& context, BlockList& blocks) {
    // If the initializers were variable declarations, they've already been hoisted
    // out into a parent block and will be initialized there.
    SmallVectorSized<const Statement*, 4> initializers;
    if (syntax.initializers.empty() ||
        syntax.initializers[0]->kind != SyntaxKind::ForVariableDeclaration) {

        BlockList emptySpan;
        for (auto initializer : syntax.initializers) {
            initializers.append(
                &Statement::bind(initializer->as<StatementSyntax>(), context, emptySpan));
        }
    }

    SmallVectorSized<const Expression*, 2> steps;
    auto& stopExpr = Expression::bind(*syntax.stopExpr, context);
    for (auto step : syntax.steps)
        steps.append(&Expression::bind(*step, context));

    auto& bodyStmt = Statement::bind(*syntax.statement, context, blocks);
    auto initList = compilation.emplace<StatementList>(initializers.copy(compilation));
    return *compilation.emplace<ForLoopStatement>(*initList, &stopExpr, steps.copy(compilation),
                                                  bodyStmt);
}

ER ForLoopStatement::evalImpl(EvalContext& context) const {
    if (ER result = initializers.eval(context); result != ER::Success)
        return result;

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
    if (!initializers.verifyConstant(context))
        return false;

    if (stopExpr && !stopExpr->verifyConstant(context))
        return false;

    for (auto step : steps) {
        if (!step->verifyConstant(context))
            return false;
    }

    return body.verifyConstant(context);
}

Statement& ExpressionStatement::fromSyntax(Compilation& compilation,
                                           const ExpressionStatementSyntax& syntax,
                                           const BindContext& context) {
    auto& expr = Expression::bind(*syntax.expr, context);
    return *compilation.emplace<ExpressionStatement>(expr);
}

ER ExpressionStatement::evalImpl(EvalContext& context) const {
    return expr.eval(context) ? ER::Success : ER::Fail;
}

bool ExpressionStatement::verifyConstantImpl(EvalContext& context) const {
    return expr.verifyConstant(context);
}

Statement& TimedStatement::fromSyntax(Compilation& compilation,
                                      const TimingControlStatementSyntax& syntax,
                                      const BindContext& context, BlockList& blocks) {
    auto& timing = TimingControl::bind(*syntax.timingControl, context);
    auto& stmt = Statement::bind(*syntax.statement, context, blocks);
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
    context.addDiag(DiagCode::NoteTimedStmtNotConst, timing.syntax->sourceRange());
    return false;
}

} // namespace slang
