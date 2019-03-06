//------------------------------------------------------------------------------
// StatementBodiedScope.cpp
// Statement binding.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/StatementBodiedScope.h"

#include "slang/binding/Statements.h"
#include "slang/compilation/Compilation.h"

namespace slang {

void StatementBodiedScope::setBody(const StatementSyntax& newSyntax) {
    sourceSyntax = &newSyntax;
    setStatement(*this);
}

void StatementBodiedScope::setBody(const SyntaxList<SyntaxNode>& newSyntax) {
    sourceSyntax = &newSyntax;
    setStatement(*this);
}

void StatementBodiedScope::bindBody() {
    ASSERT(sourceSyntax);
    if (sourceSyntax->kind == SyntaxKind::SyntaxList)
        setBody(&bindStatementList(*(const SyntaxList<SyntaxNode>*)sourceSyntax));
    else
        setBody(&bindStatement(sourceSyntax->as<StatementSyntax>(),
                               BindContext(*this, LookupLocation::max)));
}

void StatementBodiedScope::findScopes(const Scope& scope, const StatementSyntax& syntax,
                                      SmallVector<Symbol*>& results) {
    // TODO:
    /*if (syntax.label) {
        results.append(SequentialBlockSymbol::fromLabeledStmt(scope.getCompilation(), syntax));
        return;
    }*/

    auto recurse = [&](auto stmt) { findScopes(scope, *stmt, results); };

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
            break;

        case SyntaxKind::SequentialBlockStatement:
        case SyntaxKind::ParallelBlockStatement: {
            // Block statements form their own hierarhcy scope if:
            // - They have a name
            // - They are unnamed but have variable declarations within them
            auto& block = syntax.as<BlockStatementSyntax>();
            if (block.blockName) {
                results.append(&SequentialBlockSymbol::fromSyntax(scope.getCompilation(), block));
                return;
            }

            for (auto item : block.items) {
                if (StatementSyntax::isKind(item->kind))
                    recurse(&item->as<StatementSyntax>());
                else {
                    // This takes advantage of the fact that in a well formed program,
                    // all declaration in this block must be at the start, before
                    // any statements. The parser will enforce this for us.
                    results.append(
                        &SequentialBlockSymbol::fromSyntax(scope.getCompilation(), block));
                    return;
                }
            }
            break;
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
            break;
        case SyntaxKind::ConditionalStatement: {
            auto& cond = syntax.as<ConditionalStatementSyntax>();
            recurse(cond.statement);
            if (cond.elseClause)
                recurse(&cond.elseClause->clause->as<StatementSyntax>());
            break;
        }
        case SyntaxKind::ForeverStatement:
            recurse(syntax.as<ForeverStatementSyntax>().statement);
            break;
        case SyntaxKind::LoopStatement:
            recurse(syntax.as<LoopStatementSyntax>().statement);
            break;
        case SyntaxKind::DoWhileStatement:
            recurse(syntax.as<DoWhileStatementSyntax>().statement);
            break;
        case SyntaxKind::ForLoopStatement:
            recurse(syntax.as<ForLoopStatementSyntax>().statement);
            break;
        case SyntaxKind::ForeachLoopStatement:
            recurse(syntax.as<ForeachLoopStatementSyntax>().statement);
            break;
        case SyntaxKind::TimingControlStatement:
            recurse(syntax.as<TimingControlStatementSyntax>().statement);
            break;
        case SyntaxKind::WaitStatement:
            recurse(syntax.as<WaitStatementSyntax>().statement);
            break;
        case SyntaxKind::RandCaseStatement:
            for (auto item : syntax.as<RandCaseStatementSyntax>().items)
                recurse(item->statement);
            break;

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
            break;
        default:
            THROW_UNREACHABLE;
    }
}

Statement& StatementBodiedScope::bindStatement(const StatementSyntax& syntax,
                                               const BindContext& context) {
    switch (syntax.kind) {
        case SyntaxKind::ReturnStatement:
            return bindReturnStatement(syntax.as<ReturnStatementSyntax>(), context);
        case SyntaxKind::ConditionalStatement:
            return bindConditionalStatement(syntax.as<ConditionalStatementSyntax>(), context);
        case SyntaxKind::ForLoopStatement:
            return bindForLoopStatement(syntax.as<ForLoopStatementSyntax>(), context);
        case SyntaxKind::ExpressionStatement:
            return bindExpressionStatement(syntax.as<ExpressionStatementSyntax>(), context);
        case SyntaxKind::SequentialBlockStatement:
            return bindBlockStatement(syntax.as<BlockStatementSyntax>(), context);
        default:
            addDiag(DiagCode::NotYetSupported, syntax.sourceRange());
            return badStmt(nullptr);
    }
}

Statement& StatementBodiedScope::bindStatementList(const SyntaxList<SyntaxNode>& items) {
    BindContext context(*this, LookupLocation::min);
    SmallVectorSized<const Statement*, 8> buffer;
    for (auto item : items) {
        // Each bindStatement call can potentially add more members to our scope, so keep
        // updating our lookup location so that future expressions can bind to them.
        if (const Symbol* last = getLastMember())
            context.lookupLocation = LookupLocation::after(*last);

        switch (item->kind) {
            case SyntaxKind::DataDeclaration:
                bindVariableDecl(item->as<DataDeclarationSyntax>(), context, buffer);
                break;
            case SyntaxKind::TypedefDeclaration:
            case SyntaxKind::ForwardTypedefDeclaration:
            case SyntaxKind::ForwardInterfaceClassTypedefDeclaration:
            case SyntaxKind::PackageImportDeclaration:
                addMembers(*item);
                break;
            case SyntaxKind::PortDeclaration:
            case SyntaxKind::ParameterDeclarationStatement:
            case SyntaxKind::LetDeclaration:
            case SyntaxKind::NetTypeDeclaration:
                addDiag(DiagCode::NotYetSupported, item->sourceRange());
                break;
            default:
                if (StatementSyntax::isKind(item->kind))
                    buffer.append(&bindStatement(item->as<StatementSyntax>(), context));
                else
                    THROW_UNREACHABLE;
        }
    }

    return *getCompilation().emplace<StatementList>(buffer.copy(getCompilation()));
}

void StatementBodiedScope::bindVariableDecl(const DataDeclarationSyntax& syntax,
                                            const BindContext& context,
                                            SmallVector<const Statement*>& statements) {
    // TODO: check for non-variables
    SmallVectorSized<const ValueSymbol*, 4> variables;
    VariableSymbol::fromSyntax(getCompilation(), syntax, context.scope, variables);

    for (auto variable : variables) {
        addMember(*variable);
        statements.append(
            getCompilation().emplace<VariableDeclStatement>(variable->as<VariableSymbol>()));
    }
}

Statement& StatementBodiedScope::bindReturnStatement(const ReturnStatementSyntax& syntax,
                                                     const BindContext& context) {
    auto stmtLoc = syntax.returnKeyword.location();
    const Symbol* subroutine = asSymbol().findAncestor(SymbolKind::Subroutine);
    if (!subroutine) {
        addDiag(DiagCode::ReturnNotInSubroutine, stmtLoc);
        return badStmt(nullptr);
    }

    auto& expr = Expression::bind(subroutine->as<SubroutineSymbol>().getReturnType(),
                                  *syntax.returnValue, stmtLoc, context);

    Compilation& comp = getCompilation();
    return *comp.emplace<ReturnStatement>(syntax, &expr);
}

Statement& StatementBodiedScope::bindConditionalStatement(const ConditionalStatementSyntax& syntax,
                                                          const BindContext& context) {
    ASSERT(syntax.predicate->conditions.size() == 1);
    ASSERT(!syntax.predicate->conditions[0]->matchesClause);

    const auto& cond = Expression::bind(*syntax.predicate->conditions[0]->expr, context);
    const auto& ifTrue = bindStatement(*syntax.statement, context);
    const Statement* ifFalse = nullptr;
    if (syntax.elseClause)
        ifFalse = &bindStatement(syntax.elseClause->clause->as<StatementSyntax>(), context);

    Compilation& comp = getCompilation();
    return *comp.emplace<ConditionalStatement>(syntax, cond, ifTrue, ifFalse);
}

Statement& StatementBodiedScope::bindForLoopStatement(const ForLoopStatementSyntax& syntax,
                                                      const BindContext& context) {
    // If the initializers here involve doing variable declarations, then the spec says we create
    // an implicit sequential block and do the declaration there. Otherwise we'll just
    // end up returning the for statement directly.
    StatementBodiedScope* forScope = this;
    SequentialBlockStatement* implicitBlockStmt = nullptr;
    SmallVectorSized<const Statement*, 4> initializers;
    std::optional<BindContext> nestedContext;
    const BindContext* forContext = &context;

    Compilation& comp = getCompilation();
    if (!syntax.initializers.empty() &&
        syntax.initializers[0]->kind == SyntaxKind::ForVariableDeclaration) {

        auto implicitBlock =
            comp.emplace<SequentialBlockSymbol>(comp, syntax.forKeyword.location());
        implicitBlockStmt = comp.emplace<SequentialBlockStatement>(*implicitBlock);

        addMember(*implicitBlock);
        forScope = implicitBlock;
        nestedContext.emplace(*forScope, LookupLocation::max);
        forContext = &nestedContext.value();

        for (auto initializer : syntax.initializers) {
            // If one entry is a variable declaration, they should all be. Checked by the parser.
            ASSERT(initializer->kind == SyntaxKind::ForVariableDeclaration);

            auto& var =
                VariableSymbol::fromSyntax(comp, initializer->as<ForVariableDeclarationSyntax>());
            implicitBlock->addMember(var);
            initializers.append(comp.emplace<VariableDeclStatement>(var));
        }
    }
    else {
        for (auto initializer : syntax.initializers)
            initializers.append(&bindStatement(initializer->as<StatementSyntax>(), *forContext));
    }

    SmallVectorSized<const Expression*, 2> steps;
    const auto& stopExpr = Expression::bind(*syntax.stopExpr, *forContext);
    for (auto step : syntax.steps)
        steps.append(&Expression::bind(*step, *forContext));

    const auto& bodyStmt = forScope->bindStatement(*syntax.statement, *forContext);
    auto initList = comp.emplace<StatementList>(initializers.copy(comp));
    auto loop =
        comp.emplace<ForLoopStatement>(syntax, *initList, &stopExpr, steps.copy(comp), bodyStmt);

    // If we had an implicit block created to wrap the for loop, set the loop as the body
    // of that block and return it. Otherwise, just return the loop itself.
    if (implicitBlockStmt) {
        forScope->setBody(loop);
        return *implicitBlockStmt;
    }
    return *loop;
}

Statement& StatementBodiedScope::bindExpressionStatement(const ExpressionStatementSyntax& syntax,
                                                         const BindContext& context) {
    Compilation& comp = getCompilation();
    const auto& expr = Expression::bind(*syntax.expr, context);
    return *comp.emplace<ExpressionStatement>(syntax, expr);
}

Statement& StatementBodiedScope::bindBlockStatement(const BlockStatementSyntax& syntax,
                                                    const BindContext&) {
    Compilation& comp = getCompilation();
    auto& symbol = SequentialBlockSymbol::fromSyntax(comp, syntax);
    addMember(symbol);
    return *comp.emplace<SequentialBlockStatement>(symbol);
}

Statement& StatementBodiedScope::badStmt(const Statement* stmt) {
    return *getCompilation().emplace<InvalidStatement>(stmt);
}

} // namespace slang