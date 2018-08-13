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

void StatementBodiedScope::setBody(const StatementSyntax& syntax) {
    setStatement(syntax);
}

void StatementBodiedScope::setBody(const SyntaxList<SyntaxNode>& syntax) {
    setStatement(syntax);
}

void StatementBodiedScope::bindBody(const SyntaxNode& syntax) {
    if (syntax.kind == SyntaxKind::SyntaxList)
        setBody(&bindStatementList((const SyntaxList<SyntaxNode>&)syntax));
    else
        setBody(&bindStatement(syntax.as<StatementSyntax>(), BindContext(*this, LookupLocation::max)));
}

Statement& StatementBodiedScope::bindStatement(const StatementSyntax& syntax, const BindContext& context) {
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
            THROW_UNREACHABLE;
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
                bindVariableDecl(item->as<DataDeclarationSyntax>(), buffer);
                break;
            case SyntaxKind::TypedefDeclaration:
            case SyntaxKind::ForwardTypedefDeclaration:
            case SyntaxKind::ForwardInterfaceClassTypedefDeclaration:
            case SyntaxKind::PackageImportDeclaration:
                addMembers(*item);
                break;
            default:
                if (isStatement(item->kind))
                    buffer.append(&bindStatement(item->as<StatementSyntax>(), context));
                else
                    THROW_UNREACHABLE;
        }
    }

    return *getCompilation().emplace<StatementList>(buffer.copy(getCompilation()));
}

void StatementBodiedScope::bindVariableDecl(const DataDeclarationSyntax& syntax,
                                            SmallVector<const Statement*>& statements) {
    SmallVectorSized<const VariableSymbol*, 4> variables;
    VariableSymbol::fromSyntax(getCompilation(), syntax, variables);

    for (auto variable : variables) {
        addMember(*variable);
        statements.append(getCompilation().emplace<VariableDeclStatement>(*variable));
    }
}

Statement& StatementBodiedScope::bindReturnStatement(const ReturnStatementSyntax& syntax,
                                                     const BindContext& context) {
    Compilation& comp = getCompilation();
    auto stmtLoc = syntax.returnKeyword.location();
    const Symbol* subroutine = asSymbol().findAncestor(SymbolKind::Subroutine);
    if (!subroutine) {
        comp.addError(DiagCode::ReturnNotInSubroutine, stmtLoc);
        return badStmt(nullptr);
    }

    const auto& expr = Expression::bind(comp, subroutine->as<SubroutineSymbol>().getReturnType(),
                                        *syntax.returnValue, stmtLoc, context);
    return *comp.emplace<ReturnStatement>(syntax, &expr);
}

Statement& StatementBodiedScope::bindConditionalStatement(const ConditionalStatementSyntax& syntax,
                                                          const BindContext& context) {
    ASSERT(syntax.predicate->conditions.size() == 1);
    ASSERT(!syntax.predicate->conditions[0]->matchesClause);

    Compilation& comp = getCompilation();
    const auto& cond = Expression::bind(comp, *syntax.predicate->conditions[0]->expr, context);
    const auto& ifTrue = bindStatement(*syntax.statement, context);
    const Statement* ifFalse = nullptr;
    if (syntax.elseClause)
        ifFalse = &bindStatement(syntax.elseClause->clause->as<StatementSyntax>(), context);

    return *comp.emplace<ConditionalStatement>(syntax, cond, ifTrue, ifFalse);
}

Statement& StatementBodiedScope::bindForLoopStatement(const ForLoopStatementSyntax& syntax, const BindContext& context) {
    // If the initializers here involve doing variable declarations, then the spec says we create
    // an implicit sequential block and do the declaration there. Otherwise we'll just
    // end up returning the for statement directly.
    StatementBodiedScope* forScope = this;
    SequentialBlockStatement* implicitBlockStmt = nullptr;
    SmallVectorSized<const Statement*, 4> initializers;
    std::optional<BindContext> nestedContext;
    const BindContext* forContext = &context;

    Compilation& comp = getCompilation();
    if (!syntax.initializers.empty() && syntax.initializers[0]->kind == SyntaxKind::ForVariableDeclaration) {
        auto implicitBlock = comp.emplace<SequentialBlockSymbol>(comp, syntax.forKeyword.location());
        implicitBlockStmt = comp.emplace<SequentialBlockStatement>(*implicitBlock);

        addMember(*implicitBlock);
        forScope = implicitBlock;
        nestedContext.emplace(*forScope, LookupLocation::max);
        forContext = &nestedContext.value();

        for (auto initializer : syntax.initializers) {
            // If one entry is a variable declaration, they should all be. Checked by the parser.
            ASSERT(initializer->kind == SyntaxKind::ForVariableDeclaration);

            auto& var = VariableSymbol::fromSyntax(comp, initializer->as<ForVariableDeclarationSyntax>());
            implicitBlock->addMember(var);
            initializers.append(comp.emplace<VariableDeclStatement>(var));
        }
    }
    else {
        for (auto initializer : syntax.initializers) {
            ASSERT(isStatement(initializer->kind));
            initializers.append(&bindStatement(initializer->as<StatementSyntax>(), *forContext));
        }
    }

    SmallVectorSized<const Expression*, 2> steps;
    const auto& stopExpr = Expression::bind(comp, *syntax.stopExpr, *forContext);
    for (auto step : syntax.steps)
        steps.append(&Expression::bind(comp, *step, *forContext));

    const auto& bodyStmt = forScope->bindStatement(*syntax.statement, *forContext);
    auto initList = comp.emplace<StatementList>(initializers.copy(comp));
    auto loop = comp.emplace<ForLoopStatement>(syntax, *initList, &stopExpr, steps.copy(comp), bodyStmt);

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
    const auto& expr = Expression::bind(comp, *syntax.expr, context);
    return *comp.emplace<ExpressionStatement>(syntax, expr);
}

Statement& StatementBodiedScope::bindBlockStatement(const BlockStatementSyntax& syntax, const BindContext&) {
    Compilation& comp = getCompilation();
    auto& symbol = SequentialBlockSymbol::fromSyntax(comp, syntax);
    addMember(symbol);
    return *comp.emplace<SequentialBlockStatement>(symbol);
}

Statement& StatementBodiedScope::badStmt(const Statement* stmt) {
    return *getCompilation().emplace<InvalidStatement>(stmt);
}

}