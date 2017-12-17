//------------------------------------------------------------------------------
// StatementBodiedScope.cpp
// Statement binding.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Symbol.h"

#include "binding/Binder.h"
#include "binding/Statements.h"
#include "compilation/Compilation.h"

namespace slang {

void StatementBodiedScope::bindBody(const SyntaxNode& syntax) {
    if (syntax.kind == SyntaxKind::List)
        setBody(&bindStatementList((const SyntaxList<SyntaxNode>&)syntax));
    else
        setBody(&bindStatement((const StatementSyntax&)syntax));
}

Statement& StatementBodiedScope::bindStatement(const StatementSyntax& syntax) {
    switch (syntax.kind) {
        case SyntaxKind::ReturnStatement:
            return bindReturnStatement((const ReturnStatementSyntax&)syntax);
        case SyntaxKind::ConditionalStatement:
            return bindConditionalStatement((const ConditionalStatementSyntax&)syntax);
        case SyntaxKind::ForLoopStatement:
            return bindForLoopStatement((const ForLoopStatementSyntax&)syntax);
        case SyntaxKind::ExpressionStatement:
            return bindExpressionStatement((const ExpressionStatementSyntax&)syntax);
        default:
            THROW_UNREACHABLE;
    }
}

Statement& StatementBodiedScope::bindStatementList(const SyntaxList<SyntaxNode>& items) {
    SmallVectorSized<const Statement*, 8> buffer;
    for (auto item : items) {
        if (isStatement(item->kind))
            buffer.append(&bindStatement(item->as<StatementSyntax>()));
        else if (item->kind == SyntaxKind::DataDeclaration)
            bindVariableDecl(item->as<DataDeclarationSyntax>(), buffer);
        else
            THROW_UNREACHABLE;
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

Statement& StatementBodiedScope::bindReturnStatement(const ReturnStatementSyntax& syntax) {
    auto stmtLoc = syntax.returnKeyword.location();
    const Symbol* subroutine = asSymbol().findAncestor(SymbolKind::Subroutine);
    if (!subroutine) {
        getCompilation().addError(DiagCode::ReturnNotInSubroutine, stmtLoc);
        return badStmt(nullptr);
    }

    const auto& expr = Binder(*this).bindAssignmentLikeContext(*syntax.returnValue, stmtLoc,
                                                               *subroutine->as<SubroutineSymbol>().returnType);
    return *getCompilation().emplace<ReturnStatement>(syntax, &expr);
}

Statement& StatementBodiedScope::bindConditionalStatement(const ConditionalStatementSyntax& syntax) {
    ASSERT(syntax.predicate.conditions.count() == 1);
    ASSERT(!syntax.predicate.conditions[0]->matchesClause);

    const auto& cond = Binder(*this).bindSelfDeterminedExpression(syntax.predicate.conditions[0]->expr);
    const auto& ifTrue = bindStatement(syntax.statement);
    const Statement* ifFalse = nullptr;
    if (syntax.elseClause)
        ifFalse = &bindStatement(syntax.elseClause->clause.as<StatementSyntax>());

    return *getCompilation().emplace<ConditionalStatement>(syntax, cond, ifTrue, ifFalse);
}

Statement& StatementBodiedScope::bindForLoopStatement(const ForLoopStatementSyntax& syntax) {
    // If the initializers here involve doing variable declarations, then the spec says we create
    // an implicit sequential block and do the declaration there. Otherwise we'll just
    // end up returning the for statement directly.
    StatementBodiedScope* forScope = this;
    SequentialBlockStatement* implicitBlockStmt = nullptr;
    SmallVectorSized<const Statement*, 4> initializers;

    Compilation& comp = getCompilation();
    if (!syntax.initializers.empty() && syntax.initializers[0]->kind == SyntaxKind::ForVariableDeclaration) {
        auto implicitBlock = comp.emplace<SequentialBlockSymbol>(comp, syntax.forKeyword.location());
        implicitBlockStmt = comp.emplace<SequentialBlockStatement>(*implicitBlock);

        addMember(*implicitBlock);
        forScope = implicitBlock;

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
            initializers.append(&bindStatement(initializer->as<StatementSyntax>()));
        }
    }

    Binder binder(*forScope);
    const auto& stopExpr = binder.bindSelfDeterminedExpression(syntax.stopExpr);

    SmallVectorSized<const Expression*, 2> steps;
    for (auto step : syntax.steps)
        steps.append(&binder.bindSelfDeterminedExpression(*step));

    const auto& bodyStmt = forScope->bindStatement(syntax.statement);
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

Statement& StatementBodiedScope::bindExpressionStatement(const ExpressionStatementSyntax& syntax) {
    const auto& expr = Binder(*this).bindSelfDeterminedExpression(syntax.expr);
    return *getCompilation().emplace<ExpressionStatement>(syntax, expr);
}

Statement& StatementBodiedScope::badStmt(const Statement* stmt) {
    return *getCompilation().emplace<InvalidStatement>(stmt);
}

}