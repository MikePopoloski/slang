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
    Compilation& comp = getCompilation();

    for (auto item : items) {
        if (isStatement(item->kind))
            buffer.append(&bindStatement(item->as<StatementSyntax>()));
        else if (item->kind == SyntaxKind::DataDeclaration) {
            SmallVectorSized<const VariableSymbol*, 4> variables;
            VariableSymbol::fromSyntax(comp, item->as<DataDeclarationSyntax>(), variables);
            for (auto variable : variables) {
                addMember(*variable);
                buffer.append(comp.emplace<VariableDeclStatement>(*variable));
            }
        }
        else {
            THROW_UNREACHABLE;
        }
    }

    return *comp.emplace<StatementList>(buffer.copy(comp));
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

Statement& StatementBodiedScope::bindForLoopStatement(const ForLoopStatementSyntax&) {
    // TODO: initializers need better handling

    // If the initializers here involve doing variable declarations, then the spec says we create
    // an implicit sequential block and do the declaration there.
    /*BumpAllocator& alloc = root.allocator();
    SequentialBinder& implicitInitBlock = *alloc.emplace<SequentialBinder>(*this);
    const auto& forVariable = syntax.initializers[0]->as<ForVariableDeclarationSyntax>();

    const auto& loopVar = *alloc.emplace<VariableSymbol>(forVariable.declarator.name, forVariable.type,
    implicitInitBlock, VariableLifetime::Automatic, false,
    &forVariable.declarator.initializer->expr);

    implicitInitBlock.setMember(loopVar);
    builder.add(implicitInitBlock);

    Binder binder(implicitInitBlock);
    const auto& stopExpr = binder.bindSelfDeterminedExpression(syntax.stopExpr);

    SmallVectorSized<const BoundExpression*, 2> steps;
    for (auto step : syntax.steps)
    steps.append(&binder.bindSelfDeterminedExpression(*step));

    const auto& statement = implicitInitBlock.bindStatement(syntax.statement);
    const auto& loop = allocate<BoundForLoopStatement>(syntax, stopExpr, steps.copy(compilation), statement);

    SmallVectorSized<const Statement*, 2> blockList;
    blockList.append(&allocate<BoundVariableDecl>(loopVar));
    blockList.append(&loop);

    implicitInitBlock.setBody(allocate<StatementList>(blockList.copy(compilation)));
    return allocate<BoundSequentialBlock>(implicitInitBlock);*/

    return badStmt(nullptr);
}

Statement& StatementBodiedScope::bindExpressionStatement(const ExpressionStatementSyntax& syntax) {
    const auto& expr = Binder(*this).bindSelfDeterminedExpression(syntax.expr);
    return *getCompilation().emplace<ExpressionStatement>(syntax, expr);
}

Statement& StatementBodiedScope::badStmt(const Statement* stmt) {
    return *getCompilation().emplace<InvalidStatement>(stmt);
}

}