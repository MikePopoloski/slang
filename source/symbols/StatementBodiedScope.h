//------------------------------------------------------------------------------
// StatementBodiedScope.h
// Statement binding.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "binding/BindContext.h"
#include "parsing/AllSyntax.h"
#include "symbols/Scope.h"

namespace slang {

class Statement;
class StatementList;

/// Base class for scopes that have a statement body.
class StatementBodiedScope : public Scope {
public:
    const Statement* getBody() const {
        ensureElaborated();
        return body;
    }

    void setBody(const Statement* statement) { body = statement; }
    void setBody(const StatementSyntax& syntax);
    void setBody(const SyntaxList<SyntaxNode>& syntax);

protected:
    using Scope::Scope;

private:
    friend class Scope;

    void bindBody(const SyntaxNode& syntax);
    void bindVariableDecl(const DataDeclarationSyntax& syntax, SmallVector<const Statement*>& statements);

    Statement& bindStatementList(const SyntaxList<SyntaxNode>& items);
    Statement& bindStatement(const StatementSyntax& syntax, const BindContext& context);
    Statement& bindReturnStatement(const ReturnStatementSyntax& syntax, const BindContext& context);
    Statement& bindConditionalStatement(const ConditionalStatementSyntax& syntax, const BindContext& context);
    Statement& bindForLoopStatement(const ForLoopStatementSyntax& syntax, const BindContext& context);
    Statement& bindExpressionStatement(const ExpressionStatementSyntax& syntax, const BindContext& context);

    Statement& badStmt(const Statement* stmt);

    const Statement* body = nullptr;
};

}