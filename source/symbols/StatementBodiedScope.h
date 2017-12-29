//------------------------------------------------------------------------------
// StatementBodiedScope.h
// Statement binding.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "parsing/AllSyntax.h"
#include "symbols/Scope.h"

namespace slang {

class Statement;
class StatementList;

/// Base class for scopes that have a statement body.
class StatementBodiedScope : public Scope {
public:
    const Statement* getBody() const {
        ensureMembers();
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

    Statement& bindStatement(const StatementSyntax& syntax);
    Statement& bindStatementList(const SyntaxList<SyntaxNode>& items);
    Statement& bindReturnStatement(const ReturnStatementSyntax& syntax);
    Statement& bindConditionalStatement(const ConditionalStatementSyntax& syntax);
    Statement& bindForLoopStatement(const ForLoopStatementSyntax& syntax);
    Statement& bindExpressionStatement(const ExpressionStatementSyntax& syntax);

    Statement& badStmt(const Statement* stmt);

    const Statement* body = nullptr;
};

}