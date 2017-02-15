//------------------------------------------------------------------------------
// ExpressionBinder.h
// Centralized code for convert expressions into an AST.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include "AllSyntax.h"
#include "BoundNodes.h"
#include "Diagnostics.h"

namespace slang {

class SemanticModel;
class Scope;

class ExpressionBinder {
public:
    ExpressionBinder(SemanticModel& sem, const Scope* scope);
    ExpressionBinder(SemanticModel& sem, const SubroutineSymbol* subroutine);

    BoundExpression* bindConstantExpression(const ExpressionSyntax* syntax);
    BoundExpression* bindSelfDeterminedExpression(const ExpressionSyntax* syntax);
    BoundExpression* bindAssignmentLikeContext(const ExpressionSyntax* syntax, SourceLocation location, const TypeSymbol* assignmentType);

    BoundStatement* bindStatement(const StatementSyntax* syntax);
    BoundStatementList* bindStatementList(const SyntaxList<SyntaxNode>& items);

private:
    BoundExpression* bindAndPropagate(const ExpressionSyntax* syntax);
    BoundExpression* bindExpression(const ExpressionSyntax* syntax);
    BoundExpression* bindLiteral(const LiteralExpressionSyntax* syntax);
    BoundExpression* bindLiteral(const IntegerVectorExpressionSyntax* syntax);
    BoundExpression* bindName(const NameSyntax* syntax, const Scope* scope);
    BoundExpression* bindSimpleName(const IdentifierNameSyntax* syntax, const Scope* currScope);
    BoundExpression* bindSelectName(const IdentifierSelectNameSyntax* syntax, const Scope* currScope);
    BoundExpression* bindScopedName(const ScopedNameSyntax* syntax, const Scope* currScope);
    BoundExpression* bindUnaryArithmeticOperator(const PrefixUnaryExpressionSyntax* syntax);
    BoundExpression* bindUnaryReductionOperator(const PrefixUnaryExpressionSyntax* syntax);
    BoundExpression* bindArithmeticOperator(const BinaryExpressionSyntax* syntax);
    BoundExpression* bindComparisonOperator(const BinaryExpressionSyntax* syntax);
    BoundExpression* bindRelationalOperator(const BinaryExpressionSyntax* syntax);
    BoundExpression* bindShiftOrPowerOperator(const BinaryExpressionSyntax* syntax);
    BoundExpression* bindAssignmentOperator(const BinaryExpressionSyntax* syntax);
    BoundExpression* bindSubroutineCall(const InvocationExpressionSyntax* syntax);
    BoundExpression* bindConditionalExpression(const ConditionalExpressionSyntax* syntax);

    BoundStatement* bindReturnStatement(const ReturnStatementSyntax* syntax);
    BoundStatement* bindConditionalStatement(const ConditionalStatementSyntax *syntax);
    BoundStatement* bindForLoopStatement(const ForLoopStatementSyntax *syntax);
    BoundStatement* bindExpressionStatement(const ExpressionStatementSyntax *syntax);

    void bindVariableDecl(const DataDeclarationSyntax* syntax, SmallVector<const BoundStatement*>& results);

    // functions to check whether operators are applicable to the given operand types
    bool checkOperatorApplicability(SyntaxKind op, SourceLocation location, BoundExpression** operand);
    bool checkOperatorApplicability(SyntaxKind op, SourceLocation location, BoundExpression** lhs, BoundExpression** rhs);

    // Propagates the type of the expression back down to its operands.
    void propagate(BoundExpression* expression, const TypeSymbol* type);

    BadBoundExpression* badExpr(BoundExpression* expr);
    BadBoundStatement* badStmt(BoundStatement* stmt);

    // Apply propagation rules for an assignment; increasing the rhs type to the lhs type if necessary
    // apply to both sides if symmetric. Returns true if a type expansion was necessary
    bool propagateAssignmentLike(BoundExpression* rhs, const TypeSymbol* lhsType);

    const TypeSymbol* binaryOperatorResultType(const TypeSymbol* lhsType, const TypeSymbol* rhsType, bool forceFourState);

    SemanticModel& sem;
    BumpAllocator& alloc;
    const Scope* scope;
    const SubroutineSymbol* subroutine = nullptr;

    Diagnostic& addError(DiagCode code, SourceLocation location);
};

}
