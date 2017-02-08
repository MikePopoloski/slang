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

    BoundExpression* bindConstantExpression(const ExpressionSyntax* syntax);
    BoundExpression* bindSelfDeterminedExpression(const ExpressionSyntax* syntax);
    BoundExpression* bindAssignmentLikeContext(const ExpressionSyntax* syntax, SourceLocation location, const TypeSymbol* assignmentType);

    BoundExpression* bindExpression(const ExpressionSyntax* syntax);
    BoundExpression* bindLiteral(const LiteralExpressionSyntax* syntax);
    BoundExpression* bindLiteral(const IntegerVectorExpressionSyntax* syntax);
    BoundExpression* bindSimpleName(const IdentifierNameSyntax* syntax);
    BoundExpression* bindUnaryArithmeticOperator(const PrefixUnaryExpressionSyntax* syntax);
    BoundExpression* bindUnaryReductionOperator(const PrefixUnaryExpressionSyntax* syntax);
    BoundExpression* bindArithmeticOperator(const BinaryExpressionSyntax* syntax);
    BoundExpression* bindComparisonOperator(const BinaryExpressionSyntax* syntax);
    BoundExpression* bindRelationalOperator(const BinaryExpressionSyntax* syntax);
    BoundExpression* bindShiftOrPowerOperator(const BinaryExpressionSyntax* syntax);

private:
    // functions to check whether operators are applicable to the given operand types
    bool checkOperatorApplicability(SyntaxKind op, SourceLocation location, BoundExpression** operand);
    bool checkOperatorApplicability(SyntaxKind op, SourceLocation location, BoundExpression** lhs, BoundExpression** rhs);

    // Propagates the type of the expression back down to its operands.
    void propagate(BoundExpression* expression, const TypeSymbol* type);

    BadBoundExpression* makeBad(BoundExpression* expr);

    SemanticModel& sem;
    BumpAllocator& alloc;
    const Scope* scope;

    Diagnostic& addError(DiagCode code, SourceLocation location);
};

}
