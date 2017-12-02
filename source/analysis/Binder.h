//------------------------------------------------------------------------------
// Binder.h
// Centralized code for converting expressions into an AST.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "diagnostics/Diagnostics.h"
#include "parsing/AllSyntax.h"

#include "Expressions.h"
#include "Statements.h"

namespace slang {

/// A binder is responsible for binding symbols with expressions to form
/// bound expression trees. This involves doing full type checking and name
/// resolution of all identifiers.
///
/// This class is lightweight; feel free to construct it and throw it away on demand.
///
class Binder {
public:
    /// Constructs a new binder for the given scope.
    explicit Binder(const Scope& scope);

    /// Binds an expression in a context that requires a compile-time value.
    const Expression& bindConstantExpression(const ExpressionSyntax& syntax);

    /// Binds an expression in a self-determined context. This is a SystemVerilog concept that
    /// means that the final type of the expression is known without needing to know the broader
    /// context in which it is used.
    const Expression& bindSelfDeterminedExpression(const ExpressionSyntax& syntax);

    /// Binds an expression in the context of an assignment, using the type of the left hand side
    /// to perform any necessary implicit conversions and checking.
    const Expression& bindAssignmentLikeContext(const ExpressionSyntax& syntax, SourceLocation location, const TypeSymbol& assignmentType);

    const Statement& bindStatement(const StatementSyntax& syntax) const;
    const StatementList& bindStatementList(const SyntaxList<SyntaxNode>& items) const;

private:
    Expression& bindAndPropagate(const ExpressionSyntax& syntax);
    Expression& bindExpression(const ExpressionSyntax& syntax);
    Expression& bindLiteral(const LiteralExpressionSyntax& syntax);
    Expression& bindLiteral(const IntegerVectorExpressionSyntax& syntax);
    Expression& bindName(const NameSyntax& syntax);
    Expression& bindSimpleName(const IdentifierNameSyntax& syntax);
    Expression& bindSelectName(const IdentifierSelectNameSyntax& syntax);
    Expression& bindScopedName(const ScopedNameSyntax& syntax);
    Expression& bindUnaryArithmeticOperator(const PrefixUnaryExpressionSyntax& syntax);
    Expression& bindUnaryReductionOperator(const PrefixUnaryExpressionSyntax& syntax);
    Expression& bindArithmeticOperator(const BinaryExpressionSyntax& syntax);
    Expression& bindComparisonOperator(const BinaryExpressionSyntax& syntax);
    Expression& bindRelationalOperator(const BinaryExpressionSyntax& syntax);
    Expression& bindShiftOrPowerOperator(const BinaryExpressionSyntax& syntax);
    Expression& bindAssignmentOperator(const BinaryExpressionSyntax& syntax);
    Expression& bindSubroutineCall(const InvocationExpressionSyntax& syntax);
    Expression& bindConditionalExpression(const ConditionalExpressionSyntax& syntax);
    Expression& bindConcatenationExpression(const ConcatenationExpressionSyntax& syntax);
    Expression& bindMultipleConcatenationExpression(const MultipleConcatenationExpressionSyntax& syntax);
    Expression& bindSelectExpression(const ElementSelectExpressionSyntax& syntax);
    Expression& bindSelectExpression(const ExpressionSyntax& syntax, Expression& expr, const SelectorSyntax& selector);

    Statement& bindConditionalStatement(const ConditionalStatementSyntax& syntax) const;
    Statement& bindForLoopStatement(const ForLoopStatementSyntax& syntax) const;
    Statement& bindReturnStatement(const ReturnStatementSyntax& syntax) const;
    Statement& bindExpressionStatement(const ExpressionStatementSyntax& syntax) const;

    // functions to check whether operators are applicable to the given operand types
    bool checkOperatorApplicability(SyntaxKind op, SourceLocation location, Expression** operand);
    bool checkOperatorApplicability(SyntaxKind op, SourceLocation location, Expression** lhs, Expression** rhs);

    InvalidExpression& badExpr(const Expression* expr);
    InvalidStatement& badStmt(const Statement* stmt) const;

    // Apply propagation rules for an assignment; increasing the rhs type to the lhs type if necessary
    // apply to both sides if symmetric. Returns true if a type expansion was necessary
    bool propagateAssignmentLike(Expression& rhs, const TypeSymbol& lhsType);

    const TypeSymbol& binaryOperatorResultType(const TypeSymbol* lhsType, const TypeSymbol* rhsType, bool forceFourState);

    const Scope& scope;
    Compilation& compilation;
};

}
