//------------------------------------------------------------------------------
// Binder.h
// Centralized code for convert expressions and statements into an AST.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "diagnostics/Diagnostics.h"
#include "parsing/AllSyntax.h"

#include "BoundNodes.h"

namespace slang {

/// A binder is responsible for binding symbols with expressions to form
/// bound expression trees and with statements to form bound statement trees.
/// This involves doing full type checking and name resolution of all identifiers.
///
/// This class is lightweight; feel free to construct it and throw it away on demand.
///
class Binder {
public:
	explicit Binder(const ScopeSymbol& scope);

	/// Binds an expression in a context that requires a compile-time value.
    const BoundExpression& bindConstantExpression(const ExpressionSyntax& syntax);

	/// Binds an expression in a self-determined context. This is a SystemVerilog concept that
	/// means that the final type of the expression is known without needing to know the broader
	/// context in which it is used.
    const BoundExpression& bindSelfDeterminedExpression(const ExpressionSyntax& syntax);

	/// Binds an expression in the context of an assignment, using the type of the left hand side
	/// to perform any necessary implicit conversions and checking.
    const BoundExpression& bindAssignmentLikeContext(const ExpressionSyntax& syntax, SourceLocation location, const TypeSymbol& assignmentType);

	/// Binds a single statement.
    const BoundStatement& bindStatement(const StatementSyntax& syntax);

	/// Binds a list of statements, such as in a function body.
    const BoundStatementList& bindStatementList(const SyntaxList<SyntaxNode>& items);

private:
    BoundExpression& bindAndPropagate(const ExpressionSyntax& syntax);
    BoundExpression& bindExpression(const ExpressionSyntax& syntax);
    BoundExpression& bindLiteral(const LiteralExpressionSyntax& syntax);
    BoundExpression& bindLiteral(const IntegerVectorExpressionSyntax& syntax);
    BoundExpression& bindName(const NameSyntax& syntax);
    BoundExpression& bindSimpleName(const IdentifierNameSyntax& syntax);
    BoundExpression& bindSelectName(const IdentifierSelectNameSyntax& syntax);
    BoundExpression& bindUnaryArithmeticOperator(const PrefixUnaryExpressionSyntax& syntax);
    BoundExpression& bindUnaryReductionOperator(const PrefixUnaryExpressionSyntax& syntax);
    BoundExpression& bindArithmeticOperator(const BinaryExpressionSyntax& syntax);
    BoundExpression& bindComparisonOperator(const BinaryExpressionSyntax& syntax);
    BoundExpression& bindRelationalOperator(const BinaryExpressionSyntax& syntax);
    BoundExpression& bindShiftOrPowerOperator(const BinaryExpressionSyntax& syntax);
    BoundExpression& bindAssignmentOperator(const BinaryExpressionSyntax& syntax);
    BoundExpression& bindSubroutineCall(const InvocationExpressionSyntax& syntax);
    BoundExpression& bindConditionalExpression(const ConditionalExpressionSyntax& syntax);
    BoundExpression& bindConcatenationExpression(const ConcatenationExpressionSyntax& syntax);
    BoundExpression& bindMultipleConcatenationExpression(const MultipleConcatenationExpressionSyntax& syntax);
    BoundExpression& bindSelectExpression(const ElementSelectExpressionSyntax& syntax);
    BoundExpression& bindSelectExpression(const ExpressionSyntax& syntax, const BoundExpression& expr, const SelectorSyntax& selector);

    BoundStatement& bindReturnStatement(const ReturnStatementSyntax& syntax);
    BoundStatement& bindConditionalStatement(const ConditionalStatementSyntax& syntax);
    BoundStatement& bindForLoopStatement(const ForLoopStatementSyntax& syntax);
    BoundStatement& bindExpressionStatement(const ExpressionStatementSyntax& syntax);

    void bindVariableDecl(const DataDeclarationSyntax& syntax, SmallVector<const BoundStatement*>& results);

    // functions to check whether operators are applicable to the given operand types
    bool checkOperatorApplicability(SyntaxKind op, SourceLocation location, BoundExpression** operand);
    bool checkOperatorApplicability(SyntaxKind op, SourceLocation location, BoundExpression** lhs, BoundExpression** rhs);

    // Propagates the type of the expression back down to its operands.
    void propagate(BoundExpression& expression, const TypeSymbol& type);

    BadBoundExpression& badExpr(const BoundExpression* expr);
    BadBoundStatement& badStmt(const BoundStatement* stmt);

    // Apply propagation rules for an assignment; increasing the rhs type to the lhs type if necessary
    // apply to both sides if symmetric. Returns true if a type expansion was necessary
    bool propagateAssignmentLike(BoundExpression& rhs, const TypeSymbol& lhsType);

    const TypeSymbol& binaryOperatorResultType(const TypeSymbol* lhsType, const TypeSymbol* rhsType, bool forceFourState);

    const ScopeSymbol& scope;
	const DesignRootSymbol& root;
};

}
