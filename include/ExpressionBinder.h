//------------------------------------------------------------------------------
// ExpressionBinder.h
// Centralized code for convert expressions into AST trees
// (also includes constant folding).
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include "AllSyntax.h"
#include "BoundNodes.h"

namespace slang {

class SemanticModel;

class ExpressionBinder {
public:
	ExpressionBinder(SemanticModel& sem);

	BoundExpression* bindExpression(const ExpressionSyntax* syntax);
	BoundExpression* bindSelfDeterminedExpression(const ExpressionSyntax* syntax);
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
	// propagates the type of the expression back down to its operands
	// and folds constants on the way back up
	void propagateAndFold(BoundExpression* expression, const TypeSymbol* type);
	void propagateAndFoldLiteral(BoundLiteral* expression, const TypeSymbol* type);
	void propagateAndFoldParameter(BoundParameter* expression, const TypeSymbol* type);
	void propagateAndFoldUnaryArithmeticOperator(BoundUnaryExpression* expression, const TypeSymbol* type);
	void propagateAndFoldUnaryReductionOperator(BoundUnaryExpression* expression, const TypeSymbol* type);
	void propagateAndFoldArithmeticOperator(BoundBinaryExpression* expression, const TypeSymbol* type);
	void propagateAndFoldComparisonOperator(BoundBinaryExpression* expression, const TypeSymbol* type);
	void propagateAndFoldRelationalOperator(BoundBinaryExpression* expression, const TypeSymbol* type);
	void propagateAndFoldShiftOrPowerOperator(BoundBinaryExpression* expression, const TypeSymbol* type);

	SemanticModel& sem;
	BumpAllocator& alloc;
};

}