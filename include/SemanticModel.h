//------------------------------------------------------------------------------
// SemanticModel.h
// Symbol binding and semantic analysis.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include "AllSyntax.h"
#include "BoundNodes.h"
#include "Buffer.h"
#include "BufferPool.h"
#include "BumpAllocator.h"
#include "DeclarationTable.h"
#include "Diagnostics.h"

namespace slang {

class SyntaxTree;
class Symbol;

enum class SpecialType {
    ShortInt,
    Int,
    LongInt,
    Byte,
    Bit,
    Logic,
    Reg,
    Integer,
    Time,
    Real,
    ShortReal,
    RealTime,
    // note: Error must always be the last value
    Error
};

enum class ValueCategory {
    None,
    Constant
};

/// SemanticModel is responsible for binding symbols and performing
/// type checking based on input parse trees.
class SemanticModel {
public:
    SemanticModel();
    SemanticModel(DeclarationTable& declTable);

    void bindModuleImplicit(ModuleDeclarationSyntax* module);
    BoundParameterDeclaration* bindParameterDecl(const ParameterDeclarationSyntax* syntax);

	/// Expression binding methods.
    BoundExpression* bindExpression(const ExpressionSyntax* syntax);
    BoundExpression* bindSelfDeterminedExpression(const ExpressionSyntax* syntax);
    BoundExpression* bindLiteral(const LiteralExpressionSyntax* syntax);
    BoundExpression* bindLiteral(const IntegerVectorExpressionSyntax* syntax);
    BoundExpression* bindUnaryArithmeticOperator(const PrefixUnaryExpressionSyntax* syntax);
    BoundExpression* bindUnaryReductionOperator(const PrefixUnaryExpressionSyntax* syntax);
    BoundExpression* bindArithmeticOperator(const BinaryExpressionSyntax* syntax);
    BoundExpression* bindComparisonOperator(const BinaryExpressionSyntax* syntax);
    BoundExpression* bindRelationalOperator(const BinaryExpressionSyntax* syntax);
    BoundExpression* bindShiftOrPowerOperator(const BinaryExpressionSyntax* syntax);

	/// Utilities for getting various type symbols.
    const TypeSymbol* getErrorType() const { return getSpecialType(SpecialType::Error); }
    const TypeSymbol* getSpecialType(SpecialType type) const { return specialTypes[(int)type]; }
    const TypeSymbol* getIntegralType(int width, bool isSigned);

private:
	// propagates the type of the expression back down to its operands
	// and folds constants on the way back up
	void propagateAndFold(BoundExpression* expression, const TypeSymbol* type);
	void propagateAndFoldLiteral(BoundLiteralExpression* expression, const TypeSymbol* type);
	void propagateAndFoldUnaryArithmeticOperator(BoundUnaryExpression* expression, const TypeSymbol* type);
	void propagateAndFoldUnaryReductionOperator(BoundUnaryExpression* expression, const TypeSymbol* type);
	void propagateAndFoldArithmeticOperator(BoundBinaryExpression* expression, const TypeSymbol* type);
	void propagateAndFoldComparisonOperator(BoundBinaryExpression* expression, const TypeSymbol* type);
	void propagateAndFoldRelationalOperator(BoundBinaryExpression* expression, const TypeSymbol* type);
	void propagateAndFoldShiftOrPowerOperator(BoundBinaryExpression* expression, const TypeSymbol* type);

    Diagnostics diagnostics;
    BumpAllocator alloc;
    BufferPool<Symbol*> symbolPool;

    // preallocated type symbols for common types
    TypeSymbol* specialTypes[(int)SpecialType::Error+1];

	// cache of simple integral types; maps from width -> type, arrayed by 4-state/2-state and signed/unsigned
	std::unordered_map<int, const TypeSymbol*> integralTypeCache[2][2];
};

}