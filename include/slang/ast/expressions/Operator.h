//------------------------------------------------------------------------------
//! @file Operator.h
//! @brief Definitions and helpers for dealing with operators
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/numeric/ConstantValue.h"
#include "slang/syntax/SyntaxKind.h"
#include "slang/util/Enum.h"

namespace slang::ast {

class Compilation;
class Type;

// clang-format off
#define OP(x) \
    x(Plus) \
    x(Minus) \
    x(BitwiseNot) \
    x(BitwiseAnd) \
    x(BitwiseOr) \
    x(BitwiseXor) \
    x(BitwiseNand) \
    x(BitwiseNor) \
    x(BitwiseXnor) \
    x(LogicalNot) \
    x(Preincrement) \
    x(Predecrement) \
    x(Postincrement) \
    x(Postdecrement)
SLANG_ENUM(UnaryOperator, OP)
#undef OP

#define OP(x) \
    x(Add) \
    x(Subtract) \
    x(Multiply) \
    x(Divide) \
    x(Mod) \
    x(BinaryAnd) \
    x(BinaryOr) \
    x(BinaryXor) \
    x(BinaryXnor) \
    x(Equality) \
    x(Inequality) \
    x(CaseEquality) \
    x(CaseInequality) \
    x(GreaterThanEqual) \
    x(GreaterThan) \
    x(LessThanEqual) \
    x(LessThan) \
    x(WildcardEquality) \
    x(WildcardInequality) \
    x(LogicalAnd) \
    x(LogicalOr) \
    x(LogicalImplication) \
    x(LogicalEquivalence) \
    x(LogicalShiftLeft) \
    x(LogicalShiftRight) \
    x(ArithmeticShiftLeft) \
    x(ArithmeticShiftRight) \
    x(Power)
SLANG_ENUM(BinaryOperator, OP)
#undef OP
// clang-format on

/// Various utility methods for dealing with operators.
class SLANG_EXPORT OpInfo {
public:
    /// Determines if the given binary operator is a bitwise operator.
    static bool isBitwise(BinaryOperator op);

    /// Determines if the given binary operator is a comparison operator.
    static bool isComparison(BinaryOperator op);

    /// Determines if the given binary operator is a shift operator.
    static bool isShift(BinaryOperator op);

    /// Determines if the given binary operator is an arithmetic operator.
    static bool isArithmetic(BinaryOperator op);

    /// Determines if the given binary operator is a relational operator.
    static bool isRelational(BinaryOperator op);

    /// Determines if the given unary operator acts as an lvalue.
    static bool isLValue(UnaryOperator op);

    /// Determines if the given binary operator is a short-circuiting operator.
    static bool isShortCircuit(BinaryOperator op);

    /// Gets the string representation of the given binary operator.
    /// For example, BinaryOperator::Add returns "+".
    static std::string_view getText(BinaryOperator op);

    /// Gets the precedence of the given binary operator.
    static int getPrecedence(BinaryOperator op);

    /// Gets the UnaryOperator represented by the given syntax kind.
    static UnaryOperator getUnary(syntax::SyntaxKind kind);

    /// Gets the BinaryOperator represented by the given syntax kind.
    static BinaryOperator getBinary(syntax::SyntaxKind kind);

    /// Determines the resulting type of a binary operation between two types.
    static const Type* binaryType(Compilation& compilation, const Type* lt, const Type* rt,
                                  bool forceFourState, bool signednessFromRt = false);

    /// Evaluates the given binary operator on the two constant values.
    static ConstantValue eval(BinaryOperator op, const ConstantValue& cvl,
                              const ConstantValue& cvr);

private:
    OpInfo() = delete;
};

} // namespace slang::ast
