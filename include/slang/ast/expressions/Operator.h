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

class OpInfo {
public:
    static bool isBitwise(BinaryOperator op);
    static bool isComparison(BinaryOperator op);
    static bool isShift(BinaryOperator op);
    static bool isArithmetic(BinaryOperator op);
    static bool isRelational(BinaryOperator op);
    static bool isLValue(UnaryOperator op);
    static bool isShortCircuit(BinaryOperator op);
    static std::string_view getText(BinaryOperator op);
    static int getPrecedence(BinaryOperator op);

    static UnaryOperator getUnary(syntax::SyntaxKind kind);
    static BinaryOperator getBinary(syntax::SyntaxKind kind);

    static const Type* binaryType(Compilation& compilation, const Type* lt, const Type* rt,
                                  bool forceFourState, bool signednessFromRt = false);

    static ConstantValue eval(BinaryOperator op, const ConstantValue& cvl,
                              const ConstantValue& cvr);

private:
    OpInfo() = delete;
};

} // namespace slang::ast
