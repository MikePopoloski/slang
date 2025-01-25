//------------------------------------------------------------------------------
// Operator.cpp
// Definitions and helpers for dealing with operators
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/expressions/Operator.h"

#include <cmath>

#include "slang/ast/Compilation.h"
#include "slang/ast/types/AllTypes.h"

namespace {

using namespace slang;
using namespace slang::ast;

#define OP(k, v)            \
    case BinaryOperator::k: \
        return v

template<typename TL, typename TR>
ConstantValue evalLogicalOp(BinaryOperator op, const TL& l, const TR& r) {
    switch (op) {
        OP(LogicalAnd, SVInt(logic_t(l) && r));
        OP(LogicalOr, SVInt(logic_t(l) || r));
        OP(LogicalImplication, SVInt(SVInt::logicalImpl(l, r)));
        OP(LogicalEquivalence, SVInt(SVInt::logicalEquiv(l, r)));
        default:
            // This should only be reachable when speculatively
            // evaluating an expression that hasn't had its
            // type finalized via propagation, which can happen
            // during an analyzeOpTypes call.
            return nullptr;
    }
}

template<typename TRes, typename TFloat>
ConstantValue evalFloatOp(BinaryOperator op, TFloat l, TFloat r) {
    bool bl = (bool)l;
    bool br = (bool)r;

    switch (op) {
        OP(Add, TRes(l + r));
        OP(Subtract, TRes(l - r));
        OP(Multiply, TRes(l * r));
        OP(Divide, TRes(l / r));
        OP(Power, TRes(std::pow(l, r)));
        OP(GreaterThanEqual, SVInt(l >= r));
        OP(GreaterThan, SVInt(l > r));
        OP(LessThanEqual, SVInt(l <= r));
        OP(LessThan, SVInt(l < r));
        OP(Equality, SVInt(l == r));
        OP(Inequality, SVInt(l != r));
        OP(CaseEquality, SVInt(l == r));
        OP(CaseInequality, SVInt(l != r));
        OP(LogicalAnd, SVInt(bl && br));
        OP(LogicalOr, SVInt(bl || br));
        OP(LogicalImplication, SVInt(!bl || br));
        OP(LogicalEquivalence, SVInt((!bl || br) && (!br || bl)));
        default:
            SLANG_UNREACHABLE;
    }
}
#undef OP

} // namespace

namespace slang::ast {

using namespace syntax;

const Type* OpInfo::binaryType(Compilation& compilation, const Type* lt, const Type* rt,
                               bool forceFourState, bool signednessFromRt) {
    if (!lt->isNumeric() || !rt->isNumeric())
        return &compilation.getErrorType();

    // If both sides are the same type just use that type.
    // NOTE: This specifically ignores the forceFourState option for enums,
    // as that better matches expectations. This area of the LRM is underspecified.
    if (lt->isMatching(*rt)) {
        if (!forceFourState || lt->isFourState() || lt->isEnum())
            return lt;
    }

    // Figure out what the result type of an arithmetic binary operator should be. The rules are:
    // - If either operand is real, the result is real
    // - Otherwise, if either operand is shortreal, the result is shortreal
    // - Otherwise, result is integral with the following properties:
    //      - Bit width is max(lhs, rhs)
    //      - If either operand is four state (or if we force it), the result is four state
    //      - If either operand is unsigned, the result is unsigned
    const Type* result;
    if (lt->isFloating() || rt->isFloating()) {
        if ((lt->isFloating() && lt->getBitWidth() == 64) ||
            (rt->isFloating() && rt->getBitWidth() == 64)) {
            result = &compilation.getRealType();
        }
        else {
            result = &compilation.getShortRealType();
        }
    }
    else {
        bitwidth_t width = std::max(lt->getBitWidth(), rt->getBitWidth());

        bitmask<IntegralFlags> lf = lt->getIntegralFlags();
        bitmask<IntegralFlags> rf = rt->getIntegralFlags();

        bitmask<IntegralFlags> flags;
        if (rf & IntegralFlags::Signed) {
            if ((lf & IntegralFlags::Signed) || signednessFromRt)
                flags |= IntegralFlags::Signed;
        }

        if (forceFourState || (lf & IntegralFlags::FourState) || (rf & IntegralFlags::FourState))
            flags |= IntegralFlags::FourState;
        if ((lf & IntegralFlags::Reg) && (rf & IntegralFlags::Reg))
            flags |= IntegralFlags::Reg;

        // If the width is 1, try to preserve whether this was a packed array with a width of 1
        // or a plain scalar type with no dimensions specified.
        if (width == 1 && (lt->isScalar() || rt->isScalar()))
            result = &compilation.getScalarType(flags);
        else
            result = &compilation.getType(width, flags);
    }

    // Attempt to preserve any type aliases passed in when selecting the result.
    if (lt->isMatching(*result))
        return lt;
    if (rt->isMatching(*result))
        return rt;

    return result;
}

UnaryOperator OpInfo::getUnary(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::UnaryPlusExpression:
            return UnaryOperator::Plus;
        case SyntaxKind::UnaryMinusExpression:
            return UnaryOperator::Minus;
        case SyntaxKind::UnaryBitwiseNotExpression:
            return UnaryOperator::BitwiseNot;
        case SyntaxKind::UnaryBitwiseAndExpression:
            return UnaryOperator::BitwiseAnd;
        case SyntaxKind::UnaryBitwiseOrExpression:
            return UnaryOperator::BitwiseOr;
        case SyntaxKind::UnaryBitwiseXorExpression:
            return UnaryOperator::BitwiseXor;
        case SyntaxKind::UnaryBitwiseNandExpression:
            return UnaryOperator::BitwiseNand;
        case SyntaxKind::UnaryBitwiseNorExpression:
            return UnaryOperator::BitwiseNor;
        case SyntaxKind::UnaryBitwiseXnorExpression:
            return UnaryOperator::BitwiseXnor;
        case SyntaxKind::UnaryLogicalNotExpression:
            return UnaryOperator::LogicalNot;
        case SyntaxKind::UnaryPreincrementExpression:
            return UnaryOperator::Preincrement;
        case SyntaxKind::UnaryPredecrementExpression:
            return UnaryOperator::Predecrement;
        case SyntaxKind::PostincrementExpression:
            return UnaryOperator::Postincrement;
        case SyntaxKind::PostdecrementExpression:
            return UnaryOperator::Postdecrement;
        default:
            SLANG_UNREACHABLE;
    }
}

BinaryOperator OpInfo::getBinary(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::AddExpression:
            return BinaryOperator::Add;
        case SyntaxKind::SubtractExpression:
            return BinaryOperator::Subtract;
        case SyntaxKind::MultiplyExpression:
            return BinaryOperator::Multiply;
        case SyntaxKind::DivideExpression:
            return BinaryOperator::Divide;
        case SyntaxKind::ModExpression:
            return BinaryOperator::Mod;
        case SyntaxKind::BinaryAndExpression:
            return BinaryOperator::BinaryAnd;
        case SyntaxKind::BinaryOrExpression:
            return BinaryOperator::BinaryOr;
        case SyntaxKind::BinaryXorExpression:
            return BinaryOperator::BinaryXor;
        case SyntaxKind::BinaryXnorExpression:
            return BinaryOperator::BinaryXnor;
        case SyntaxKind::EqualityExpression:
            return BinaryOperator::Equality;
        case SyntaxKind::InequalityExpression:
            return BinaryOperator::Inequality;
        case SyntaxKind::CaseEqualityExpression:
            return BinaryOperator::CaseEquality;
        case SyntaxKind::CaseInequalityExpression:
            return BinaryOperator::CaseInequality;
        case SyntaxKind::GreaterThanEqualExpression:
            return BinaryOperator::GreaterThanEqual;
        case SyntaxKind::GreaterThanExpression:
            return BinaryOperator::GreaterThan;
        case SyntaxKind::LessThanEqualExpression:
            return BinaryOperator::LessThanEqual;
        case SyntaxKind::LessThanExpression:
            return BinaryOperator::LessThan;
        case SyntaxKind::WildcardEqualityExpression:
            return BinaryOperator::WildcardEquality;
        case SyntaxKind::WildcardInequalityExpression:
            return BinaryOperator::WildcardInequality;
        case SyntaxKind::LogicalAndExpression:
            return BinaryOperator::LogicalAnd;
        case SyntaxKind::LogicalOrExpression:
            return BinaryOperator::LogicalOr;
        case SyntaxKind::LogicalImplicationExpression:
            return BinaryOperator::LogicalImplication;
        case SyntaxKind::LogicalEquivalenceExpression:
            return BinaryOperator::LogicalEquivalence;
        case SyntaxKind::LogicalShiftLeftExpression:
            return BinaryOperator::LogicalShiftLeft;
        case SyntaxKind::LogicalShiftRightExpression:
            return BinaryOperator::LogicalShiftRight;
        case SyntaxKind::ArithmeticShiftLeftExpression:
            return BinaryOperator::ArithmeticShiftLeft;
        case SyntaxKind::ArithmeticShiftRightExpression:
            return BinaryOperator::ArithmeticShiftRight;
        case SyntaxKind::PowerExpression:
            return BinaryOperator::Power;
        case SyntaxKind::AddAssignmentExpression:
            return BinaryOperator::Add;
        case SyntaxKind::SubtractAssignmentExpression:
            return BinaryOperator::Subtract;
        case SyntaxKind::MultiplyAssignmentExpression:
            return BinaryOperator::Multiply;
        case SyntaxKind::DivideAssignmentExpression:
            return BinaryOperator::Divide;
        case SyntaxKind::ModAssignmentExpression:
            return BinaryOperator::Mod;
        case SyntaxKind::AndAssignmentExpression:
            return BinaryOperator::BinaryAnd;
        case SyntaxKind::OrAssignmentExpression:
            return BinaryOperator::BinaryOr;
        case SyntaxKind::XorAssignmentExpression:
            return BinaryOperator::BinaryXor;
        case SyntaxKind::LogicalLeftShiftAssignmentExpression:
            return BinaryOperator::LogicalShiftLeft;
        case SyntaxKind::LogicalRightShiftAssignmentExpression:
            return BinaryOperator::LogicalShiftRight;
        case SyntaxKind::ArithmeticLeftShiftAssignmentExpression:
            return BinaryOperator::ArithmeticShiftLeft;
        case SyntaxKind::ArithmeticRightShiftAssignmentExpression:
            return BinaryOperator::ArithmeticShiftRight;
        default:
            SLANG_UNREACHABLE;
    }
}

ConstantValue OpInfo::eval(BinaryOperator op, const ConstantValue& cvl, const ConstantValue& cvr) {
    if (!cvl || !cvr)
        return nullptr;

#define OP(k, v)            \
    case BinaryOperator::k: \
        return v

    if (cvl.isInteger()) {
        const SVInt& l = cvl.integer();

        if (cvr.isInteger()) {
            const SVInt& r = cvr.integer();
            switch (op) {
                OP(Add, l + r);
                OP(Subtract, l - r);
                OP(Multiply, l * r);
                OP(Divide, l / r);
                OP(Mod, l % r);
                OP(BinaryAnd, l & r);
                OP(BinaryOr, l | r);
                OP(BinaryXor, l ^ r);
                OP(LogicalShiftLeft, l.shl(r));
                OP(LogicalShiftRight, l.lshr(r));
                OP(ArithmeticShiftLeft, l.shl(r));
                OP(ArithmeticShiftRight, l.ashr(r));
                OP(BinaryXnor, l.xnor(r));
                OP(Equality, SVInt(l == r));
                OP(Inequality, SVInt(l != r));
                OP(CaseEquality, SVInt((logic_t)exactlyEqual(l, r)));
                OP(CaseInequality, SVInt((logic_t)!exactlyEqual(l, r)));
                OP(WildcardEquality, SVInt(condWildcardEqual(l, r)));
                OP(WildcardInequality, SVInt(!condWildcardEqual(l, r)));
                OP(GreaterThanEqual, SVInt(l >= r));
                OP(GreaterThan, SVInt(l > r));
                OP(LessThanEqual, SVInt(l <= r));
                OP(LessThan, SVInt(l < r));
                OP(LogicalAnd, SVInt(l && r));
                OP(LogicalOr, SVInt(l || r));
                OP(LogicalImplication, SVInt(SVInt::logicalImpl(l, r)));
                OP(LogicalEquivalence, SVInt(SVInt::logicalEquiv(l, r)));
                OP(Power, l.pow(r));
            }
        }
        else if (cvr.isReal()) {
            return evalLogicalOp(op, l, (bool)cvr.real());
        }
        else if (cvr.isShortReal()) {
            return evalLogicalOp(op, l, (bool)cvr.shortReal());
        }
    }
    else if (cvl.isReal()) {
        double l = cvl.real();

        if (cvr.isReal())
            return evalFloatOp<real_t>(op, l, (double)cvr.real());
        else if (cvr.isInteger())
            return evalLogicalOp(op, (bool)l, cvr.integer());
        else if (cvr.isShortReal())
            return evalLogicalOp(op, (bool)l, (bool)cvr.shortReal());
    }
    else if (cvl.isShortReal()) {
        float l = cvl.shortReal();

        if (cvr.isShortReal())
            return evalFloatOp<shortreal_t>(op, l, (float)cvr.shortReal());
        else if (cvr.isInteger())
            return evalLogicalOp(op, (bool)l, cvr.integer());
        else if (cvr.isReal())
            return evalLogicalOp(op, (bool)l, (bool)cvr.real());
    }
    else if (cvl.isContainer()) {
        if (cvl.size() != cvr.size())
            return SVInt(false);

        auto li = begin(cvl);
        auto ri = begin(cvr);
        for (; li != end(cvl); li++, ri++) {
            ConstantValue result = eval(op, *li, *ri);
            if (!result)
                return nullptr;

            logic_t l = (logic_t)result.integer();
            if (l.isUnknown() || !l)
                return SVInt(l);
        }

        return SVInt(true);
    }
    else if (cvl.isString()) {
        auto& l = cvl.str();
        auto& r = cvr.str();

        switch (op) {
            OP(GreaterThanEqual, SVInt(l >= r));
            OP(GreaterThan, SVInt(l > r));
            OP(LessThanEqual, SVInt(l <= r));
            OP(LessThan, SVInt(l < r));
            OP(Equality, SVInt(l == r));
            OP(Inequality, SVInt(l != r));
            OP(CaseEquality, SVInt(l == r));
            OP(CaseInequality, SVInt(l != r));
            default:
                SLANG_UNREACHABLE;
        }
    }
    else if (cvl.isNullHandle()) {
        // Null can only ever appear in contexts where it's being compared to
        // something else that is null.
        switch (op) {
            OP(Equality, SVInt(true));
            OP(Inequality, SVInt(false));
            OP(CaseEquality, SVInt(true));
            OP(CaseInequality, SVInt(false));
            default:
                SLANG_UNREACHABLE;
        }
    }
    else if (cvl.isUnion() && cvr.isUnion()) {
        switch (op) {
            OP(Equality, SVInt(cvl == cvr));
            OP(Inequality, SVInt(cvl != cvr));
            OP(CaseEquality, SVInt(cvl == cvr));
            OP(CaseInequality, SVInt(cvl != cvr));
            default:
                SLANG_UNREACHABLE;
        }
    }

#undef OP
    SLANG_UNREACHABLE;
}

bool OpInfo::isBitwise(BinaryOperator op) {
    switch (op) {
        case BinaryOperator::BinaryOr:
        case BinaryOperator::BinaryAnd:
        case BinaryOperator::BinaryXor:
        case BinaryOperator::BinaryXnor:
            return true;
        default:
            return false;
    }
}

bool OpInfo::isComparison(BinaryOperator op) {
    switch (op) {
        case BinaryOperator::Equality:
        case BinaryOperator::Inequality:
        case BinaryOperator::CaseEquality:
        case BinaryOperator::CaseInequality:
        case BinaryOperator::WildcardEquality:
        case BinaryOperator::WildcardInequality:
        case BinaryOperator::GreaterThanEqual:
        case BinaryOperator::GreaterThan:
        case BinaryOperator::LessThanEqual:
        case BinaryOperator::LessThan:
            return true;
        default:
            return false;
    }
}

bool OpInfo::isShift(BinaryOperator op) {
    switch (op) {
        case BinaryOperator::LogicalShiftLeft:
        case BinaryOperator::LogicalShiftRight:
        case BinaryOperator::ArithmeticShiftLeft:
        case BinaryOperator::ArithmeticShiftRight:
            return true;
        default:
            return false;
    }
}

bool OpInfo::isArithmetic(BinaryOperator op) {
    switch (op) {
        case BinaryOperator::Add:
        case BinaryOperator::Subtract:
        case BinaryOperator::Multiply:
        case BinaryOperator::Divide:
        case BinaryOperator::Mod:
        case BinaryOperator::Power:
            return true;
        default:
            return false;
    }
}

bool OpInfo::isRelational(BinaryOperator op) {
    switch (op) {
        case BinaryOperator::GreaterThanEqual:
        case BinaryOperator::GreaterThan:
        case BinaryOperator::LessThanEqual:
        case BinaryOperator::LessThan:
            return true;
        default:
            return false;
    }
}

bool OpInfo::isLValue(UnaryOperator op) {
    switch (op) {
        case UnaryOperator::Preincrement:
        case UnaryOperator::Predecrement:
        case UnaryOperator::Postincrement:
        case UnaryOperator::Postdecrement:
            return true;
        default:
            return false;
    }
}

bool OpInfo::isShortCircuit(BinaryOperator op) {
    switch (op) {
        case BinaryOperator::LogicalAnd:
        case BinaryOperator::LogicalOr:
        case BinaryOperator::LogicalImplication:
            return true;
        default:
            return false;
    }
}

// LCOV_EXCL_START
std::string_view OpInfo::getText(BinaryOperator op) {
    switch (op) {
        case BinaryOperator::Add:
            return "+";
        case BinaryOperator::Subtract:
            return "-";
        case BinaryOperator::Multiply:
            return "*";
        case BinaryOperator::Divide:
            return "/";
        case BinaryOperator::Mod:
            return "%";
        case BinaryOperator::BinaryAnd:
            return "&";
        case BinaryOperator::BinaryOr:
            return "|";
        case BinaryOperator::BinaryXor:
            return "^";
        case BinaryOperator::BinaryXnor:
            return "~^";
        case BinaryOperator::Equality:
            return "==";
        case BinaryOperator::Inequality:
            return "!=";
        case BinaryOperator::CaseEquality:
            return "===";
        case BinaryOperator::CaseInequality:
            return "!==";
        case BinaryOperator::GreaterThanEqual:
            return ">=";
        case BinaryOperator::GreaterThan:
            return ">";
        case BinaryOperator::LessThanEqual:
            return "<=";
        case BinaryOperator::LessThan:
            return "<";
        case BinaryOperator::WildcardEquality:
            return "==?";
        case BinaryOperator::WildcardInequality:
            return "!=?";
        case BinaryOperator::LogicalAnd:
            return "&&";
        case BinaryOperator::LogicalOr:
            return "||";
        case BinaryOperator::LogicalImplication:
            return "->";
        case BinaryOperator::LogicalEquivalence:
            return "<->";
        case BinaryOperator::LogicalShiftLeft:
            return "<<";
        case BinaryOperator::LogicalShiftRight:
            return ">>";
        case BinaryOperator::ArithmeticShiftLeft:
            return "<<<";
        case BinaryOperator::ArithmeticShiftRight:
            return ">>>";
        case BinaryOperator::Power:
            return "**";
    }
    SLANG_UNREACHABLE;
}

int OpInfo::getPrecedence(BinaryOperator op) {
    // Note: the precedence levels here match what is returned by
    // SyntaxFacts::getPrecedence.
    switch (op) {
        case BinaryOperator::LogicalImplication:
        case BinaryOperator::LogicalEquivalence:
            return 2;
        case BinaryOperator::LogicalOr:
            return 3;
        case BinaryOperator::LogicalAnd:
            return 4;
        case BinaryOperator::BinaryOr:
            return 5;
        case BinaryOperator::BinaryXor:
        case BinaryOperator::BinaryXnor:
            return 6;
        case BinaryOperator::BinaryAnd:
            return 7;
        case BinaryOperator::Equality:
        case BinaryOperator::Inequality:
        case BinaryOperator::CaseEquality:
        case BinaryOperator::CaseInequality:
        case BinaryOperator::WildcardEquality:
        case BinaryOperator::WildcardInequality:
            return 8;
        case BinaryOperator::GreaterThanEqual:
        case BinaryOperator::GreaterThan:
        case BinaryOperator::LessThanEqual:
        case BinaryOperator::LessThan:
            return 9;
        case BinaryOperator::LogicalShiftLeft:
        case BinaryOperator::LogicalShiftRight:
        case BinaryOperator::ArithmeticShiftLeft:
        case BinaryOperator::ArithmeticShiftRight:
            return 10;
        case BinaryOperator::Add:
        case BinaryOperator::Subtract:
            return 11;
        case BinaryOperator::Multiply:
        case BinaryOperator::Divide:
        case BinaryOperator::Mod:
            return 12;
        case BinaryOperator::Power:
            return 13;
    }
    SLANG_UNREACHABLE;
}
// LCOV_EXCL_STOP

} // namespace slang::ast
