//------------------------------------------------------------------------------
// OperatorExpressions.cpp
// Definitions for operator expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/expressions/OperatorExpressions.h"

#include <cmath>

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Bitstream.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/Patterns.h"
#include "slang/ast/Statements.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/syntax/AllSyntax.h"

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
            SLANG_UNREACHABLE;
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

bool isLValueOp(UnaryOperator op) {
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

bool isShortCircuitOp(BinaryOperator op) {
    switch (op) {
        case BinaryOperator::LogicalAnd:
        case BinaryOperator::LogicalOr:
        case BinaryOperator::LogicalImplication:
            return true;
        default:
            return false;
    }
}

} // namespace

namespace slang::ast {

using namespace parsing;
using namespace syntax;

const Type* Expression::binaryOperatorType(Compilation& compilation, const Type* lt, const Type* rt,
                                           bool forceFourState, bool signednessFromRt) {
    if (!lt->isNumeric() || !rt->isNumeric())
        return &compilation.getErrorType();

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
    else if (lt->isEnum() && rt->isEnum() && lt->isMatching(*rt)) {
        // If both sides are the same enum type, preserve that in the output type.
        // NOTE: This specifically ignores the forceFourState option.
        return lt;
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

bool Expression::bindMembershipExpressions(const ASTContext& context, TokenKind keyword,
                                           bool requireIntegral, bool unwrapUnpacked,
                                           bool allowTypeReferences, bool allowOpenRange,
                                           const ExpressionSyntax& valueExpr,
                                           std::span<const ExpressionSyntax* const> expressions,
                                           SmallVectorBase<const Expression*>& results) {
    auto extraFlags = allowTypeReferences ? ASTFlags::AllowTypeReferences : ASTFlags::None;
    Compilation& comp = context.getCompilation();
    Expression& valueRes = create(comp, valueExpr, context, extraFlags);
    results.push_back(&valueRes);

    const Type* type = valueRes.type;
    bool bad = valueRes.bad();
    bool canBeStrings = valueRes.isImplicitString();

    if ((!requireIntegral && type->isAggregate()) || (requireIntegral && !type->isIntegral())) {
        if (!bad) {
            context.addDiag(diag::BadSetMembershipType, valueRes.sourceRange)
                << *type << LexerFacts::getTokenKindText(keyword);
            bad = true;
        }
    }

    auto checkType = [&](const Expression& expr, const Type& bt) {
        if (bt.isNumeric() && type->isNumeric()) {
            type = binaryOperatorType(comp, type, &bt, false);
        }
        else if ((bt.isClass() && bt.isAssignmentCompatible(*type)) ||
                 (type->isClass() && type->isAssignmentCompatible(bt))) {
            // ok
        }
        else if ((bt.isCHandle() || bt.isNull()) && (type->isCHandle() || type->isNull())) {
            // ok
        }
        else if ((bt.isEvent() || bt.isNull()) && (type->isEvent() || type->isNull())) {
            // ok
        }
        else if ((bt.isCovergroup() || bt.isNull()) && (type->isCovergroup() || type->isNull())) {
            // ok
        }
        else if (bt.isTypeRefType() && type->isTypeRefType()) {
            // ok
        }
        else if (canBeStrings) {
            // If canBeStrings is still true, it means either this specific type or
            // the common type (or both) are of type string. This is ok, but force
            // all further expressions to also be strings (or implicitly
            // convertible to them).
            type = &comp.getStringType();
        }
        else if (bt.isAggregate()) {
            // Aggregates are just never allowed in membership expressions.
            context.addDiag(diag::BadSetMembershipType, expr.sourceRange)
                << bt << LexerFacts::getTokenKindText(keyword);
            bad = true;
        }
        else {
            // Couldn't find a common type.
            context.addDiag(diag::NoCommonComparisonType, expr.sourceRange)
                << LexerFacts::getTokenKindText(keyword) << bt << *type;
            bad = true;
        }
    };

    // We need to find a common type across all expressions. If this is for a wildcard
    // case statement, the types can only be integral. Otherwise all singular types are allowed.
    for (auto expr : expressions) {
        Expression* bound = &create(comp, *expr, context, extraFlags);
        results.push_back(bound);
        bad |= bound->bad();
        if (bad)
            continue;

        // Special handling for open range expressions -- they don't have
        // a real type on their own, we need to check their bounds.
        if (allowOpenRange && bound->kind == ExpressionKind::OpenRange) {
            if (canBeStrings && !bound->isImplicitString())
                canBeStrings = false;

            auto& range = bound->as<OpenRangeExpression>();
            checkType(range.left(), *range.left().type);
            checkType(range.right(), *range.right().type);
            continue;
        }

        const Type* bt = bound->type;
        if (requireIntegral) {
            if (!bt->isIntegral()) {
                context.addDiag(diag::BadSetMembershipType, bound->sourceRange)
                    << *bt << LexerFacts::getTokenKindText(keyword);
                bad = true;
            }
            else {
                type = binaryOperatorType(comp, type, bt, false);
            }
            continue;
        }

        // If this is an "inside" operation, then unpacked arrays are unwrapped
        // into their element types before checking further.
        if (unwrapUnpacked) {
            while (bt->isUnpackedArray())
                bt = bt->getArrayElementType();
        }

        if (canBeStrings && !bound->isImplicitString() && !bt->isString())
            canBeStrings = false;

        checkType(*bound, *bt);
    }

    if (bad)
        return false;

    size_t index = 0;
    for (auto result : results) {
        // const_casts here are because we want the result array to be constant and
        // don't want to waste time / space allocating another array here locally just
        // to immediately copy it to the output.
        Expression* expr = const_cast<Expression*>(result);

        if ((type->isNumeric() || type->isString()) && !expr->type->isUnpackedArray())
            contextDetermined(context, expr, *type);
        else
            selfDetermined(context, expr);

        if (expr->bad())
            return false;

        results[index++] = expr;
    }

    return true;
}

Expression& UnaryExpression::fromSyntax(Compilation& compilation,
                                        const PrefixUnaryExpressionSyntax& syntax,
                                        const ASTContext& context) {
    auto op = getUnaryOperator(syntax.kind);
    bitmask<ASTFlags> extraFlags;
    if (isLValueOp(op))
        extraFlags = ASTFlags::LValue | ASTFlags::LAndRValue;

    Expression& operand = create(compilation, *syntax.operand, context, extraFlags);
    const Type* type = operand.type;

    auto result = compilation.emplace<UnaryExpression>(op, *type, operand, syntax.sourceRange());
    if (operand.bad())
        return badExpr(compilation, result);

    context.setAttributes(*result, syntax.attributes);

    bool good;
    switch (syntax.kind) {
        case SyntaxKind::UnaryPlusExpression:
        case SyntaxKind::UnaryMinusExpression:
            // Supported for both integral and real types. Result is same as input type.
            good = type->isNumeric();
            result->type = type;
            break;
        case SyntaxKind::UnaryLogicalNotExpression:
            // Supported for both integral and real types. Result is a single bit.
            good = type->isNumeric();
            result->type = type->isFourState() ? &compilation.getLogicType()
                                               : &compilation.getBitType();
            selfDetermined(context, result->operand_);
            break;
        case SyntaxKind::UnaryBitwiseNotExpression:
            // Supported for integral only. Result is same as input type.
            good = type->isIntegral();
            result->type = type;
            break;
        case SyntaxKind::UnaryBitwiseAndExpression:
        case SyntaxKind::UnaryBitwiseOrExpression:
        case SyntaxKind::UnaryBitwiseXorExpression:
        case SyntaxKind::UnaryBitwiseNandExpression:
        case SyntaxKind::UnaryBitwiseNorExpression:
        case SyntaxKind::UnaryBitwiseXnorExpression:
            // Supported for integral only. Result type is always a single bit.
            good = type->isIntegral();
            result->type = type->isFourState() ? &compilation.getLogicType()
                                               : &compilation.getBitType();
            selfDetermined(context, result->operand_);
            break;
        case SyntaxKind::UnaryPreincrementExpression:
        case SyntaxKind::UnaryPredecrementExpression:
            if ((context.flags.has(ASTFlags::NonProcedural) &&
                 !context.flags.has(ASTFlags::AssignmentAllowed)) ||
                context.flags.has(ASTFlags::AssignmentDisallowed)) {
                context.addDiag(diag::IncDecNotAllowed, syntax.sourceRange());
                return badExpr(compilation, result);
            }

            // Supported for both integral and real types. Result is same as input type.
            // The operand must also be an assignable lvalue.
            // TODO: detect and warn for multiple reads and writes of a single variable in an
            // expression
            good = type->isNumeric();
            result->type = type;
            if (!operand.requireLValue(context, syntax.operatorToken.location())) {
                return badExpr(compilation, result);
            }

            break;
        default:
            SLANG_UNREACHABLE;
    }

    if (!good) {
        auto& diag = context.addDiag(diag::BadUnaryExpression, syntax.operatorToken.location());
        diag << *type;
        diag << operand.sourceRange;
        return badExpr(compilation, result);
    }

    return *result;
}

Expression& UnaryExpression::fromSyntax(Compilation& compilation,
                                        const PostfixUnaryExpressionSyntax& syntax,
                                        const ASTContext& context) {
    // This method is only ever called for postincrement and postdecrement operators, so
    // the operand must be an lvalue.
    Expression& operand = create(compilation, *syntax.operand, context,
                                 ASTFlags::LValue | ASTFlags::LAndRValue);
    const Type* type = operand.type;

    Expression* result = compilation.emplace<UnaryExpression>(getUnaryOperator(syntax.kind), *type,
                                                              operand, syntax.sourceRange());
    if (operand.bad() || !operand.requireLValue(context, syntax.operatorToken.location()))
        return badExpr(compilation, result);

    if ((context.flags.has(ASTFlags::NonProcedural) &&
         !context.flags.has(ASTFlags::AssignmentAllowed)) ||
        context.flags.has(ASTFlags::AssignmentDisallowed)) {
        context.addDiag(diag::IncDecNotAllowed, syntax.sourceRange());
        return badExpr(compilation, result);
    }

    if (!type->isNumeric()) {
        auto& diag = context.addDiag(diag::BadUnaryExpression, syntax.operatorToken.location());
        diag << *type;
        diag << operand.sourceRange;
        return badExpr(compilation, result);
    }

    context.setAttributes(*result, syntax.attributes);
    return *result;
}

bool UnaryExpression::propagateType(const ASTContext& context, const Type& newType) {
    switch (op) {
        case UnaryOperator::Plus:
        case UnaryOperator::Minus:
        case UnaryOperator::BitwiseNot:
            type = &newType;
            contextDetermined(context, operand_, newType);
            return true;
        case UnaryOperator::BitwiseAnd:
        case UnaryOperator::BitwiseOr:
        case UnaryOperator::BitwiseXor:
        case UnaryOperator::BitwiseNand:
        case UnaryOperator::BitwiseNor:
        case UnaryOperator::BitwiseXnor:
        case UnaryOperator::LogicalNot:
        case UnaryOperator::Preincrement:
        case UnaryOperator::Predecrement:
        case UnaryOperator::Postincrement:
        case UnaryOperator::Postdecrement:
            // Operand is self determined and already folded.
            return false;
    }
    SLANG_UNREACHABLE;
}

std::optional<bitwidth_t> UnaryExpression::getEffectiveWidthImpl() const {
    switch (op) {
        case UnaryOperator::Plus:
        case UnaryOperator::Minus:
        case UnaryOperator::BitwiseNot:
            return operand().getEffectiveWidth();
        default:
            return type->getBitWidth();
    }
}

ConstantValue UnaryExpression::evalImpl(EvalContext& context) const {
    // Handle operations that require an lvalue up front.
    if (isLValueOp(op)) {
        LValue lvalue = operand().evalLValue(context);
        if (!lvalue)
            return nullptr;

        ConstantValue cv = lvalue.load();
        if (!cv)
            return nullptr;

        if (cv.isInteger()) {
#define OP(k, val)         \
    case UnaryOperator::k: \
        lvalue.store(val); \
        return v

            SVInt v = std::move(cv).integer();
            switch (op) {
                OP(Preincrement, ++v);
                OP(Predecrement, --v);
                OP(Postincrement, v + 1);
                OP(Postdecrement, v - 1);
                default:
                    break;
            }
#undef OP
        }
        else if (cv.isReal()) {
#define OP(k, val)                 \
    case UnaryOperator::k:         \
        lvalue.store(real_t(val)); \
        return real_t(v)

            double v = cv.real();
            switch (op) {
                OP(Preincrement, ++v);
                OP(Predecrement, --v);
                OP(Postincrement, v + 1);
                OP(Postdecrement, v - 1);
                default:
                    break;
            }
#undef OP
        }
        else if (cv.isShortReal()) {
#define OP(k, val)                      \
    case UnaryOperator::k:              \
        lvalue.store(shortreal_t(val)); \
        return shortreal_t(v)

            float v = cv.shortReal();
            switch (op) {
                OP(Preincrement, ++v);
                OP(Predecrement, --v);
                OP(Postincrement, v + 1);
                OP(Postdecrement, v - 1);
                default:
                    break;
            }
#undef OP
        }

        SLANG_UNREACHABLE;
    }

    ConstantValue cv = operand().eval(context);
    if (!cv)
        return nullptr;

#define OP(k, v)           \
    case UnaryOperator::k: \
        return v;

    if (cv.isInteger()) {
        SVInt v = std::move(cv).integer();
        switch (op) {
            OP(Plus, v);
            OP(Minus, -v);
            OP(BitwiseNot, ~v);
            OP(BitwiseAnd, SVInt(v.reductionAnd()));
            OP(BitwiseOr, SVInt(v.reductionOr()));
            OP(BitwiseXor, SVInt(v.reductionXor()));
            OP(BitwiseNand, SVInt(!v.reductionAnd()));
            OP(BitwiseNor, SVInt(!v.reductionOr()));
            OP(BitwiseXnor, SVInt(!v.reductionXor()));
            OP(LogicalNot, SVInt(!v));
            default:
                break;
        }
    }
    else if (cv.isReal()) {
        double v = cv.real();
        switch (op) {
            OP(Plus, real_t(v));
            OP(Minus, real_t(-v));
            OP(LogicalNot, SVInt(!(bool)v));
            default:
                break;
        }
    }
    else if (cv.isShortReal()) {
        float v = cv.shortReal();
        switch (op) {
            OP(Plus, shortreal_t(v));
            OP(Minus, shortreal_t(-v));
            OP(LogicalNot, SVInt(!(bool)v));
            default:
                break;
        }
    }

#undef OP
    SLANG_UNREACHABLE;
}

void UnaryExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("op", toString(op));
    serializer.write("operand", operand());
}

Expression& BinaryExpression::fromSyntax(Compilation& compilation,
                                         const BinaryExpressionSyntax& syntax,
                                         const ASTContext& context) {
    // If we are allowed unbounded literals here, pass that along to subexpressions.
    bitmask<ASTFlags> flags = ASTFlags::None;
    if (context.flags.has(ASTFlags::AllowUnboundedLiteral) &&
        context.flags.has(ASTFlags::AllowUnboundedLiteralArithmetic)) {
        flags = ASTFlags::AllowUnboundedLiteral;
    }

    auto op = getBinaryOperator(syntax.kind);
    if (op == BinaryOperator::Equality || op == BinaryOperator::Inequality ||
        op == BinaryOperator::CaseEquality || op == BinaryOperator::CaseInequality) {
        flags |= ASTFlags::AllowTypeReferences;
    }

    Expression& lhs = create(compilation, *syntax.left, context, flags);
    Expression& rhs = create(compilation, *syntax.right, context, flags);

    auto& result = fromComponents(lhs, rhs, op, syntax.operatorToken.location(),
                                  syntax.sourceRange(), context);
    context.setAttributes(result, syntax.attributes);

    return result;
}

Expression& BinaryExpression::fromComponents(Expression& lhs, Expression& rhs, BinaryOperator op,
                                             SourceLocation opLoc, SourceRange sourceRange,
                                             const ASTContext& context) {
    auto& compilation = context.getCompilation();
    const Type* lt = lhs.type;
    const Type* rt = rhs.type;

    auto result = compilation.emplace<BinaryExpression>(op, *lt, lhs, rhs, sourceRange);
    if (lhs.bad() || rhs.bad())
        return badExpr(compilation, result);

    if (lt->isUnbounded())
        lt = &compilation.getIntType();
    if (rt->isUnbounded())
        rt = &compilation.getIntType();

    bool bothIntegral = lt->isIntegral() && rt->isIntegral();
    bool bothNumeric = lt->isNumeric() && rt->isNumeric();
    bool bothStrings = lhs.isImplicitString() && rhs.isImplicitString();

    auto forceFourState = [](Compilation& compilation, const Type* forceType) {
        if (forceType->isFloating() || forceType->isFourState())
            return forceType;

        // Use the logic in binaryOperatorType to create a type with the correct size and sign.
        return binaryOperatorType(compilation, forceType, forceType, true);
    };

    auto singleBitType = [](Compilation& compilation, const Type* lt, const Type* rt) {
        if (lt->isFourState() || rt->isFourState())
            return &compilation.getLogicType();
        return &compilation.getBitType();
    };

    bool good;
    switch (op) {
        case BinaryOperator::Add:
        case BinaryOperator::Subtract:
        case BinaryOperator::Multiply:
            good = bothNumeric;
            result->type = binaryOperatorType(compilation, lt, rt, false);
            break;
        case BinaryOperator::Divide:
            // Result is forced to 4-state because result can be X.
            good = bothNumeric;
            result->type = binaryOperatorType(compilation, lt, rt, true);
            break;
        case BinaryOperator::Mod:
            // Result is forced to 4-state because result can be X.
            // Different from divide because only integers are allowed.
            good = bothIntegral;
            result->type = binaryOperatorType(compilation, lt, rt, true);
            break;
        case BinaryOperator::BinaryAnd:
        case BinaryOperator::BinaryOr:
        case BinaryOperator::BinaryXor:
        case BinaryOperator::BinaryXnor:
            good = bothIntegral;
            result->type = binaryOperatorType(compilation, lt, rt, false);
            break;
        case BinaryOperator::LogicalShiftLeft:
        case BinaryOperator::LogicalShiftRight:
        case BinaryOperator::ArithmeticShiftLeft:
        case BinaryOperator::ArithmeticShiftRight:
            // The result is always the same type as the lhs, except that if the rhs is
            // four state then the lhs also becomes four state.
            good = bothIntegral;
            if (rt->isFourState())
                result->type = forceFourState(compilation, lt);
            else
                result->type = lt;
            selfDetermined(context, result->right_);
            break;
        case BinaryOperator::Power:
            good = bothNumeric;
            if (lt->isFloating() || rt->isFloating()) {
                result->type = binaryOperatorType(compilation, lt, rt, false);
                contextDetermined(context, result->right_, *result->type);
            }
            else {
                // Result is forced to 4-state because result can be X.
                result->type = forceFourState(compilation, lt);
                selfDetermined(context, result->right_);
            }
            break;
        case BinaryOperator::GreaterThanEqual:
        case BinaryOperator::GreaterThan:
        case BinaryOperator::LessThanEqual:
        case BinaryOperator::LessThan: {
            // Result is always a single bit.
            good = bothNumeric || bothStrings;
            result->type = singleBitType(compilation, lt, rt);

            // Result type is fixed but the two operands affect each other as they would in
            // other context-determined operators.
            auto nt = (good && !bothNumeric) ? &compilation.getStringType()
                                             : binaryOperatorType(compilation, lt, rt, false);
            contextDetermined(context, result->left_, *nt);
            contextDetermined(context, result->right_, *nt);
            break;
        }
        case BinaryOperator::LogicalAnd:
        case BinaryOperator::LogicalOr:
        case BinaryOperator::LogicalImplication:
        case BinaryOperator::LogicalEquivalence:
            // Result is always a single bit.
            good = bothNumeric;
            result->type = singleBitType(compilation, lt, rt);
            selfDetermined(context, result->left_);
            selfDetermined(context, result->right_);
            break;
        case BinaryOperator::Equality:
        case BinaryOperator::Inequality:
        case BinaryOperator::WildcardEquality:
        case BinaryOperator::WildcardInequality:
        case BinaryOperator::CaseEquality:
        case BinaryOperator::CaseInequality:
            // Two types are comparable if:
            // - they are both integral or floating
            // - both classes or null, and assignment compatible
            // - both chandles or null
            // - both aggregates and equivalent
            if (bothNumeric) {
                // For equality and inequality, result is four state if either operand is
                // four state. For case equality and case inequality, result is never four
                // state. For wildcard equality / inequality, result is four state only if
                // lhs is four state.
                if (op == BinaryOperator::Equality || op == BinaryOperator::Inequality) {
                    good = true;
                    result->type = singleBitType(compilation, lt, rt);
                }
                else if (op == BinaryOperator::CaseEquality ||
                         op == BinaryOperator::CaseInequality) {
                    good = true;
                    result->type = &compilation.getBitType();
                }
                else {
                    good = bothIntegral;
                    result->type = lt->isFourState() ? &compilation.getLogicType()
                                                     : &compilation.getBitType();
                }

                // Result type is fixed but the two operands affect each other as they would
                // in other context-determined operators.
                auto nt = binaryOperatorType(compilation, lt, rt, false);
                contextDetermined(context, result->left_, *nt);
                contextDetermined(context, result->right_, *nt);
            }
            else {
                bool isContext = false;
                bool isWildcard = op == BinaryOperator::WildcardEquality ||
                                  op == BinaryOperator::WildcardInequality;

                if (bothStrings) {
                    good = !isWildcard;
                    result->type = &compilation.getBitType();

                    // If there is a literal involved, make sure it's converted to string.
                    isContext = true;
                    contextDetermined(context, result->left_, compilation.getStringType());
                    contextDetermined(context, result->right_, compilation.getStringType());
                }
                else if (lt->isAggregate() && lt->isEquivalent(*rt) && !lt->isUnpackedUnion()) {
                    good = !isWildcard;
                    result->type = singleBitType(compilation, lt, rt);
                }
                else if ((lt->isClass() && lt->isAssignmentCompatible(*rt)) ||
                         (rt->isClass() && rt->isAssignmentCompatible(*lt))) {
                    good = true;
                    result->type = &compilation.getBitType();
                }
                else if ((lt->isCHandle() || lt->isNull()) && (rt->isCHandle() || rt->isNull())) {
                    good = true;
                    result->type = &compilation.getBitType();
                }
                else if ((lt->isEvent() || lt->isNull()) && (rt->isEvent() || rt->isNull())) {
                    good = true;
                    result->type = &compilation.getBitType();
                }
                else if ((lt->isCovergroup() || lt->isNull()) &&
                         (rt->isCovergroup() || rt->isNull())) {
                    good = true;
                    result->type = &compilation.getBitType();
                }
                else if ((lt->isVirtualInterface() && lt->isAssignmentCompatible(*rt)) ||
                         (rt->isVirtualInterface() && rt->isAssignmentCompatible(*lt))) {
                    good = true;
                    result->type = &compilation.getBitType();
                }
                else if (lt->isTypeRefType() && rt->isTypeRefType()) {
                    good = !isWildcard;
                    result->type = &compilation.getBitType();
                }
                else {
                    good = false;
                }

                if (!isContext) {
                    selfDetermined(context, result->left_);
                    selfDetermined(context, result->right_);
                }
            }
            break;
        default:
            SLANG_UNREACHABLE;
    }

    if (!good) {
        auto& diag = context.addDiag(diag::BadBinaryExpression, opLoc);
        diag << *lt << *rt;
        diag << lhs.sourceRange;
        diag << rhs.sourceRange;
        return badExpr(compilation, result);
    }

    return *result;
}

bool BinaryExpression::propagateType(const ASTContext& context, const Type& newType) {
    switch (op) {
        case BinaryOperator::Add:
        case BinaryOperator::Subtract:
        case BinaryOperator::Multiply:
        case BinaryOperator::Divide:
        case BinaryOperator::Mod:
        case BinaryOperator::BinaryAnd:
        case BinaryOperator::BinaryOr:
        case BinaryOperator::BinaryXor:
        case BinaryOperator::BinaryXnor:
            type = &newType;
            contextDetermined(context, left_, newType);
            contextDetermined(context, right_, newType);
            return true;
        case BinaryOperator::Equality:
        case BinaryOperator::Inequality:
        case BinaryOperator::CaseEquality:
        case BinaryOperator::CaseInequality:
        case BinaryOperator::GreaterThanEqual:
        case BinaryOperator::GreaterThan:
        case BinaryOperator::LessThanEqual:
        case BinaryOperator::LessThan:
        case BinaryOperator::WildcardEquality:
        case BinaryOperator::WildcardInequality:
        case BinaryOperator::LogicalAnd:
        case BinaryOperator::LogicalOr:
        case BinaryOperator::LogicalImplication:
        case BinaryOperator::LogicalEquivalence:
            // Type is already set (always 1 bit) and operands are already folded.
            return false;
        case BinaryOperator::LogicalShiftLeft:
        case BinaryOperator::LogicalShiftRight:
        case BinaryOperator::ArithmeticShiftLeft:
        case BinaryOperator::ArithmeticShiftRight:
        case BinaryOperator::Power:
            // Only the left hand side gets propagated; the rhs is self determined.
            type = &newType;
            contextDetermined(context, left_, newType);
            return true;
    }
    SLANG_UNREACHABLE;
}

std::optional<bitwidth_t> BinaryExpression::getEffectiveWidthImpl() const {
    switch (op) {
        case BinaryOperator::Add:
        case BinaryOperator::Subtract:
        case BinaryOperator::Multiply:
        case BinaryOperator::Divide:
        case BinaryOperator::Mod:
        case BinaryOperator::BinaryAnd:
        case BinaryOperator::BinaryOr:
        case BinaryOperator::BinaryXor:
        case BinaryOperator::BinaryXnor:
            return std::max(left().getEffectiveWidth(), right().getEffectiveWidth());
        case BinaryOperator::LogicalShiftLeft:
        case BinaryOperator::LogicalShiftRight:
        case BinaryOperator::ArithmeticShiftLeft:
        case BinaryOperator::ArithmeticShiftRight:
        case BinaryOperator::Power:
            return left().getEffectiveWidth();
        default:
            return type->getBitWidth();
    }
}

ConstantValue BinaryExpression::evalImpl(EvalContext& context) const {
    if (left().kind == ExpressionKind::TypeReference &&
        right().kind == ExpressionKind::TypeReference) {
        auto& lt = left().as<TypeReferenceExpression>().targetType;
        auto& rt = right().as<TypeReferenceExpression>().targetType;
        bool val = lt.isMatching(rt);
        if (op == BinaryOperator::Inequality || op == BinaryOperator::CaseInequality)
            val = !val;

        return SVInt(1, val, false);
    }

    ConstantValue cvl = left().eval(context);
    if (!cvl)
        return nullptr;

    // Handle short-circuiting operators up front, as we need to avoid
    // evaluating the rhs entirely in those cases.
    if (isShortCircuitOp(op)) {
        switch (op) {
            case BinaryOperator::LogicalOr:
                if (cvl.isTrue())
                    return SVInt(true);
                break;
            case BinaryOperator::LogicalAnd:
                if (cvl.isFalse())
                    return SVInt(false);
                break;
            case BinaryOperator::LogicalImplication:
                if (cvl.isFalse())
                    return SVInt(true);
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    ConstantValue cvr = right().eval(context);
    if (!cvr)
        return nullptr;

    return evalBinaryOperator(op, cvl, cvr);
}

void BinaryExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("op", toString(op));
    serializer.write("left", left());
    serializer.write("right", right());
}

Expression& ConditionalExpression::fromSyntax(Compilation& comp,
                                              const ConditionalExpressionSyntax& syntax,
                                              const ASTContext& context,
                                              const Type* assignmentTarget) {
    bool bad = false;
    bool isConst = true;
    bool isTrue = true;
    bool isFourState = false;
    SmallVector<Condition> conditions;
    ASTContext trueContext = context;

    for (auto condSyntax : syntax.predicate->conditions) {
        auto& cond = selfDetermined(comp, *condSyntax->expr, trueContext);
        bad |= cond.bad();

        const Pattern* pattern = nullptr;
        if (condSyntax->matchesClause) {
            Pattern::VarMap patternVarMap;
            pattern = &Pattern::bind(*condSyntax->matchesClause->pattern, *cond.type, patternVarMap,
                                     trueContext);

            // We don't consider the condition to be const if there's a pattern.
            isConst = false;
            bad |= pattern->bad();
        }
        else {
            isFourState |= cond.type->isFourState();
            if (!bad && !trueContext.requireBooleanConvertible(cond))
                bad = true;
        }

        if (!bad && isConst) {
            ConstantValue condVal = trueContext.tryEval(cond);
            if (!condVal || (condVal.isInteger() && condVal.integer().hasUnknown()))
                isConst = false;
            else if (!condVal.isTrue())
                isTrue = false;
        }

        conditions.push_back({&cond, pattern});
    }

    // If the predicate is known at compile time, we can tell which branch will be unevaluated.
    bitmask<ASTFlags> leftFlags = ASTFlags::None;
    bitmask<ASTFlags> rightFlags = ASTFlags::None;
    if (isConst) {
        if (isTrue)
            rightFlags = ASTFlags::UnevaluatedBranch;
        else
            leftFlags = ASTFlags::UnevaluatedBranch;
    }

    // Pass through the flag allowing unbounded literals.
    if (context.flags.has(ASTFlags::AllowUnboundedLiteral) &&
        context.flags.has(ASTFlags::AllowUnboundedLiteralArithmetic)) {
        leftFlags |= ASTFlags::AllowUnboundedLiteral;
        rightFlags |= ASTFlags::AllowUnboundedLiteral;
    }

    auto& left = create(comp, *syntax.left, trueContext, leftFlags, assignmentTarget);
    auto& right = create(comp, *syntax.right, context, rightFlags, assignmentTarget);
    bad |= left.bad() || right.bad();

    const Type* lt = left.type;
    const Type* rt = right.type;
    if (lt->isUnbounded())
        lt = &comp.getIntType();
    if (rt->isUnbounded())
        rt = &comp.getIntType();

    // Force four-state return type for ambiguous condition case.
    const Type* resultType = binaryOperatorType(comp, lt, rt, isFourState);
    auto result = comp.emplace<ConditionalExpression>(*resultType, conditions.copy(comp), left,
                                                      right, syntax.sourceRange());
    if (bad)
        return badExpr(comp, result);

    // If both sides of the expression are numeric, we've already determined the correct
    // result type. Otherwise, follow the rules in [11.14.11].
    bool good = true;
    if (!lt->isNumeric() || !rt->isNumeric()) {
        if (lt->isNull() && rt->isNull()) {
            result->type = &comp.getNullType();
        }
        else if (lt->isClass() || rt->isClass() || lt->isCHandle() || rt->isCHandle() ||
                 lt->isEvent() || rt->isEvent() || lt->isVirtualInterface() ||
                 rt->isVirtualInterface() || lt->isCovergroup() || rt->isCovergroup()) {
            if (lt->isNull())
                result->type = rt;
            else if (rt->isNull())
                result->type = lt;
            else if (rt->isAssignmentCompatible(*lt))
                result->type = rt;
            else if (lt->isAssignmentCompatible(*rt))
                result->type = lt;
            else if (auto common = Type::getCommonBase(*lt, *rt))
                result->type = common;
            else if (lt->isEquivalent(*rt))
                result->type = lt;
            else
                good = false;
        }
        else if (lt->isEquivalent(*rt) && !lt->isUnpackedUnion()) {
            result->type = lt;
        }
        else if (left.isImplicitString() && right.isImplicitString()) {
            result->type = &comp.getStringType();
        }
        else {
            good = false;
        }
    }

    if (!good) {
        auto& diag = context.addDiag(diag::BadConditionalExpression, syntax.question.location());
        diag << *lt << *rt;
        diag << left.sourceRange;
        diag << right.sourceRange;
        return badExpr(comp, result);
    }

    context.setAttributes(*result, syntax.attributes);
    return *result;
}

bool ConditionalExpression::propagateType(const ASTContext& context, const Type& newType) {
    // The predicate is self determined so no need to handle it here.
    type = &newType;
    contextDetermined(context, left_, newType);
    contextDetermined(context, right_, newType);
    return true;
}

std::optional<bitwidth_t> ConditionalExpression::getEffectiveWidthImpl() const {
    return std::max(left().getEffectiveWidth(), right().getEffectiveWidth());
}

ConstantValue ConditionalExpression::evalImpl(EvalContext& context) const {
    ConstantValue cp;
    for (auto& cond : conditions) {
        cp = cond.expr->eval(context);
        if (cond.pattern)
            cp = cond.pattern->eval(context, cp, CaseStatementCondition::Normal);

        if (cp.bad())
            return nullptr;

        if (!cp.isTrue())
            break;
    }

    // When the conditional predicate is unknown, there are rules to combine both sides
    // and return the hybrid result.
    if (cp.isInteger() && cp.integer().hasUnknown()) {
        ConstantValue cvl = left().eval(context);
        ConstantValue cvr = right().eval(context);
        if (!cvl || !cvr)
            return nullptr;

        if (cvl.isInteger() && cvr.isInteger())
            return SVInt::conditional(cp.integer(), cvl.integer(), cvr.integer());

        auto combineArrays = [&](auto& result, auto& la, auto& ra) -> ConstantValue {
            ConstantValue defaultElement = type->getArrayElementType()->getDefaultValue();

            // [11.4.11] says that if both sides are unpacked arrays, we
            // check each element. If they are equal, take it in the result,
            // otherwise use the default.
            for (size_t i = 0; i < la.size(); i++) {
                ConstantValue comp = evalBinaryOperator(BinaryOperator::Equality, la[i], ra[i]);
                if (!comp)
                    return nullptr;

                logic_t l = (logic_t)comp.integer();
                if (l.isUnknown() || !l)
                    result[i] = defaultElement;
                else
                    result[i] = la[i];
            }

            return result;
        };

        if (cvl.isUnpacked()) {
            // Sizes here might differ for dynamic arrays.
            std::span<const ConstantValue> la = cvl.elements();
            std::span<const ConstantValue> ra = cvr.elements();
            if (la.size() == ra.size() && type->isArray()) {
                std::vector<ConstantValue> result(la.size());
                return combineArrays(result, la, ra);
            }
        }
        else if (cvl.isQueue()) {
            auto& la = *cvl.queue();
            auto& ra = *cvr.queue();
            if (la.size() == ra.size()) {
                SVQueue result(la.size());
                return combineArrays(result, la, ra);
            }
        }

        return type->getDefaultValue();
    }

    if (cp.isTrue())
        return left().eval(context);
    else
        return right().eval(context);
}

void ConditionalExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("conditions");
    for (auto& cond : conditions) {
        serializer.startObject();
        serializer.write("expr", *cond.expr);
        if (cond.pattern)
            serializer.write("pattern", *cond.pattern);
        serializer.endObject();
    }
    serializer.endArray();

    serializer.write("left", left());
    serializer.write("right", right());
}

Expression& InsideExpression::fromSyntax(Compilation& compilation,
                                         const InsideExpressionSyntax& syntax,
                                         const ASTContext& context) {
    SmallVector<const ExpressionSyntax*> expressions;
    for (auto elemSyntax : syntax.ranges->valueRanges)
        expressions.push_back(elemSyntax);

    SmallVector<const Expression*> bound;
    bool bad =
        !bindMembershipExpressions(context, TokenKind::InsideKeyword, /* requireIntegral */ false,
                                   /* unwrapUnpacked */ true, /* allowTypeReferences */ false,
                                   /* allowOpenRange */ true, *syntax.expr, expressions, bound);

    auto boundSpan = bound.copy(compilation);
    auto result = compilation.emplace<InsideExpression>(compilation.getLogicType(), *boundSpan[0],
                                                        boundSpan.subspan(1), syntax.sourceRange());
    if (bad)
        return badExpr(compilation, result);

    return *result;
}

static logic_t checkInsideMatch(const ConstantValue& cvl, const ConstantValue& cvr) {
    // Unpacked arrays get unwrapped into their members for comparison.
    if (cvr.isContainer()) {
        bool anyUnknown = false;
        for (auto& elem : cvr) {
            logic_t result = checkInsideMatch(cvl, elem);
            if (result)
                return logic_t(true);

            if (result.isUnknown())
                anyUnknown = true;
        }

        return anyUnknown ? logic_t::x : logic_t(0);
    }

    // Otherwise, we do a wildcard comparison if both sides are integers
    // and an equivalence comparison if not.
    if (cvl.isInteger() && cvr.isInteger())
        return condWildcardEqual(cvl.integer(), cvr.integer());

    return logic_t(cvl == cvr);
}

ConstantValue InsideExpression::evalImpl(EvalContext& context) const {
    ConstantValue cvl = left().eval(context);
    if (!cvl)
        return nullptr;

    bool anyUnknown = false;
    for (auto elem : rangeList()) {
        logic_t result;
        if (elem->kind == ExpressionKind::OpenRange) {
            ConstantValue cvr = elem->as<OpenRangeExpression>().checkInside(context, cvl);
            if (!cvr)
                return nullptr;

            result = (logic_t)cvr.integer();
        }
        else {
            ConstantValue cvr = elem->eval(context);
            if (!cvr)
                return nullptr;

            result = checkInsideMatch(cvl, cvr);
        }

        if (result)
            return SVInt(logic_t(true));

        if (result.isUnknown())
            anyUnknown = true;
    }

    return SVInt(anyUnknown ? logic_t::x : logic_t(0));
}

void InsideExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("left", left());

    if (!rangeList().empty()) {
        serializer.startArray("rangeList");
        for (auto elem : rangeList())
            serializer.serialize(*elem);
        serializer.endArray();
    }
}

Expression& ConcatenationExpression::fromSyntax(Compilation& compilation,
                                                const ConcatenationExpressionSyntax& syntax,
                                                const ASTContext& context,
                                                const Type* assignmentTarget) {
    // If we are in an assignment-like context with a target type that is an unpacked array,
    // this is an array concatenation (as opposed to a vector or string concatenation).
    if (assignmentTarget && assignmentTarget->isUnpackedArray()) {
        if (assignmentTarget->isAssociativeArray()) {
            context.addDiag(diag::UnpackedConcatAssociative, syntax.sourceRange());
            return badExpr(compilation, nullptr);
        }

        // TODO: check overflow handling
        bool bad = false;
        bool anyDynamic = false;
        size_t totalElems = 0;
        const Type& type = *assignmentTarget;
        const Type& elemType = *type.getArrayElementType();
        SmallVector<Expression*> buffer;

        for (auto argSyntax : syntax.expressions) {
            Expression* arg = &create(compilation, *argSyntax, context);
            if (arg->bad()) {
                bad = true;
                continue;
            }

            if (arg->isImplicitlyAssignableTo(compilation, elemType)) {
                buffer.push_back(&convertAssignment(context, elemType, *arg,
                                                    argSyntax->getFirstToken().location()));
                totalElems++;
                continue;
            }

            // The argument can be an unpacked array as long as its element type is
            // assignment compatible with the target.
            auto& argType = *arg->type;
            if (argType.isUnpackedArray() &&
                elemType.isAssignmentCompatible(*argType.getArrayElementType())) {
                // If this is a dynamic array we can't check element counts statically.
                // Otherwise we should count each fixed element in the total.
                if (argType.hasFixedRange())
                    totalElems += argType.getFixedRange().width();
                else
                    anyDynamic = true;

                selfDetermined(context, arg);
                buffer.push_back(arg);
                continue;
            }

            // Otherwise this is an error.
            bad = true;
            context.addDiag(diag::BadConcatExpression, arg->sourceRange) << argType;
            selfDetermined(context, arg);
            buffer.push_back(arg);
        }

        // If we have a fixed size source and target, check that they match in size.
        if (!bad && !anyDynamic && type.hasFixedRange() &&
            type.getFixedRange().width() != totalElems) {
            context.addDiag(diag::UnpackedConcatSize, syntax.sourceRange())
                << type << type.getFixedRange().width() << totalElems;
            bad = true;
        }

        auto result = compilation.emplace<ConcatenationExpression>(type, buffer.ccopy(compilation),
                                                                   syntax.sourceRange());
        if (bad)
            return badExpr(compilation, result);

        return *result;
    }

    bool errored = false;
    bool unsizedWarned = false;
    bool anyStrings = false;
    bitmask<IntegralFlags> flags;
    bitwidth_t totalWidth = 0;
    SmallVector<Expression*> buffer;

    for (auto argSyntax : syntax.expressions) {
        // Replications inside of concatenations have a special feature that allows them to have
        // a width of zero. Check now if we're going to be creating a replication and if so set
        // an additional flag so that it knows it's ok to have that zero count.
        Expression* arg;
        if (argSyntax->kind == SyntaxKind::MultipleConcatenationExpression)
            arg = &create(compilation, *argSyntax, context, ASTFlags::InsideConcatenation);
        else
            arg = &create(compilation, *argSyntax, context);
        buffer.push_back(arg);

        if (arg->bad()) {
            errored = true;
            break;
        }

        const Type& type = *arg->type;
        if (type.isVoid() && argSyntax->kind == SyntaxKind::MultipleConcatenationExpression)
            continue;

        if (type.isString()) {
            anyStrings = true;
            continue;
        }

        if (!type.isIntegral()) {
            errored = true;
            context.addDiag(diag::BadConcatExpression, arg->sourceRange) << type;
            break;
        }

        if (arg->isUnsizedInteger() && !unsizedWarned) {
            context.addDiag(diag::UnsizedInConcat, arg->sourceRange) << type.getBitWidth();
            unsizedWarned = true;
        }

        // Can't overflow because 2*maxWidth is still less than 2^32-1.
        totalWidth += type.getBitWidth();

        if (!context.requireValidBitWidth(totalWidth, syntax.sourceRange())) {
            errored = true;
            break;
        }

        if (type.isFourState())
            flags |= IntegralFlags::FourState;
    }

    if (!errored) {
        for (size_t i = 0; i < buffer.size(); i++) {
            if (!anyStrings) {
                selfDetermined(context, buffer[i]);
            }
            else {
                Expression* expr = buffer[i];
                if (expr->type->isString()) {
                    selfDetermined(context, expr);
                }
                else if (expr->isImplicitString()) {
                    expr = &ConversionExpression::makeImplicit(context, compilation.getStringType(),
                                                               ConversionKind::Implicit, *expr,
                                                               expr->sourceRange.start());
                }
                else {
                    errored = true;
                    context.addDiag(diag::ConcatWithStringInt, expr->sourceRange);
                    break;
                }
                buffer[i] = expr;
            }
        }

        if (!anyStrings && totalWidth == 0) {
            context.addDiag(diag::EmptyConcatNotAllowed, syntax.sourceRange());
            errored = true;
        }
    }

    if (errored) {
        return badExpr(compilation,
                       compilation.emplace<ConcatenationExpression>(compilation.getErrorType(),
                                                                    std::span<const Expression*>(),
                                                                    syntax.sourceRange()));
    }

    const Type* type;
    if (anyStrings)
        type = &compilation.getStringType();
    else
        type = &compilation.getType(totalWidth, flags);

    return *compilation.emplace<ConcatenationExpression>(*type, buffer.ccopy(compilation),
                                                         syntax.sourceRange());
}

Expression& ConcatenationExpression::fromEmpty(Compilation& compilation,
                                               const EmptyQueueExpressionSyntax& syntax,
                                               const ASTContext& context,
                                               const Type* assignmentTarget) {
    // Empty concatenation can only target arrays.
    if (!assignmentTarget || !assignmentTarget->isUnpackedArray()) {
        context.addDiag(diag::EmptyConcatNotAllowed, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    if (assignmentTarget->isAssociativeArray()) {
        context.addDiag(diag::UnpackedConcatAssociative, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    if (assignmentTarget->hasFixedRange()) {
        context.addDiag(diag::UnpackedConcatSize, syntax.sourceRange())
            << *assignmentTarget << assignmentTarget->getFixedRange().width() << 0;
        return badExpr(compilation, nullptr);
    }

    return *compilation.emplace<ConcatenationExpression>(*assignmentTarget,
                                                         std::span<const Expression* const>{},
                                                         syntax.sourceRange());
}

ConstantValue ConcatenationExpression::evalImpl(EvalContext& context) const {
    if (type->isUnpackedArray()) {
        auto& elemType = *type->getArrayElementType();
        auto build = [&](auto&& result) {
            for (auto op : operands()) {
                ConstantValue cv = op->eval(context);
                if (!cv)
                    return false;

                // Check if we can take this element as-is or if we need to
                // unwrap it into constituents.
                if (elemType.isEquivalent(*op->type))
                    result.emplace_back(std::move(cv));
                else {
                    SLANG_ASSERT(cv.isContainer());
                    const Type& from = *op->type->getArrayElementType();
                    for (auto& elem : cv) {
                        result.emplace_back(ConversionExpression::convert(
                            context, from, elemType, op->sourceRange, std::move(elem),
                            ConversionKind::Implicit));
                    }
                }
            }
            return true;
        };

        if (type->isQueue()) {
            SVQueue result;
            result.maxBound = type->getCanonicalType().as<QueueType>().maxBound;
            if (!build(result))
                return nullptr;

            result.resizeToBound();
            return result;
        }
        else {
            std::vector<ConstantValue> result;
            if (!build(result))
                return nullptr;

            // If we have a fixed size target, check that they match in size.
            if (type->hasFixedRange() && type->getFixedRange().width() != result.size()) {
                context.addDiag(diag::UnpackedConcatSize, sourceRange)
                    << *type << type->getFixedRange().width() << result.size();
                return nullptr;
            }

            return result;
        }
    }

    if (type->isString()) {
        std::string result;
        for (auto operand : operands()) {
            ConstantValue v = operand->eval(context);
            if (!v)
                return nullptr;

            // Skip zero-width replication operands.
            if (operand->type->isVoid())
                continue;

            result.append(v.str());
        }

        return result;
    }

    SmallVector<SVInt, 4> values;
    for (auto operand : operands()) {
        ConstantValue v = operand->eval(context);
        if (!v)
            return nullptr;

        // Skip zero-width replication operands.
        if (operand->type->isVoid())
            continue;

        values.push_back(v.integer());
    }

    return SVInt::concat(values);
}

LValue ConcatenationExpression::evalLValueImpl(EvalContext& context) const {
    std::vector<LValue> lvals;
    lvals.reserve(operands().size());
    for (auto operand : operands()) {
        LValue lval = operand->evalLValue(context);
        if (!lval)
            return nullptr;

        lvals.emplace_back(std::move(lval));
    }

    return LValue(std::move(lvals));
}

void ConcatenationExpression::serializeTo(ASTSerializer& serializer) const {
    if (!operands().empty()) {
        serializer.startArray("operands");
        for (auto op : operands())
            serializer.serialize(*op);
        serializer.endArray();
    }
}

Expression& ReplicationExpression::fromSyntax(Compilation& compilation,
                                              const MultipleConcatenationExpressionSyntax& syntax,
                                              const ASTContext& context) {
    Expression& left = selfDetermined(compilation, *syntax.expression, context);
    Expression* right = &create(compilation, *syntax.concatenation, context);

    auto result = compilation.emplace<ReplicationExpression>(compilation.getErrorType(), left,
                                                             *right, syntax.sourceRange());
    if (left.bad() || right->bad())
        return badExpr(compilation, result);

    if (!left.type->isIntegral() || (!right->type->isIntegral() && !right->type->isString())) {
        auto& diag = context.addDiag(diag::BadReplicationExpression,
                                     syntax.concatenation->getFirstToken().location());
        diag << *left.type << *right->type;
        diag << left.sourceRange;
        diag << right->sourceRange;
        return badExpr(compilation, result);
    }

    // If the multiplier isn't constant this must be a string replication.
    EvalContext evalCtx(compilation, EvalFlags::CacheResults);
    if (ConstantValue leftVal = left.eval(evalCtx); !leftVal) {
        if (!right->isImplicitString()) {
            // They probably meant for this to be a constant (non-string) replication,
            // so do the normal error reporting for that case.
            evalCtx.reportDiags(context);
            return badExpr(compilation, result);
        }

        contextDetermined(context, right, compilation.getStringType());

        result->concat_ = right;
        result->type = &compilation.getStringType();
        return *result;
    }

    std::optional<int32_t> count = context.evalInteger(left);
    if (!count)
        return badExpr(compilation, result);

    if (*count < 0) {
        context.requireGtZero(count, left.sourceRange);
        return badExpr(compilation, result);
    }

    if (*count == 0) {
        if (!context.flags.has(ASTFlags::InsideConcatenation)) {
            context.addDiag(diag::ReplicationZeroOutsideConcat, left.sourceRange);
            return badExpr(compilation, result);
        }

        // Use a placeholder type here to indicate to the parent concatenation that this had a
        // zero width.
        result->type = &compilation.getVoidType();
        return *result;
    }

    selfDetermined(context, right);
    result->concat_ = right;

    if (right->type->isString()) {
        result->type = &compilation.getStringType();
        return *result;
    }

    auto width = context.requireValidBitWidth(
        SVInt(32, uint64_t(*count), true) * right->type->getBitWidth(), syntax.sourceRange());
    if (!width)
        return badExpr(compilation, result);

    result->type = &compilation.getType(*width, right->type->isFourState()
                                                    ? IntegralFlags::FourState
                                                    : IntegralFlags::TwoState);
    return *result;
}

ConstantValue ReplicationExpression::evalImpl(EvalContext& context) const {
    // Operands are always evaluated, even if count is zero.
    ConstantValue v = concat().eval(context);
    ConstantValue c = count().eval(context);
    if (!v || !c)
        return nullptr;

    if (type->isVoid())
        return ConstantValue::NullPlaceholder();

    if (type->isString()) {
        std::optional<int32_t> optCount = c.integer().as<int32_t>();
        if (!optCount || *optCount < 0) {
            context.addDiag(diag::ConstEvalReplicationCountInvalid, count().sourceRange) << c;
            return nullptr;
        }

        std::string result;
        for (int32_t i = 0; i < *optCount; i++)
            result.append(v.str());

        return result;
    }

    return v.integer().replicate(c.integer());
}

void ReplicationExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("count", count());
    serializer.write("concat", concat());
}

Expression& StreamingConcatenationExpression::fromSyntax(
    Compilation& comp, const StreamingConcatenationExpressionSyntax& syntax,
    const ASTContext& context, const Type* assignmentTarget) {

    // The sole purpose of assignmentTarget here is to know whether this is a
    // "destination" stream (i.e. an unpack operation) or whether it is a source / pack.
    // Streaming concatenation is self-determined and its size/type should not be affected
    // by assignmentTarget.
    const bool isDestination = !assignmentTarget;

    const bool isRightToLeft = syntax.operatorToken.kind == TokenKind::LeftShift;
    size_t sliceSize = 0;

    auto badResult = [&]() -> Expression& {
        return badExpr(comp, comp.emplace<StreamingConcatenationExpression>(
                                 comp.getErrorType(), sliceSize,
                                 std::span<const StreamExpression>(), syntax.sourceRange()));
    };

    if (!context.flags.has(ASTFlags::StreamingAllowed)) {
        context.addDiag(diag::BadStreamContext, syntax.operatorToken.location());
        return badResult();
    }

    if (syntax.sliceSize) {
        // The slice_size determines the size of each block. If specified, it may be a constant
        // integral expression or a simple type.
        auto& sliceExpr = bind(*syntax.sliceSize, context, ASTFlags::AllowDataType);
        if (sliceExpr.bad())
            return badResult();

        if (sliceExpr.kind == ExpressionKind::DataType) {
            if (!sliceExpr.type->isFixedSize()) {
                auto& diag = context.addDiag(diag::BadStreamSlice, sliceExpr.sourceRange);
                if (sliceExpr.type->location)
                    diag.addNote(diag::NoteDeclarationHere, sliceExpr.type->location);
                return badResult();
            }
            sliceSize = sliceExpr.type->bitstreamWidth();
        }
        else {
            // It shall be an error for the value to be zero or negative.
            std::optional<int32_t> count = context.evalInteger(sliceExpr);
            if (!context.requireGtZero(count, sliceExpr.sourceRange))
                return badResult();
            sliceSize = static_cast<size_t>(*count);
        }

        if (!isRightToLeft) {
            // Left-to-right streaming using >> shall cause the slice_size to be ignored and no
            // re-ordering performed.
            sliceSize = 0;
            context.addDiag(diag::IgnoredSlice, syntax.sliceSize->sourceRange());
        }
    }
    else if (isRightToLeft) {
        // If a slice_size is not specified, the default is 1.
        sliceSize = 1;
    }

    SmallVector<StreamExpression, 4> buffer;
    for (const auto argSyntax : syntax.expressions) {
        Expression* arg;
        if (assignmentTarget &&
            argSyntax->expression->kind == SyntaxKind::StreamingConcatenationExpression) {
            arg = &create(comp, *argSyntax->expression, context, ASTFlags::StreamingAllowed,
                          assignmentTarget);
        }
        else {
            arg = &selfDetermined(comp, *argSyntax->expression, context,
                                  ASTFlags::StreamingAllowed);
        }

        if (arg->bad())
            return badResult();

        const Expression* withExpr = nullptr;
        std::optional<bitwidth_t> constantWithWidth;
        if (argSyntax->withRange) {
            // The expression before the with can be any one-dimensional unpacked array
            // (including a queue). Interpreted as fixed-sized unpacked arrays,
            // dynamic arrays, or queues of fixed-size elements.
            auto& arrayType = *arg->type;
            if (!arrayType.isUnpackedArray() || arrayType.isAssociativeArray() ||
                !arrayType.getArrayElementType()->isFixedSize()) {
                context.addDiag(diag::BadStreamWithType, arg->sourceRange);
                return badResult();
            }

            withExpr = &bindSelector(comp, *arg, *argSyntax->withRange->range,
                                     context.resetFlags(ASTFlags::StreamingWithRange));
            if (withExpr->bad())
                return badResult();

            // Try to get the bounds of the selection, if they are constant.
            EvalContext evalCtx(comp);
            auto range = withExpr->evalSelector(evalCtx);
            if (range)
                constantWithWidth = range->width();
        }

        if (argSyntax->expression->kind != SyntaxKind::StreamingConcatenationExpression) {
            // Unpacked unions get "unwrapped" to their first member when streaming.
            const Type* type = arg->type;
            if (type->isUnpackedUnion() && !type->isTaggedUnion()) {
                auto& uu = type->getCanonicalType().as<UnpackedUnionType>();
                auto members = uu.members();
                if (members.begin() != members.end())
                    type = &members.begin()->as<ValueSymbol>().getType();
            }

            if (!type->isBitstreamType(isDestination)) {
                context.addDiag(diag::BadStreamExprType, arg->sourceRange) << *arg->type;
                return badResult();
            }
        }

        buffer.push_back({arg, withExpr, constantWithWidth});
    }

    // Streaming concatenation has no explicit type. Use void to prevent problems when
    // its type is passed to context-determined expressions.
    return *comp.emplace<StreamingConcatenationExpression>(comp.getVoidType(), sliceSize,
                                                           buffer.ccopy(comp),
                                                           syntax.sourceRange());
}

ConstantValue StreamingConcatenationExpression::evalImpl(EvalContext& context) const {
    std::vector<ConstantValue> values;
    values.reserve(streams().size());
    for (auto& stream : streams()) {
        auto cv = stream.operand->eval(context);
        if (!cv)
            return nullptr;

        if (stream.withExpr) {
            auto range = stream.withExpr->evalSelector(context);
            if (!range)
                return nullptr;

            // If the range expression evaluates to a range greater than the extent of the array
            // size, the entire array is streamed, and the remaining items are generated using the
            // nonexistent array entry value
            cv = Bitstream::resizeToRange(
                std::move(cv), *range,
                stream.operand->type->getArrayElementType()->getDefaultValue());
        }

        values.emplace_back(std::move(cv));
    }

    if (sliceSize > 0)
        return Bitstream::reOrder(std::move(values), sliceSize);

    return values;
}

void StreamingConcatenationExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("sliceSize", sliceSize);
    if (!streams().empty()) {
        serializer.startArray("streams");
        for (auto& stream : streams()) {
            serializer.startObject();
            serializer.write("operand", *stream.operand);
            if (stream.withExpr)
                serializer.write("withExpr", *stream.withExpr);
            serializer.endObject();
        }
        serializer.endArray();
    }
}

bool StreamingConcatenationExpression::isFixedSize() const {
    for (auto& stream : streams()) {
        if (stream.operand->kind == ExpressionKind::Streaming) {
            if (!stream.operand->as<StreamingConcatenationExpression>().isFixedSize())
                return false;
        }
        else if (stream.withExpr) {
            if (!stream.constantWithWidth.has_value())
                return false;
        }
        else {
            if (!stream.operand->type->isFixedSize())
                return false;
        }
    }
    return true;
}

size_t StreamingConcatenationExpression::bitstreamWidth() const {
    size_t width = 0;
    for (auto& stream : streams()) {
        auto& operand = *stream.operand;
        if (operand.kind == ExpressionKind::Streaming) {
            width += operand.as<StreamingConcatenationExpression>().bitstreamWidth();
        }
        else if (stream.withExpr) {
            // TODO: overflow
            size_t count = stream.constantWithWidth.value_or(1);
            width += count * operand.type->getArrayElementType()->bitstreamWidth();
        }
        else if (operand.type->isUnpackedUnion()) {
            auto& uu = operand.type->getCanonicalType().as<UnpackedUnionType>();
            auto members = uu.members();
            if (members.begin() != members.end())
                width += members.begin()->as<ValueSymbol>().getType().bitstreamWidth();
        }
        else {
            width += operand.type->bitstreamWidth();
        }
    }
    return width;
}

Expression& OpenRangeExpression::fromSyntax(Compilation& comp,
                                            const OpenRangeExpressionSyntax& syntax,
                                            const ASTContext& context) {
    // If we are allowed unbounded literals here, pass that along to subexpressions.
    bitmask<ASTFlags> flags = ASTFlags::None;
    if (context.flags.has(ASTFlags::AllowUnboundedLiteral))
        flags = ASTFlags::AllowUnboundedLiteral;

    Expression& left = create(comp, *syntax.left, context, flags);
    Expression& right = create(comp, *syntax.right, context, flags);

    auto result = comp.emplace<OpenRangeExpression>(comp.getVoidType(), left, right,
                                                    syntax.sourceRange());
    if (left.bad() || right.bad())
        return badExpr(comp, result);

    auto lt = left.type;
    auto rt = right.type;
    if (lt->isUnbounded()) {
        lt = &comp.getIntType();
        if (rt->isUnbounded())
            context.addDiag(diag::OpenRangeUnbounded, result->sourceRange);
    }

    if (rt->isUnbounded())
        rt = &comp.getIntType();

    if (!(lt->isNumeric() && rt->isNumeric()) &&
        !(left.isImplicitString() && right.isImplicitString())) {
        auto& diag = context.addDiag(diag::BadOpenRange, syntax.colon.location());
        diag << left.sourceRange << right.sourceRange << *lt << *rt;
        return badExpr(comp, result);
    }

    auto cvl = context.tryEval(left);
    auto cvr = context.tryEval(right);
    if (cvl.isInteger() && cvr.isInteger() && bool(cvl.integer() > cvr.integer()))
        context.addDiag(diag::ReversedOpenRange, result->sourceRange);

    return *result;
}

bool OpenRangeExpression::propagateType(const ASTContext& context, const Type& newType) {
    contextDetermined(context, left_, newType);
    contextDetermined(context, right_, newType);
    return true;
}

ConstantValue OpenRangeExpression::evalImpl(EvalContext&) const {
    // Should never enter this expecting a real result.
    return nullptr;
}

ConstantValue OpenRangeExpression::checkInside(EvalContext& context,
                                               const ConstantValue& val) const {
    ConstantValue cvl = left().eval(context);
    ConstantValue cvr = right().eval(context);
    if (!cvl || !cvr)
        return nullptr;

    cvl = evalBinaryOperator(BinaryOperator::GreaterThanEqual, val, cvl);
    cvr = evalBinaryOperator(BinaryOperator::LessThanEqual, val, cvr);
    return evalLogicalOp(BinaryOperator::LogicalAnd, cvl.integer(), cvr.integer());
}

void OpenRangeExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("left", left());
    serializer.write("right", right());
}

UnaryOperator Expression::getUnaryOperator(SyntaxKind kind) {
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

BinaryOperator Expression::getBinaryOperator(SyntaxKind kind) {
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

ConstantValue Expression::evalBinaryOperator(BinaryOperator op, const ConstantValue& cvl,
                                             const ConstantValue& cvr) {
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
            ConstantValue result = evalBinaryOperator(op, *li, *ri);
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

#undef OP
    SLANG_UNREACHABLE;
}

} // namespace slang::ast
