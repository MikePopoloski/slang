//------------------------------------------------------------------------------
// OperatorExpressions.cpp
// Definitions for operator expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/expressions/OperatorExpressions.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Bitstream.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/Patterns.h"
#include "slang/ast/expressions/ConversionExpression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/statements/ConditionalStatements.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/numeric/MathUtils.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

static std::optional<bitwidth_t> evalEffectiveWidth(const ASTContext& context,
                                                    const Expression& expr, TokenKind keyword) {
    auto cv = context.tryEval(expr);
    auto width = cv.getEffectiveWidth();
    if (!width)
        return std::nullopt;

    // If the case statement we are evaluating allows wildcards,
    // don't count a wildcard in a top bit as part of the effective
    // width, since it can match zeros.
    if (keyword == TokenKind::CaseXKeyword)
        return *width - cv.integer().countLeadingUnknowns();
    if (keyword == TokenKind::CaseZKeyword)
        return *width - cv.integer().countLeadingZs();
    return width;
}

bool Expression::bindMembershipExpressions(const ASTContext& context, TokenKind keyword,
                                           bool requireIntegral, bool unwrapUnpacked,
                                           bool allowTypeReferences, bool allowValueRange,
                                           const ExpressionSyntax& valueExpr,
                                           std::span<const ExpressionSyntax* const> expressions,
                                           SmallVectorBase<const Expression*>& results) {
    const auto keywordStr = LexerFacts::getTokenKindText(keyword);
    auto extraFlags = allowTypeReferences ? ASTFlags::AllowTypeReferences : ASTFlags::None;
    Compilation& comp = context.getCompilation();
    Expression& valueRes = create(comp, valueExpr, context, extraFlags);
    results.push_back(&valueRes);

    const Type* type = valueRes.type;
    auto valueWidth = evalEffectiveWidth(context, valueRes, keyword);
    bool bad = valueRes.bad();
    bool canBeStrings = valueRes.isImplicitString();

    if ((!requireIntegral && type->isAggregate()) || (requireIntegral && !type->isIntegral())) {
        if (!bad) {
            context.addDiag(diag::BadSetMembershipType, valueRes.sourceRange)
                << *type << keywordStr;
            bad = true;
        }
    }

    auto checkType = [&](const Expression& expr, const Type& bt) {
        if (bt.isNumeric() && type->isNumeric()) {
            type = OpInfo::binaryType(comp, type, &bt, false);
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
        else if (bt.isUnbounded() && (type->isNumeric() || type->isString())) {
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
            context.addDiag(diag::BadSetMembershipType, expr.sourceRange) << bt << keywordStr;
            bad = true;
        }
        else {
            // Couldn't find a common type.
            context.addDiag(diag::NoCommonComparisonType, expr.sourceRange)
                << keywordStr << bt << *type;
            bad = true;
        }

        if (!bad && !bt.isMatching(*valueRes.type) && !bt.isUnbounded()) {
            auto& lct = bt.getCanonicalType();
            auto& rct = valueRes.type->getCanonicalType();
            BinaryExpression::analyzeOpTypes(lct, rct, bt, *valueRes.type, expr, valueRes, context,
                                             expr.sourceRange, diag::CaseTypeMismatch,
                                             /* isComparison */ false, keywordStr);

            if (expr.type->isIntegral() && valueRes.type->isIntegral()) {
                // Check whether either the item or the value expression is
                // a constant integral (but not both). If so, check that the
                // constant value's effective width is not larger than the
                // bit width of the other expression, which would make it
                // impossible to ever match.
                auto exprWidth = evalEffectiveWidth(context, expr, keyword);
                auto vw = valueWidth.value_or(valueRes.type->getBitWidth());

                if (valueWidth > expr.type->getBitWidth() && !exprWidth) {
                    auto& diag = context.addDiag(diag::CaseOutsideRange, expr.sourceRange);
                    diag << keywordStr << expr.type->getBitWidth() << *valueWidth;
                }
                else if (exprWidth > vw && !valueWidth) {
                    auto& diag = context.addDiag(diag::CaseOutsideRange, expr.sourceRange);
                    diag << keywordStr << *exprWidth << vw;
                }
            }
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

        // Special handling for value range expressions -- they don't have
        // a real type on their own, we need to check their bounds.
        if (allowValueRange && bound->kind == ExpressionKind::ValueRange) {
            if (canBeStrings && !bound->isImplicitString())
                canBeStrings = false;

            auto& range = bound->as<ValueRangeExpression>();
            checkType(range.left(), *range.left().type);
            if (range.rangeKind == ValueRangeKind::Simple)
                checkType(range.right(), *range.right().type);
            continue;
        }

        const Type* bt = bound->type;
        if (requireIntegral) {
            if (!bt->isIntegral()) {
                context.addDiag(diag::BadSetMembershipType, bound->sourceRange)
                    << *bt << keywordStr;
                bad = true;
            }
            else {
                checkType(*bound, *bt);
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
            contextDetermined(context, expr, nullptr, *type, {});
        else
            selfDetermined(context, expr);

        SLANG_ASSERT(!expr->bad());
        results[index++] = expr;
    }

    return true;
}

Expression& UnaryExpression::fromSyntax(Compilation& compilation,
                                        const PrefixUnaryExpressionSyntax& syntax,
                                        const ASTContext& context) {
    auto op = OpInfo::getUnary(syntax.kind);
    bitmask<ASTFlags> extraFlags;
    if (OpInfo::isLValue(op))
        extraFlags = ASTFlags::LValue | ASTFlags::LAndRValue;

    Expression& operand = create(compilation, *syntax.operand, context, extraFlags);
    const Type* type = operand.type;

    auto result = compilation.emplace<UnaryExpression>(op, *type, operand, syntax.sourceRange(),
                                                       syntax.operatorToken.range());
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
            // Supported for all boolean convertible types. Result is a single bit.
            good = type->isBooleanConvertible();
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

    Expression* result = compilation.emplace<UnaryExpression>(OpInfo::getUnary(syntax.kind), *type,
                                                              operand, syntax.sourceRange(),
                                                              syntax.operatorToken.range());
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

bool UnaryExpression::propagateType(const ASTContext& context, const Type& newType,
                                    SourceRange propRange, ConversionKind) {
    switch (op) {
        case UnaryOperator::Plus:
        case UnaryOperator::Minus:
        case UnaryOperator::BitwiseNot:
            type = &newType;
            contextDetermined(context, operand_, this, newType, propRange);
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

Expression::EffectiveSign UnaryExpression::getEffectiveSignImpl(bool isForConversion) const {
    switch (op) {
        case UnaryOperator::Plus:
        case UnaryOperator::BitwiseNot:
            return operand().getEffectiveSign(isForConversion);
        case UnaryOperator::Minus:
            // If we're negating a number it should be signed.
            return EffectiveSign::Signed;
        default:
            return type->isSigned() ? EffectiveSign::Signed : EffectiveSign::Unsigned;
    }
}

ConstantValue UnaryExpression::evalImpl(EvalContext& context) const {
    // Handle operations that require an lvalue up front.
    if (OpInfo::isLValue(op)) {
        LValue lvalue = operand().evalLValue(context);
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
                    SLANG_UNREACHABLE;
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
                    SLANG_UNREACHABLE;
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
                    SLANG_UNREACHABLE;
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
    else if (op == UnaryOperator::LogicalNot) {
        return SVInt(cv.isFalse());
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

    Expression *lhs, *rhs;
    auto& syntaxLeft = *syntax.left;
    auto& syntaxRight = *syntax.right;

    auto op = OpInfo::getBinary(syntax.kind);
    if (op == BinaryOperator::Equality || op == BinaryOperator::Inequality ||
        op == BinaryOperator::CaseEquality || op == BinaryOperator::CaseInequality) {
        flags |= ASTFlags::AllowTypeReferences;

        // Special case to handle comparing a virtual interface with an
        // actual instance. We can't normally bind to an instance from
        // an expression so we need to explicitly try that separately here.
        lhs = tryBindInterfaceRef(context, syntaxLeft, /* isInterfacePort */ false);
        if (!lhs)
            lhs = &create(compilation, syntaxLeft, context, flags);

        // If we found a virtual interface on the lhs we can also try for an instance
        // on the rhs. Otherwise we know we're doing normal expression binding.
        if (lhs->type->isVirtualInterface()) {
            rhs = tryBindInterfaceRef(context, syntaxRight, /* isInterfacePort */ false);
            if (!rhs) {
                rhs = &create(compilation, syntaxRight, context, flags);
            }
            else if (lhs->kind == ExpressionKind::ArbitrarySymbol &&
                     rhs->kind == ExpressionKind::ArbitrarySymbol) {
                // Having an instance on both sides is not allowed. One side must be
                // an actual virtual interface.
                context.addDiag(diag::CannotCompareTwoInstances, syntax.operatorToken.location())
                    << lhs->sourceRange << rhs->sourceRange;
                return badExpr(compilation, nullptr);
            }
        }
        else {
            rhs = &create(compilation, syntaxRight, context, flags);
        }
    }
    else {
        lhs = &create(compilation, syntaxLeft, context, flags);

        if (OpInfo::isShortCircuit(op)) {
            // We want to evaluate the lhs as a constant if possible, to know whether
            // the rhs is for sure in an unevaluated context. This is required for
            // correctness in cases where the condition on the lhs gates off otherwise
            // invalid code on the rhs.
            if (auto val = context.tryEval(*lhs)) {
                switch (op) {
                    case BinaryOperator::LogicalAnd:
                    case BinaryOperator::LogicalImplication:
                        if (val.isFalse())
                            flags |= ASTFlags::UnevaluatedBranch;
                        break;
                    case BinaryOperator::LogicalOr:
                        if (val.isTrue())
                            flags |= ASTFlags::UnevaluatedBranch;
                        break;
                    default:
                        SLANG_UNREACHABLE;
                }
            }
        }

        rhs = &create(compilation, syntaxRight, context, flags);
    }

    auto& result = fromComponents(*lhs, *rhs, op, syntax.operatorToken.range(),
                                  syntax.sourceRange(), context);
    context.setAttributes(result, syntax.attributes);

    return result;
}

static void analyzePrecedence(const ASTContext& context, const Expression& lhs,
                              const Expression& rhs, BinaryOperator op, SourceRange opRange) {
    // Ignore compound assignments.
    if (lhs.kind == ExpressionKind::LValueReference)
        return;

    auto getBin = [](const Expression& expr) {
        return expr.isParenthesized() ? nullptr : expr.as_if<BinaryExpression>();
    };

    auto isBoolean = [](const Expression& expr) {
        return expr.type->isIntegral() && expr.type->getBitWidth() == 1;
    };

    // Warn when mixing bitwise ops and comparisons -- comparisons have higher precedence.
    // ex: `flags & 'h20 != 0` is equivalent to `flags & 1`
    if (OpInfo::isBitwise(op)) {
        auto lhsBin = getBin(lhs);
        auto rhsBin = getBin(rhs);

        const bool isLeftComp = lhsBin && OpInfo::isComparison(lhsBin->op);
        const bool isRightComp = rhsBin && OpInfo::isComparison(rhsBin->op);
        if (isLeftComp != isRightComp) {
            // Bitwise operations are sometimes used as eager logical ops.
            // Don't diagnose this.
            const bool isLeftBitwise = lhsBin && OpInfo::isBitwise(lhsBin->op);
            const bool isRightBitwise = rhsBin && OpInfo::isBitwise(rhsBin->op);
            const bool bothBoolean = isBoolean(lhs) && isBoolean(rhs);
            if (!isLeftBitwise && !isRightBitwise && !bothBoolean) {
                auto opStr = OpInfo::getText(op);
                auto compOpStr = isLeftComp ? OpInfo::getText(lhsBin->op)
                                            : OpInfo::getText(rhsBin->op);
                auto compRange = isLeftComp ? lhs.sourceRange : rhs.sourceRange;

                auto& diag = context.addDiag(diag::BitwiseRelPrecedence, opRange);
                diag << opStr << compOpStr << compOpStr << compRange;

                auto rewrittenRange =
                    isLeftComp
                        ? SourceRange(lhsBin->right().sourceRange.start(), rhs.sourceRange.end())
                        : SourceRange(lhs.sourceRange.start(), rhsBin->left().sourceRange.end());
                diag.addNote(diag::NotePrecedenceBitwiseFirst, rewrittenRange) << opStr;
                diag.addNote(diag::NotePrecedenceSilence, compRange) << compOpStr;
            }
        }
    }

    auto warnAWithinB = [&](DiagCode code, const BinaryExpression& binOp) {
        auto binOpText = OpInfo::getText(binOp.op);
        auto& diag = context.addDiag(code, binOp.opRange);
        diag << binOpText << OpInfo::getText(op);
        diag << binOp.sourceRange << opRange;
        diag.addNote(diag::NotePrecedenceSilence, binOp.opRange) << binOpText << binOp.sourceRange;
    };

    // Warn about `a & b | c` constructs.
    if (op == BinaryOperator::BinaryOr || op == BinaryOperator::BinaryXor ||
        op == BinaryOperator::BinaryXnor) {
        auto check = [&](const Expression& expr) {
            if (auto binOp = getBin(expr)) {
                if (OpInfo::isBitwise(binOp->op) &&
                    OpInfo::getPrecedence(binOp->op) > OpInfo::getPrecedence(op)) {
                    warnAWithinB(diag::BitwiseOpParentheses, *binOp);
                }
            }
        };

        check(lhs);
        check(rhs);
    }

    // Warn about `a && b || c` constructs (except in macros).
    if (op == BinaryOperator::LogicalOr) {
        auto check = [&](const Expression& expr) {
            if (auto binOp = getBin(expr)) {
                if (binOp->op == BinaryOperator::LogicalAnd)
                    warnAWithinB(diag::LogicalOpParentheses, *binOp);
            }
        };

        check(lhs);
        check(rhs);
    }

    // Warn about `x << 1 + 1` constructs.
    if (OpInfo::isShift(op)) {
        auto check = [&](const Expression& expr) {
            if (auto binOp = getBin(expr)) {
                if (binOp->op == BinaryOperator::Add || binOp->op == BinaryOperator::Subtract) {
                    auto binOpText = OpInfo::getText(binOp->op);
                    auto& diag = context.addDiag(diag::ArithInShift, binOp->opRange);
                    diag << OpInfo::getText(op) << binOpText << binOpText;
                    diag << binOp->sourceRange << opRange;
                    diag.addNote(diag::NotePrecedenceSilence, binOp->opRange)
                        << binOpText << binOp->sourceRange;
                }
            }
        };

        check(lhs);
        check(rhs);
    }

    // Warn about `!x < y` and `!x & y` where they probably meant `!(x < y)` and `!(x & y)`
    if ((OpInfo::isComparison(op) || op == BinaryOperator::BinaryAnd) &&
        lhs.kind == ExpressionKind::UnaryOp && !lhs.isParenthesized() &&
        lhs.as<UnaryExpression>().op == UnaryOperator::LogicalNot) {

        auto& unary = lhs.as<UnaryExpression>();
        if (!isBoolean(unary.operand()) && !isBoolean(rhs)) {
            auto kindStr = op == BinaryOperator::BinaryAnd ? "bitwise operator"sv : "comparison"sv;
            auto& diag = context.addDiag(diag::LogicalNotParentheses, unary.opRange);
            diag << kindStr << opRange;

            SourceRange range(unary.operand().sourceRange.start(), rhs.sourceRange.end());
            diag.addNote(diag::NoteLogicalNotFix, range) << kindStr;
            diag.addNote(diag::NoteLogicalNotSilence, lhs.sourceRange);
        }
    }

    // Warn about comparisons like `x < y < z` which doesn't compare the way you'd
    // mathematically expect.
    if (OpInfo::isRelational(op)) {
        if (auto binOp = getBin(lhs); binOp && OpInfo::isRelational(binOp->op))
            context.addDiag(diag::ConsecutiveComparison, opRange);
    }
}

Expression& BinaryExpression::fromComponents(Expression& lhs, Expression& rhs, BinaryOperator op,
                                             SourceRange opRange, SourceRange sourceRange,
                                             const ASTContext& context) {
    auto& compilation = context.getCompilation();
    const Type* lt = lhs.type;
    const Type* rt = rhs.type;

    auto result = compilation.emplace<BinaryExpression>(op, *lt, lhs, rhs, sourceRange, opRange);
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
        return OpInfo::binaryType(compilation, forceType, forceType, true);
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
            result->type = OpInfo::binaryType(compilation, lt, rt, false);
            break;
        case BinaryOperator::Divide:
            // Result is forced to 4-state because result can be X.
            good = bothNumeric;
            result->type = OpInfo::binaryType(compilation, lt, rt, true);
            break;
        case BinaryOperator::Mod:
            // Result is forced to 4-state because result can be X.
            // Different from divide because only integers are allowed.
            good = bothIntegral;
            result->type = OpInfo::binaryType(compilation, lt, rt, true);
            break;
        case BinaryOperator::BinaryAnd:
        case BinaryOperator::BinaryOr:
        case BinaryOperator::BinaryXor:
        case BinaryOperator::BinaryXnor:
            good = bothIntegral;
            result->type = OpInfo::binaryType(compilation, lt, rt, false);
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
                result->type = OpInfo::binaryType(compilation, lt, rt, false);
                contextDetermined(context, result->right_, result, *result->type, opRange);
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
                                             : OpInfo::binaryType(compilation, lt, rt, false);
            contextDetermined(context, result->left_, result, *nt, opRange);
            contextDetermined(context, result->right_, result, *nt, opRange);
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
            if (good) {
                // Call this just to get warnings about boolean conversions.
                context.requireBooleanConvertible(*result->left_);
                context.requireBooleanConvertible(*result->right_);
            }
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
                auto nt = OpInfo::binaryType(compilation, lt, rt, false);
                contextDetermined(context, result->left_, result, *nt, opRange);
                contextDetermined(context, result->right_, result, *nt, opRange);
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
                    contextDetermined(context, result->left_, result, compilation.getStringType(),
                                      opRange);
                    contextDetermined(context, result->right_, result, compilation.getStringType(),
                                      opRange);
                }
                else if (lt->isAggregate() && lt->isEquivalent(*rt)) {
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
        auto& diag = context.addDiag(diag::BadBinaryExpression, opRange);
        diag << *lt << *rt;
        diag << lhs.sourceRange;
        diag << rhs.sourceRange;
        return badExpr(compilation, result);
    }

    analyzePrecedence(context, lhs, rhs, op, opRange);

    auto& clt = lt->getCanonicalType();
    auto& crt = rt->getCanonicalType();
    if (!clt.isMatching(crt)) {
        auto checkTypes = [&](DiagCode code, bool isComparison) {
            analyzeOpTypes(clt, crt, *lt, *rt, lhs, rhs, context, opRange, code, isComparison, {});
        };

        switch (op) {
            case BinaryOperator::Add:
            case BinaryOperator::Subtract:
            case BinaryOperator::Multiply:
            case BinaryOperator::Divide:
            case BinaryOperator::Mod:
                checkTypes(diag::ArithOpMismatch, false);
                break;
            case BinaryOperator::BinaryAnd:
            case BinaryOperator::BinaryOr:
            case BinaryOperator::BinaryXor:
            case BinaryOperator::BinaryXnor:
                checkTypes(diag::BitwiseOpMismatch, false);
                break;
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
                checkTypes(diag::ComparisonMismatch, true);
                break;
            default:
                // Remaining operations have self determined
                // operands so the warning wouldn't make sense.
                break;
        }
    }

    return *result;
}

void BinaryExpression::analyzeOpTypes(const Type& clt, const Type& crt, const Type& originalLt,
                                      const Type& originalRt, const Expression& lhs,
                                      const Expression& rhs, const ASTContext& context,
                                      SourceRange opRange, DiagCode code, bool isComparison,
                                      std::optional<std::string_view> extraDiagArg) {
    // Don't warn if either side is a compiler generated variable
    // (which can be true for genvars).
    auto isCompGenVar = [](const Symbol* sym) {
        if (sym) {
            if (sym->kind == SymbolKind::Variable &&
                sym->as<VariableSymbol>().flags.has(VariableFlags::CompilerGenerated)) {
                return true;
            }

            if (sym->kind == SymbolKind::Parameter && sym->as<ParameterSymbol>().isFromGenvar()) {
                return true;
            }
        }
        return false;
    };

    auto lsym = lhs.getSymbolReference(), rsym = rhs.getSymbolReference();
    if (isCompGenVar(lsym) || isCompGenVar(rsym))
        return;

    // Don't warn if either side is an enum value symbol and the
    // other side is the base type of that enum.
    auto isEnumBaseCompare = [](const Symbol* sym, const Type& otherType) {
        if (sym && sym->kind == SymbolKind::EnumValue) {
            auto& ct = sym->as<EnumValueSymbol>().getType().getCanonicalType();
            if (ct.kind == SymbolKind::EnumType)
                return ct.as<EnumType>().baseType.isMatching(otherType);
        }
        return false;
    };

    if (isComparison && (isEnumBaseCompare(lsym, crt) || isEnumBaseCompare(rsym, clt)))
        return;

    if (clt.isSimpleBitVector() && crt.isSimpleBitVector()) {
        const bool sameSign = clt.isSigned() == crt.isSigned() ||
                              signMatches(lhs.getEffectiveSign(/* isForConversion */ false),
                                          rhs.getEffectiveSign(/* isForConversion */ false));

        if (isComparison) {
            // Comparisons of bit vectors should warn if the signs differ and
            // otherwise should not warn, otherwise you can get quite misleading
            // results like:
            //      logic [7:0] a, b;
            //      bit b = a + b < 257;
            // We don't want a warning for the comparison between logic[7:0] and
            // int because the addition will actually be promoted correctly and
            // everything will work as expected.
            if (sameSign)
                return;

            if ((clt.getBitWidth() == 8 && clt.isPredefinedInteger() && rhs.isImplicitString()) ||
                (crt.getBitWidth() == 8 && crt.isPredefinedInteger() && lhs.isImplicitString())) {
                // Don't warn if the comparison is between `byte` and a string literal.
                return;
            }

            auto& diag = context.addDiag(diag::SignCompare, opRange);
            SLANG_ASSERT(!extraDiagArg);
            diag << originalLt << originalRt;
            diag << lhs.sourceRange << rhs.sourceRange;
            return;
        }

        if (sameSign) {
            // If we have two integers of the same effective sign and size
            // (using the same ideas as in checkImplicitConversions) then we
            // should not warn.
            auto alw = clt.getBitWidth();
            auto arw = crt.getBitWidth();
            if (alw == arw)
                return;

            auto elw = lhs.getEffectiveWidth();
            auto erw = rhs.getEffectiveWidth();
            if (!elw || !erw)
                return;

            if (elw <= arw && alw >= erw)
                return;

            // If either side is a constant we'll assume the max allowed
            // width is actually unbounded.
            EvalContext evalCtx(context);
            if (lhs.eval(evalCtx))
                alw = SVInt::MAX_BITS;
            if (rhs.eval(evalCtx))
                arw = SVInt::MAX_BITS;

            if (elw <= arw && alw >= erw)
                return;
        }
    }
    else if (clt.isHandleType() && crt.isHandleType()) {
        // Ignore operations between handles (like comparing a class handle with null).
        return;
    }
    else if (clt.isNumeric() && crt.isNumeric()) {
        // If either side is a constant we might want to avoid warning.
        // The cases that I think make sense are:
        // - comparing any numeric value against the constant 0
        // - any floating value operator alongside an integer constant
        EvalContext evalCtx(context);
        auto lcv = lhs.eval(evalCtx);
        auto rcv = rhs.eval(evalCtx);
        if (lcv || rcv) {
            if (clt.isFloating() && crt.isIntegral() && rcv)
                return;
            if (crt.isFloating() && clt.isIntegral() && lcv)
                return;

            if (isComparison) {
                if (lcv.isInteger() && bool(lcv.integer() == 0))
                    return;
                if (rcv.isInteger() && bool(rcv.integer() == 0))
                    return;
            }
        }
    }
    else if ((clt.isString() && rhs.isImplicitString()) ||
             (crt.isString() && lhs.isImplicitString())) {
        // Ignore operations between strings and string literals.
        return;
    }

    auto& diag = context.addDiag(code, opRange);
    if (extraDiagArg)
        diag << *extraDiagArg;
    diag << originalLt << originalRt;
    diag << lhs.sourceRange << rhs.sourceRange;
}

bool BinaryExpression::propagateType(const ASTContext& context, const Type& newType,
                                     SourceRange propRange, ConversionKind) {
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
            contextDetermined(context, left_, this, newType, propRange);
            contextDetermined(context, right_, this, newType, propRange);
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
            contextDetermined(context, left_, this, newType, propRange);
            if (op == BinaryOperator::ArithmeticShiftRight && !type->isSigned())
                context.addDiag(diag::UnsignedArithShift, left_->sourceRange) << *type;
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
            return 1;
        case BinaryOperator::LogicalShiftLeft:
        case BinaryOperator::LogicalShiftRight:
        case BinaryOperator::ArithmeticShiftLeft:
        case BinaryOperator::ArithmeticShiftRight:
        case BinaryOperator::Power:
            return left().getEffectiveWidth();
    }
    SLANG_UNREACHABLE;
}

Expression::EffectiveSign BinaryExpression::getEffectiveSignImpl(bool isForConversion) const {
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
            return conjunction(left().getEffectiveSign(isForConversion),
                               right().getEffectiveSign(isForConversion));
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
            return EffectiveSign::Either;
        case BinaryOperator::LogicalShiftLeft:
        case BinaryOperator::LogicalShiftRight:
        case BinaryOperator::ArithmeticShiftLeft:
        case BinaryOperator::ArithmeticShiftRight:
        case BinaryOperator::Power:
            return left().getEffectiveSign(isForConversion);
    }
    SLANG_UNREACHABLE;
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
    if (OpInfo::isShortCircuit(op)) {
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

    return OpInfo::eval(op, cvl, cvr);
}

void BinaryExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("op", toString(op));
    serializer.write("left", left());
    serializer.write("right", right());
}

static const Pattern* createPattern(Compilation& comp, ASTContext& context,
                                    const PatternSyntax& syntax, const Type& targetType) {

    SmallVector<const PatternVarSymbol*> vars;
    if (!Pattern::createPatternVars(context, syntax, targetType, vars))
        return comp.emplace<InvalidPattern>(nullptr);

    SmallMap<std::string_view, const Symbol*, 4> varMap;
    for (auto var : vars) {
        if (!var->name.empty()) {
            auto [it, inserted] = varMap.emplace(var->name, var);
            if (!inserted) {
                auto& diag = context.addDiag(diag::Redefinition, var->location);
                diag << var->name;
                diag.addNote(diag::NoteDeclarationHere, it->second->location);
                continue;
            }

            // We just created this pattern var so the const_cast is safe.
            const_cast<PatternVarSymbol*>(var)->nextTemp = std::exchange(context.firstTempVar, var);

            // We need to force resolution here because the pattern variable doesn't
            // live in a scope and so later attempts at touching it could cause normal
            // resolution logic to fail.
            var->getDeclaredType()->forceResolveAt(context);
        }
    }

    return &Pattern::bind(context, syntax, targetType);
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
            pattern = createPattern(comp, trueContext, *condSyntax->matchesClause->pattern,
                                    *cond.type);
            bad |= pattern->bad();

            // We don't consider the condition to be const if there's a pattern.
            isConst = false;
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
    const Type* resultType = OpInfo::binaryType(comp, lt, rt, isFourState);
    auto result = comp.emplace<ConditionalExpression>(*resultType, conditions.copy(comp),
                                                      syntax.question.location(), left, right,
                                                      syntax.sourceRange(), isConst, isTrue);
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
        else if (lt->isEquivalent(*rt)) {
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

    // Warn about cases where a conditional expression and a binary operator
    // are mixed in a way that suggests the user mixed up the precedence order.
    // ex: `a + b ? 1 : 2`
    if (conditions.size() == 1 && !conditions[0].pattern) {
        if (auto binOp = conditions[0].expr->as_if<BinaryExpression>();
            binOp && !binOp->isParenthesized()) {
            if (OpInfo::isArithmetic(binOp->op) || OpInfo::isShift(binOp->op)) {
                auto opStr = OpInfo::getText(binOp->op);
                auto& diag = context.addDiag(diag::ConditionalPrecedence,
                                             syntax.question.location());
                diag << opStr << opStr << binOp->sourceRange;

                SourceRange range(binOp->right().sourceRange.start(), right.sourceRange.end());
                diag.addNote(diag::NoteConditionalPrecedenceFix, range);
                diag.addNote(diag::NotePrecedenceSilence, binOp->sourceRange) << opStr;
            }
        }
    }

    context.setAttributes(*result, syntax.attributes);
    return *result;
}

bool ConditionalExpression::propagateType(const ASTContext& context, const Type& newType,
                                          SourceRange opRange, ConversionKind conversionKind) {
    const bool parentTypeEquiv = type->isEquivalent(newType);
    type = &newType;

    bitmask<ASTFlags> leftFlags = ASTFlags::None;
    bitmask<ASTFlags> rightFlags = ASTFlags::None;
    if (isConst) {
        if (isTrue)
            rightFlags = ASTFlags::UnevaluatedBranch;
        else
            leftFlags = ASTFlags::UnevaluatedBranch;
    }

    auto handleBranch = [&](Expression*& expr, bitmask<ASTFlags> flags,
                            std::optional<bitwidth_t> otherEffectiveWidth) {
        // This is a propagated conversion but we'd like to see width-expand
        // warnings anyway so we'll manually do the check conversion check here.
        if (!flags.has(ASTFlags::UnevaluatedBranch) &&
            conversionKind <= ConversionKind::Propagated) {
            // If the parent type was already equivalent to what's being propagated,
            // then the only conversions we might be doing are "self induced", in the
            // sense that one branch is propagating its type to the other side.
            // We want to avoid warning in those cases where we have a literal
            // expression with a smaller effective type, like for example:
            //   bit a, b, c;
            //   c = a ? b : 0; // 32-bit literal 0 shouldn't cause a warning
            if (!parentTypeEquiv || !newType.isNumeric() || !expr->type->isNumeric() ||
                !otherEffectiveWidth || expr->type->getBitWidth() < otherEffectiveWidth) {
                ConversionExpression::checkImplicitConversions(context, *expr->type, newType, *expr,
                                                               this, opRange,
                                                               ConversionKind::Implicit);
            }
        }

        contextDetermined(context.resetFlags(flags), expr, this, newType, opRange);
    };

    auto leftEffectiveWidth = left().getEffectiveWidth();
    auto rightEffectiveWidth = right().getEffectiveWidth();
    handleBranch(left_, leftFlags, rightEffectiveWidth);
    handleBranch(right_, rightFlags, leftEffectiveWidth);

    // The predicate is self determined so no need to handle it here.
    return true;
}

std::optional<bitwidth_t> ConditionalExpression::getEffectiveWidthImpl() const {
    if (auto branch = knownSide())
        return branch->getEffectiveWidth();
    return std::max(left().getEffectiveWidth(), right().getEffectiveWidth());
}

Expression::EffectiveSign ConditionalExpression::getEffectiveSignImpl(bool isForConversion) const {
    if (auto branch = knownSide())
        return branch->getEffectiveSign(isForConversion);
    return conjunction(left().getEffectiveSign(isForConversion),
                       right().getEffectiveSign(isForConversion));
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
                ConstantValue comp = OpInfo::eval(BinaryOperator::Equality, la[i], ra[i]);
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
                                   /* allowValueRange */ true, *syntax.expr, expressions, bound);

    auto boundSpan = bound.copy(compilation);
    auto result = compilation.emplace<InsideExpression>(compilation.getLogicType(), *boundSpan[0],
                                                        boundSpan.subspan(1), syntax.sourceRange());
    if (bad)
        return badExpr(compilation, result);

    // Warn about `!x inside {y, z}` where they probably meant `!(x inside {y, z})`
    auto& lhs = boundSpan[0]->unwrapImplicitConversions();
    if (lhs.kind == ExpressionKind::UnaryOp && !lhs.isParenthesized() &&
        lhs.as<UnaryExpression>().op == UnaryOperator::LogicalNot) {

        auto& unary = lhs.as<UnaryExpression>();
        auto kindStr = "'inside' expression"sv;
        auto& diag = context.addDiag(diag::LogicalNotParentheses, unary.opRange);
        diag << kindStr << syntax.inside.range();

        SourceRange range(unary.operand().sourceRange.start(), result->sourceRange.end());
        diag.addNote(diag::NoteLogicalNotFix, range) << kindStr;
        diag.addNote(diag::NoteLogicalNotSilence, lhs.sourceRange);
    }

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
        if (elem->kind == ExpressionKind::ValueRange) {
            ConstantValue cvr = elem->as<ValueRangeExpression>().checkInside(context, cvl);
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

        bool bad = false;
        bool anyDynamic = false;
        size_t totalElems = 0;
        const Type& type = *assignmentTarget;
        const Type& elemType = *type.getArrayElementType();
        const bool isVirtualIface = elemType.isVirtualInterface();
        SmallVector<Expression*> buffer;

        for (auto argSyntax : syntax.expressions) {
            Expression* arg = nullptr;
            if (isVirtualIface) {
                arg = tryBindInterfaceRef(context, *argSyntax,
                                          /* isInterfacePort */ false);
            }

            if (!arg)
                arg = &create(compilation, *argSyntax, context);

            if (arg->bad()) {
                bad = true;
                continue;
            }

            if (arg->isImplicitlyAssignableTo(compilation, elemType)) {
                buffer.push_back(&convertAssignment(context, elemType, *arg, arg->sourceRange));
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
                                                               nullptr, {});
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
        if (!assignmentTarget || !assignmentTarget->isError())
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

    return LValue(std::move(lvals), LValue::Concat::Packed);
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
    EvalContext evalCtx(context, EvalFlags::CacheResults);
    if (ConstantValue leftVal = left.eval(evalCtx); !leftVal) {
        if (!right->isImplicitString()) {
            // They probably meant for this to be a constant (non-string) replication,
            // so do the normal error reporting for that case.
            evalCtx.reportAllDiags();
            return badExpr(compilation, result);
        }

        contextDetermined(context, right, result, compilation.getStringType(), {});

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
    const ASTContext& context) {

    const bool isDestination = context.flags.has(ASTFlags::LValue);
    const bool isRightToLeft = syntax.operatorToken.kind == TokenKind::LeftShift;
    uint64_t sliceSize = 0;

    auto badResult = [&]() -> Expression& {
        return badExpr(comp, comp.emplace<StreamingConcatenationExpression>(
                                 comp.getErrorType(), sliceSize, 0u,
                                 std::span<const StreamExpression>(), syntax.sourceRange()));
    };

    if (!context.flags.has(ASTFlags::StreamingAllowed) &&
        (isDestination || !comp.hasFlag(CompilationFlags::AllowSelfDeterminedStreamConcat))) {
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
            sliceSize = sliceExpr.type->getBitstreamWidth();
        }
        else {
            // It shall be an error for the value to be zero or negative.
            std::optional<int32_t> count = context.evalInteger(sliceExpr);
            if (!context.requireGtZero(count, sliceExpr.sourceRange))
                return badResult();
            sliceSize = static_cast<uint32_t>(*count);
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

    uint64_t bitstreamWidth = 0;
    SmallVector<StreamExpression, 4> buffer;
    for (const auto argSyntax : syntax.expressions) {
        auto& arg = selfDetermined(comp, *argSyntax->expression, context,
                                   ASTFlags::StreamingAllowed);
        if (arg.bad())
            return badResult();

        const Type* argType = arg.type;
        const Expression* withExpr = nullptr;
        std::optional<bitwidth_t> constantWithWidth;
        if (argSyntax->withRange) {
            // The expression before the with can be any one-dimensional unpacked array
            // (including a queue).
            if (!argType->isUnpackedArray() || argType->isAssociativeArray() ||
                !argType->getArrayElementType()->isFixedSize()) {
                context.addDiag(diag::BadStreamWithType, arg.sourceRange);
                return badResult();
            }

            withExpr = &bindSelector(comp, arg, *argSyntax->withRange->range,
                                     context.resetFlags(ASTFlags::StreamingWithRange));
            if (withExpr->bad())
                return badResult();

            // Try to get the bounds of the selection, if they are constant.
            // If they are constant, we've already done bounds checking and
            // max size checking on them.
            EvalContext evalCtx(context);
            auto range = withExpr->evalSelector(evalCtx, /* enforceBounds */ false);
            if (range)
                constantWithWidth = range->width();
        }

        if (argSyntax->expression->kind != SyntaxKind::StreamingConcatenationExpression) {
            // Unpacked unions get "unwrapped" to their first member when streaming.
            if (argType->isUnpackedUnion() && !argType->isTaggedUnion()) {
                auto& uu = argType->getCanonicalType().as<UnpackedUnionType>();
                auto members = uu.members();
                if (members.begin() != members.end())
                    argType = &members.begin()->as<ValueSymbol>().getType();
            }

            if (!argType->isBitstreamType(isDestination)) {
                context.addDiag(diag::BadStreamExprType, arg.sourceRange) << *arg.type;
                return badResult();
            }

            if (!Bitstream::checkClassAccess(*argType, context, arg.sourceRange))
                return badResult();
        }

        uint64_t argWidth = 0;
        if (arg.kind == ExpressionKind::Streaming) {
            argWidth = arg.as<StreamingConcatenationExpression>().getBitstreamWidth();
        }
        else if (withExpr) {
            if (constantWithWidth) {
                auto rangeBits = checkedMulU64(argType->getArrayElementType()->getBitstreamWidth(),
                                               *constantWithWidth);
                if (!rangeBits || rangeBits > Type::MaxBitWidth) {
                    context.addDiag(diag::ObjectTooLarge, withExpr->sourceRange);
                    return badResult();
                }

                argWidth = *rangeBits;
            }
        }
        else {
            argWidth = argType->getBitstreamWidth();
        }

        bitstreamWidth += argWidth;
        if (bitstreamWidth > Type::MaxBitWidth) {
            context.addDiag(diag::ObjectTooLarge, syntax.sourceRange());
            return badResult();
        }

        buffer.push_back({&arg, withExpr, constantWithWidth});
    }

    // So normally the type of a streaming concatenation is never inspected,
    // since it can only be used in assignments and there is explicit handling
    // of these expressions there. We use a void type for the result to represent
    // this (also because otherwise what type can we use for e.g. non fixed-size
    // streams). However, in VCS compat mode the error about requiring an assignment
    // context can be silenced, so we need to come up with a real result type here,
    // which we do by converting to a packed bit vector of bitstream width.
    auto& result = *comp.emplace<StreamingConcatenationExpression>(
        comp.getVoidType(), sliceSize, bitstreamWidth, buffer.ccopy(comp), syntax.sourceRange());

    if (!context.flags.has(ASTFlags::StreamingAllowed)) {
        // Cap the width so we don't overflow. The conversion will error for us
        // since the target width will be less than the source width.
        auto width = std::min(bitstreamWidth, (uint64_t)SVInt::MAX_BITS);
        auto& type = comp.getType(bitwidth_t(width), IntegralFlags::FourState);
        return convertAssignment(context, type, result, result.sourceRange);
    }

    return result;
}

ConstantValue StreamingConcatenationExpression::evalImpl(EvalContext& context) const {
    std::vector<ConstantValue> values;
    values.reserve(streams().size());
    for (auto& stream : streams()) {
        auto cv = stream.operand->eval(context);
        if (!cv)
            return nullptr;

        if (stream.withExpr) {
            auto range = stream.withExpr->evalSelector(context, /* enforceBounds */ false);
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

Expression& ValueRangeExpression::fromSyntax(Compilation& comp,
                                             const ValueRangeExpressionSyntax& syntax,
                                             const ASTContext& context) {
    ValueRangeKind rangeKind;
    switch (syntax.op.kind) {
        case TokenKind::PlusDivMinus:
            rangeKind = ValueRangeKind::AbsoluteTolerance;
            break;
        case TokenKind::PlusModMinus:
            rangeKind = ValueRangeKind::RelativeTolerance;
            break;
        default:
            rangeKind = ValueRangeKind::Simple;
            break;
    }

    // Unbounded literals are allowed if we are not a tolerance range.
    const auto flags = rangeKind == ValueRangeKind::Simple ? ASTFlags::AllowUnboundedLiteral
                                                           : ASTFlags::None;
    auto& left = create(comp, *syntax.left, context, flags);
    auto& right = create(comp, *syntax.right, context, flags);
    auto result = comp.emplace<ValueRangeExpression>(comp.getVoidType(), rangeKind, left, right,
                                                     syntax.sourceRange());
    if (left.bad() || right.bad())
        return badExpr(comp, result);

    auto lt = left.type;
    auto rt = right.type;

    if (rangeKind == ValueRangeKind::Simple) {
        if (lt->isUnbounded()) {
            lt = &comp.getIntType();
            if (rt->isUnbounded())
                context.addDiag(diag::ValueRangeUnbounded, result->sourceRange);
        }

        if (rt->isUnbounded())
            rt = &comp.getIntType();

        if (!(lt->isNumeric() && rt->isNumeric()) &&
            !(left.isImplicitString() && right.isImplicitString())) {
            auto& diag = context.addDiag(diag::BadValueRange, syntax.op.location());
            diag << left.sourceRange << right.sourceRange << *lt << *rt;
            return badExpr(comp, result);
        }

        auto cvl = context.tryEval(left);
        auto cvr = context.tryEval(right);
        if (cvl.isInteger() && cvr.isInteger() && bool(cvl.integer() > cvr.integer()))
            context.addDiag(diag::ReversedValueRange, result->sourceRange);
    }
    else {
        if (!lt->isNumeric() || !rt->isNumeric()) {
            auto& diag = context.addDiag(diag::BadValueRange, syntax.op.location());
            diag << left.sourceRange << right.sourceRange << *lt << *rt;
            return badExpr(comp, result);
        }

        selfDetermined(context, result->right_);
    }

    return *result;
}

bool ValueRangeExpression::propagateType(const ASTContext& context, const Type& newType,
                                         SourceRange opRange, ConversionKind) {
    contextDetermined(context, left_, this, newType, opRange);
    if (rangeKind == ValueRangeKind::Simple)
        contextDetermined(context, right_, this, newType, opRange);
    return true;
}

ConstantValue ValueRangeExpression::evalImpl(EvalContext&) const {
    // Should never enter this expecting a real result.
    return nullptr;
}

ConstantValue ValueRangeExpression::checkInside(EvalContext& context,
                                                const ConstantValue& val) const {
    ConstantValue cvl = left().eval(context);
    ConstantValue cvr = right().eval(context);
    if (!cvl || !cvr)
        return nullptr;

    auto convert = [&](const Type& from, const Type& to, SourceRange range, ConstantValue&& cv) {
        return ConversionExpression::convert(context, from, to, range, std::move(cv),
                                             ConversionKind::Propagated);
    };

    if (rangeKind != ValueRangeKind::Simple) {
        auto& comp = context.getCompilation();
        if (rangeKind == ValueRangeKind::RelativeTolerance) {
            // Convert both sides to the common type so we can scale them together.
            auto l = cvl;
            auto& lt = *left().type;
            auto common = OpInfo::binaryType(comp, &lt, right().type, false);
            l = convert(lt, *common, left().sourceRange, std::move(l));
            cvr = convert(*right().type, *common, right().sourceRange, std::move(cvr));

            // Final equation looks like:
            // cvr = left'(common'(cvl) * common'(cvr) / 100.0);
            cvr = OpInfo::eval(BinaryOperator::Multiply, l, cvr).convertToReal();
            cvr = OpInfo::eval(BinaryOperator::Divide, cvr, real_t(100.0));

            // Special case for the conversion: LRM says that real -> int truncates
            // instead of rounding unlike every other case in the language. shrug?
            if (lt.isIntegral()) {
                cvr = SVInt::fromDouble(lt.getBitWidth(), cvr.real(), lt.isSigned(),
                                        /* round */ false);
            }
            else {
                cvr = convert(comp.getRealType(), lt, right().sourceRange, std::move(cvr));
            }
        }
        else {
            // Convert the rhs to the lhs type.
            cvr = convert(*right().type, *left().type, right().sourceRange, std::move(cvr));
        }

        // Form the range, [A - B : A + B], swapping A and B if needed
        // to form a non-empty range.
        auto lower = OpInfo::eval(BinaryOperator::Subtract, cvl, cvr);
        auto upper = OpInfo::eval(BinaryOperator::Add, cvl, cvr);
        if (OpInfo::eval(BinaryOperator::LessThan, upper, lower).isTrue()) {
            cvl = std::move(upper);
            cvr = std::move(lower);
        }
        else {
            cvl = std::move(lower);
            cvr = std::move(upper);
        }
    }

    // If a side is unbounded, that comparison is just always true.
    if (cvl.isUnbounded())
        cvl = SVInt(1);
    else
        cvl = OpInfo::eval(BinaryOperator::GreaterThanEqual, val, cvl);

    if (cvr.isUnbounded())
        cvr = SVInt(1);
    else
        cvr = OpInfo::eval(BinaryOperator::LessThanEqual, val, cvr);

    return OpInfo::eval(BinaryOperator::LogicalAnd, cvl, cvr);
}

void ValueRangeExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("left", left());
    serializer.write("right", right());
    serializer.write("rangeKind", toString(rangeKind));
}

} // namespace slang::ast
