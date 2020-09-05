//------------------------------------------------------------------------------
// OperatorExpressions.cpp
// Definitions for operator expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/OperatorExpressions.h"

#include "slang/binding/AssignmentExpressions.h"
#include "slang/binding/LiteralExpressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/AllTypes.h"
#include "slang/syntax/AllSyntax.h"

namespace {

using namespace slang;

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
            THROW_UNREACHABLE;
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
            THROW_UNREACHABLE;
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

namespace slang {

const Type* Expression::binaryOperatorType(Compilation& compilation, const Type* lt, const Type* rt,
                                           bool forceFourState) {
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
        if ((lf & IntegralFlags::Signed) && (rf & IntegralFlags::Signed))
            flags |= IntegralFlags::Signed;
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

bool Expression::bindMembershipExpressions(const BindContext& context, TokenKind keyword,
                                           bool wildcard, bool unwrapUnpacked,
                                           const ExpressionSyntax& valueExpr,
                                           span<const ExpressionSyntax* const> expressions,
                                           SmallVector<const Expression*>& results) {
    Compilation& comp = context.scope.getCompilation();
    Expression& valueRes = create(comp, valueExpr, context);
    results.append(&valueRes);

    const Type* type = valueRes.type;
    bool bad = valueRes.bad();
    bool canBeStrings = valueRes.isImplicitString();

    if ((!wildcard && type->isAggregate()) || (wildcard && !type->isIntegral())) {
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
        Expression* bound = &create(comp, *expr, context);
        results.append(bound);
        bad |= bound->bad();
        if (bad)
            continue;

        if (canBeStrings && !bound->isImplicitString())
            canBeStrings = false;

        const Type* bt = bound->type;
        if (wildcard) {
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

        // Special handling for open range expressions -- they don't have
        // a real type on their own, we need to check their bounds.
        if (bound->kind == ExpressionKind::OpenRange) {
            auto& range = bound->as<OpenRangeExpression>();
            checkType(range.left(), *range.left().type);
            checkType(range.right(), *range.right().type);
            continue;
        }

        // If this is an "inside" operation, then unpacked arrays are unwrapped
        // into their element types before checking further.
        if (unwrapUnpacked) {
            while (bt->isUnpackedArray())
                bt = bt->getArrayElementType();
        }

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

        auto& checked = checkBindFlags(*expr, context);
        if (checked.bad())
            return false;

        results[index++] = &checked;
    }

    return true;
}

Expression& UnaryExpression::fromSyntax(Compilation& compilation,
                                        const PrefixUnaryExpressionSyntax& syntax,
                                        const BindContext& context) {
    Expression& operand = create(compilation, *syntax.operand, context);
    const Type* type = operand.type;

    auto result = compilation.emplace<UnaryExpression>(getUnaryOperator(syntax.kind), *type,
                                                       operand, syntax.sourceRange());
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
            result->type =
                type->isFourState() ? &compilation.getLogicType() : &compilation.getBitType();
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
            result->type =
                type->isFourState() ? &compilation.getLogicType() : &compilation.getBitType();
            selfDetermined(context, result->operand_);
            break;
        case SyntaxKind::UnaryPreincrementExpression:
        case SyntaxKind::UnaryPredecrementExpression:
            if ((context.flags & BindFlags::ProceduralStatement) == 0 &&
                (context.flags & BindFlags::AssignmentAllowed) == 0) {
                context.addDiag(diag::IncDecNotAllowed, syntax.sourceRange());
                return badExpr(compilation, result);
            }

            // Supported for both integral and real types. Result is same as input type.
            // The operand must also be an assignable lvalue.
            // TODO: detect and warn for multiple reads and writes of a single variable in an
            // expression
            good = type->isNumeric();
            result->type = type;
            if (!operand.verifyAssignable(context, /* isNonBlocking */ false,
                                          syntax.operatorToken.location())) {
                return badExpr(compilation, result);
            }
            break;
        default:
            THROW_UNREACHABLE;
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
                                        const BindContext& context) {
    Expression& operand = create(compilation, *syntax.operand, context);
    const Type* type = operand.type;

    // This method is only ever called for postincrement and postdecrement operators, so
    // the operand must be an lvalue.
    Expression* result = compilation.emplace<UnaryExpression>(getUnaryOperator(syntax.kind), *type,
                                                              operand, syntax.sourceRange());
    if (operand.bad() || !operand.verifyAssignable(context, /* isNonBlocking */ false,
                                                   syntax.operatorToken.location())) {
        return badExpr(compilation, result);
    }

    if ((context.flags & BindFlags::ProceduralStatement) == 0 &&
        (context.flags & BindFlags::AssignmentAllowed) == 0) {
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

bool UnaryExpression::propagateType(const BindContext& context, const Type& newType) {
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
    THROW_UNREACHABLE;
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

        THROW_UNREACHABLE;
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
    THROW_UNREACHABLE;
}

bool UnaryExpression::verifyConstantImpl(EvalContext& context) const {
    return operand().verifyConstant(context);
}

void UnaryExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("op", toString(op));
    serializer.write("operand", operand());
}

Expression& BinaryExpression::fromSyntax(Compilation& compilation,
                                         const BinaryExpressionSyntax& syntax,
                                         const BindContext& context) {
    Expression& lhs = create(compilation, *syntax.left, context);
    Expression& rhs = create(compilation, *syntax.right, context);
    const Type* lt = lhs.type;
    const Type* rt = rhs.type;

    auto result = compilation.emplace<BinaryExpression>(getBinaryOperator(syntax.kind), *lhs.type,
                                                        lhs, rhs, syntax.sourceRange());
    if (lhs.bad() || rhs.bad())
        return badExpr(compilation, result);

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
    switch (syntax.kind) {
        case SyntaxKind::AddExpression:
        case SyntaxKind::SubtractExpression:
        case SyntaxKind::MultiplyExpression:
            good = bothNumeric;
            result->type = binaryOperatorType(compilation, lt, rt, false);
            break;
        case SyntaxKind::DivideExpression:
            // Result is forced to 4-state because result can be X.
            good = bothNumeric;
            result->type = binaryOperatorType(compilation, lt, rt, true);
            break;
        case SyntaxKind::ModExpression:
            // Result is forced to 4-state because result can be X.
            // Different from divide because only integers are allowed.
            good = bothIntegral;
            result->type = binaryOperatorType(compilation, lt, rt, true);
            break;
        case SyntaxKind::BinaryAndExpression:
        case SyntaxKind::BinaryOrExpression:
        case SyntaxKind::BinaryXorExpression:
        case SyntaxKind::BinaryXnorExpression:
            good = bothIntegral;
            result->type = binaryOperatorType(compilation, lt, rt, false);
            break;
        case SyntaxKind::LogicalShiftLeftExpression:
        case SyntaxKind::LogicalShiftRightExpression:
        case SyntaxKind::ArithmeticShiftLeftExpression:
        case SyntaxKind::ArithmeticShiftRightExpression:
            // The result is always the same type as the lhs, except that if the rhs is
            // four state then the lhs also becomes four state.
            good = bothIntegral;
            if (rt->isFourState())
                result->type = forceFourState(compilation, lt);
            else
                result->type = lt;
            selfDetermined(context, result->right_);
            break;
        case SyntaxKind::PowerExpression:
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
        case SyntaxKind::GreaterThanEqualExpression:
        case SyntaxKind::GreaterThanExpression:
        case SyntaxKind::LessThanEqualExpression:
        case SyntaxKind::LessThanExpression: {
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
        case SyntaxKind::LogicalAndExpression:
        case SyntaxKind::LogicalOrExpression:
        case SyntaxKind::LogicalImplicationExpression:
        case SyntaxKind::LogicalEquivalenceExpression:
            // Result is always a single bit.
            good = bothNumeric;
            result->type = singleBitType(compilation, lt, rt);
            selfDetermined(context, result->left_);
            selfDetermined(context, result->right_);
            break;
        case SyntaxKind::EqualityExpression:
        case SyntaxKind::InequalityExpression:
        case SyntaxKind::WildcardEqualityExpression:
        case SyntaxKind::WildcardInequalityExpression:
        case SyntaxKind::CaseEqualityExpression:
        case SyntaxKind::CaseInequalityExpression:
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
                if (syntax.kind == SyntaxKind::EqualityExpression ||
                    syntax.kind == SyntaxKind::InequalityExpression) {
                    good = true;
                    result->type = singleBitType(compilation, lt, rt);
                }
                else if (syntax.kind == SyntaxKind::CaseEqualityExpression ||
                         syntax.kind == SyntaxKind::CaseInequalityExpression) {
                    good = true;
                    result->type = &compilation.getBitType();
                }
                else {
                    good = bothIntegral;
                    result->type =
                        lt->isFourState() ? &compilation.getLogicType() : &compilation.getBitType();
                }

                // Result type is fixed but the two operands affect each other as they would
                // in other context-determined operators.
                auto nt = binaryOperatorType(compilation, lt, rt, false);
                contextDetermined(context, result->left_, *nt);
                contextDetermined(context, result->right_, *nt);
            }
            else {
                bool isContext = false;
                bool isWildcard = syntax.kind == SyntaxKind::WildcardEqualityExpression ||
                                  syntax.kind == SyntaxKind::WildcardInequalityExpression;

                if (bothStrings) {
                    good = !isWildcard;
                    result->type = &compilation.getBitType();

                    // If there is a literal involved, make sure it's converted to string.
                    isContext = true;
                    contextDetermined(context, result->left_, compilation.getStringType());
                    contextDetermined(context, result->right_, compilation.getStringType());
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
            THROW_UNREACHABLE;
    }

    auto location = syntax.operatorToken.location();
    if (!good) {
        auto& diag = context.addDiag(diag::BadBinaryExpression, location);
        diag << *lt << *rt;
        diag << lhs.sourceRange;
        diag << rhs.sourceRange;
        return badExpr(compilation, result);
    }

    context.setAttributes(*result, syntax.attributes);
    return *result;
}

bool BinaryExpression::propagateType(const BindContext& context, const Type& newType) {
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
    THROW_UNREACHABLE;
}

ConstantValue BinaryExpression::evalImpl(EvalContext& context) const {
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
                THROW_UNREACHABLE;
        }
    }

    ConstantValue cvr = right().eval(context);
    if (!cvr)
        return nullptr;

    return evalBinaryOperator(op, cvl, cvr);
}

bool BinaryExpression::verifyConstantImpl(EvalContext& context) const {
    return left().verifyConstant(context) && right().verifyConstant(context);
}

void BinaryExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("op", toString(op));
    serializer.write("left", left());
    serializer.write("right", right());
}

Expression& ConditionalExpression::fromSyntax(Compilation& compilation,
                                              const ConditionalExpressionSyntax& syntax,
                                              const BindContext& context,
                                              const Type* assignmentTarget) {
    if (syntax.predicate->conditions.size() != 1) {
        context.addDiag(diag::NotYetSupported, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    auto& pred = selfDetermined(compilation, *syntax.predicate->conditions[0]->expr, context);

    // If the predicate is known at compile time, we can tell which branch will be unevaluated.
    BindFlags leftFlags = BindFlags::None;
    BindFlags rightFlags = BindFlags::None;
    ConstantValue predVal = context.tryEval(pred);
    if (predVal && (!predVal.isInteger() || !predVal.integer().hasUnknown())) {
        if (predVal.isTrue())
            rightFlags = BindFlags::UnevaluatedBranch;
        else
            leftFlags = BindFlags::UnevaluatedBranch;
    }

    auto& left = create(compilation, *syntax.left, context, leftFlags, assignmentTarget);
    auto& right = create(compilation, *syntax.right, context, rightFlags, assignmentTarget);

    // Force four-state return type for ambiguous condition case.
    const Type* resultType =
        binaryOperatorType(compilation, left.type, right.type, pred.type->isFourState());
    auto result = compilation.emplace<ConditionalExpression>(*resultType, pred, left, right,
                                                             syntax.sourceRange());
    if (pred.bad() || left.bad() || right.bad())
        return badExpr(compilation, result);

    if (!context.requireBooleanConvertible(pred))
        return badExpr(compilation, result);

    // If both sides of the expression are numeric, we've already determined the correct
    // result type. Otherwise, follow the rules in [11.14.11].
    bool good = true;
    const Type& lt = *left.type;
    const Type& rt = *right.type;
    if (!lt.isNumeric() || !rt.isNumeric()) {
        if (lt.isNull() && rt.isNull()) {
            result->type = &compilation.getNullType();
        }
        else if (lt.isClass() || rt.isClass()) {
            if (lt.isNull())
                result->type = &rt;
            else if (rt.isNull())
                result->type = &lt;
            else if (rt.isAssignmentCompatible(lt))
                result->type = &rt;
            else if (lt.isAssignmentCompatible(rt))
                result->type = &lt;
            // TODO: handle case for class types derived from common base
            else if (lt.isEquivalent(rt))
                result->type = &lt;
            else
                good = false;
        }
        else if (lt.isEquivalent(rt)) {
            result->type = &lt;
        }
        else if (left.isImplicitString() && right.isImplicitString()) {
            result->type = &compilation.getStringType();
        }
        else {
            good = false;
        }
    }

    if (!good) {
        auto& diag = context.addDiag(diag::BadConditionalExpression, syntax.question.location());
        diag << lt << rt;
        diag << left.sourceRange;
        diag << right.sourceRange;
        return badExpr(compilation, result);
    }

    context.setAttributes(*result, syntax.attributes);
    return *result;
}

bool ConditionalExpression::propagateType(const BindContext& context, const Type& newType) {
    // The predicate is self determined so no need to handle it here.
    type = &newType;
    contextDetermined(context, left_, newType);
    contextDetermined(context, right_, newType);
    return true;
}

ConstantValue ConditionalExpression::evalImpl(EvalContext& context) const {
    ConstantValue cp = pred().eval(context);
    if (!cp)
        return nullptr;

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
            span<const ConstantValue> la = cvl.elements();
            span<const ConstantValue> ra = cvr.elements();
            if (la.size() == ra.size()) {
                // TODO: what if this is an unpacked struct?
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

bool ConditionalExpression::verifyConstantImpl(EvalContext& context) const {
    return left().verifyConstant(context) && right().verifyConstant(context) &&
           pred().verifyConstant(context);
}

void ConditionalExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("pred", pred());
    serializer.write("left", left());
    serializer.write("right", right());
}

Expression& InsideExpression::fromSyntax(Compilation& compilation,
                                         const InsideExpressionSyntax& syntax,
                                         const BindContext& context) {
    SmallVectorSized<const ExpressionSyntax*, 8> expressions;
    for (auto elemSyntax : syntax.ranges->valueRanges)
        expressions.append(elemSyntax);

    SmallVectorSized<const Expression*, 8> bound;
    bool bad =
        !bindMembershipExpressions(context, TokenKind::InsideKeyword, /* wildcard */ false,
                                   /* unwrapUnpacked */ true, *syntax.expr, expressions, bound);

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

bool InsideExpression::verifyConstantImpl(EvalContext& context) const {
    if (!left().verifyConstant(context))
        return false;

    for (auto elem : rangeList()) {
        if (!elem->verifyConstant(context))
            return false;
    }

    return true;
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
                                                const BindContext& context,
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
        SmallVectorSized<Expression*, 8> buffer;

        for (auto argSyntax : syntax.expressions) {
            Expression* arg = &create(compilation, *argSyntax, context);
            if (arg->bad()) {
                bad = true;
                continue;
            }

            if (arg->isImplicitlyAssignableTo(elemType)) {
                buffer.append(&convertAssignment(context, elemType, *arg,
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
                buffer.append(arg);
                continue;
            }

            // Otherwise this is an error.
            // TODO: handle null values for classes
            bad = true;
            context.addDiag(diag::BadConcatExpression, arg->sourceRange) << argType;
            selfDetermined(context, arg);
            buffer.append(arg);
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
    bool anyStrings = false;
    bitmask<IntegralFlags> flags;
    bitwidth_t totalWidth = 0;
    SmallVectorSized<Expression*, 8> buffer;

    for (auto argSyntax : syntax.expressions) {
        // Replications inside of concatenations have a special feature that allows them to have
        // a width of zero. Check now if we're going to be binding a replication and if so set
        // an additional flag so that it knows it's ok to have that zero count.
        Expression* arg;
        if (argSyntax->kind == SyntaxKind::MultipleConcatenationExpression)
            arg = &create(compilation, *argSyntax, context, BindFlags::InsideConcatenation);
        else
            arg = &create(compilation, *argSyntax, context);
        buffer.append(arg);

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
            if (!anyStrings)
                selfDetermined(context, buffer[i]);
            else {
                Expression* expr = buffer[i];
                if (expr->type->isString())
                    selfDetermined(context, expr);
                else if (expr->isImplicitString())
                    contextDetermined(context, expr, compilation.getStringType());
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
        return badExpr(compilation, compilation.emplace<ConcatenationExpression>(
                                        compilation.getErrorType(), span<const Expression*>(),
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
                                               const BindContext& context,
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

    return *compilation.emplace<ConcatenationExpression>(
        *assignmentTarget, span<const Expression* const>{}, syntax.sourceRange());
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
                    ASSERT(cv.isContainer());
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
            if (!build(result))
                return nullptr;
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

    SmallVectorSized<SVInt, 8> values;
    for (auto operand : operands()) {
        ConstantValue v = operand->eval(context);
        if (!v)
            return nullptr;

        // Skip zero-width replication operands.
        if (operand->type->isVoid())
            continue;

        values.append(v.integer());
    }

    return SVInt::concat(values);
}

LValue ConcatenationExpression::evalLValueImpl(EvalContext& context) const {
    std::vector<LValue> lvals;
    for (auto operand : operands()) {
        LValue lval = operand->evalLValue(context);
        if (!lval)
            return nullptr;

        lvals.emplace_back(std::move(lval));
    }

    return LValue(std::move(lvals));
}

bool ConcatenationExpression::verifyConstantImpl(EvalContext& context) const {
    for (auto operand : operands()) {
        if (!operand->verifyConstant(context))
            return false;
    }
    return true;
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
                                              const BindContext& context) {
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

    optional<int32_t> count = context.evalInteger(left);
    if (!count)
        return badExpr(compilation, result);

    if (*count < 0) {
        context.requireGtZero(count, left.sourceRange);
        return badExpr(compilation, result);
    }

    if (*count == 0) {
        if ((context.flags & BindFlags::InsideConcatenation) == 0) {
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

    result->type = &compilation.getType(
        *width, right->type->isFourState() ? IntegralFlags::FourState : IntegralFlags::TwoState);
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
        optional<int32_t> optCount = c.integer().as<int32_t>();
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

bool ReplicationExpression::verifyConstantImpl(EvalContext& context) const {
    return count().verifyConstant(context) && concat().verifyConstant(context);
}

void ReplicationExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("count", count());
    serializer.write("concat", concat());
}

Expression& StreamingConcatenationExpression::fromSyntax(
    Compilation& compilation, const StreamingConcatenationExpressionSyntax& syntax,
    const BindContext& context, const Type* assignmentTarget) {
    const bool isRightToLeft = syntax.operatorToken.kind == TokenKind::LeftShift;
    std::size_t sliceSize = 0;

    auto badResult = [&]() {
        return compilation.emplace<StreamingConcatenationExpression>(
            compilation.getErrorType(), sliceSize, span<const Expression*>(), syntax.sourceRange());
    };

    if (!(context.flags & BindFlags::StreamingAllowed)) {
        context.addDiag(diag::BadStreamContext, syntax.operatorToken.location());
        return badExpr(compilation, badResult());
    }
    if (assignmentTarget && !assignmentTarget->isBitstreamType(true)) {
        context.addDiag(diag::BadStreamType, syntax.sourceRange())
            << std::string("target") << *assignmentTarget;
        return badExpr(compilation, badResult());
    }

    if (syntax.sliceSize) {
        if (isRightToLeft) {
            const auto& sliceExpr =
                bind(*syntax.sliceSize, context, BindFlags::AllowDataType | BindFlags::Constant);
            if (sliceExpr.bad())
                return badExpr(compilation, badResult());
            if (sliceExpr.kind == ExpressionKind::DataType) {
                if (!sliceExpr.type->isFixedSize()) {
                    auto& diag = context.addDiag(diag::BasStreamSlice, sliceExpr.sourceRange);
                    if (sliceExpr.type->location)
                        diag.addNote(diag::NoteDeclarationHere, sliceExpr.type->location);
                    return badExpr(compilation, badResult());
                }
                sliceSize = sliceExpr.type->bitstreamWidth();
            }
            else {
                optional<int32_t> count = context.evalInteger(sliceExpr);
                if (!count)
                    return badExpr(compilation, badResult());
                if (*count <= 0) {
                    context.requireGtZero(count, sliceExpr.sourceRange);
                    return badExpr(compilation, badResult());
                }
                sliceSize = static_cast<bitwidth_t>(*count);
            }
        }
        else
            context.addDiag(diag::IgnoredSlice, syntax.sliceSize->sourceRange());
    }
    else if (isRightToLeft)
        sliceSize = 1;

    SmallVectorSized<Expression*, 8> buffer;
    for (const auto argSyntax : syntax.expressions) {
        Expression* arg;
        if (assignmentTarget &&
            argSyntax->expression->kind == SyntaxKind::StreamingConcatenationExpression)
            arg = &create(compilation, *argSyntax->expression, context, BindFlags::StreamingAllowed,
                          assignmentTarget);
        else
            arg = &selfDetermined(compilation, *argSyntax->expression, context,
                                  BindFlags::StreamingAllowed);
        if (argSyntax->withRange)
            arg = &bindSelector(compilation, *arg, *argSyntax->withRange->range, context);

        if (arg->bad())
            return badExpr(compilation, badResult());
        if (argSyntax->expression->kind == SyntaxKind::StreamingConcatenationExpression)
            continue; // type has been checked

        const Type& type = *arg->type;
        // TODO: first-declared member of untagged union
        if (!type.isBitstreamType(!assignmentTarget)) {
            context.addDiag(diag::BadStreamType, arg->sourceRange)
                << std::string("expression") << type;
            return badExpr(compilation, badResult());
        }

        buffer.append(arg);
    }

    return *compilation.emplace<StreamingConcatenationExpression>(
        compilation.getIntegerType(), sliceSize, buffer.ccopy(compilation), syntax.sourceRange());
}

ConstantValue StreamingConcatenationExpression::evalImpl(EvalContext& /* context */) const {
    return nullptr;
}

bool StreamingConcatenationExpression::verifyConstantImpl(EvalContext& context) const {
    for (auto stream : streams()) {
        if (!stream->verifyConstant(context))
            return false;
    }
    return true;
}

void StreamingConcatenationExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("sliceSize", sliceSize);
    if (!streams().empty()) {
        serializer.startArray("streams");
        for (auto op : streams())
            serializer.serialize(*op);
        serializer.endArray();
    }
}

Expression& OpenRangeExpression::fromSyntax(Compilation& comp,
                                            const OpenRangeExpressionSyntax& syntax,
                                            const BindContext& context) {
    Expression& left = create(comp, *syntax.left, context);
    Expression& right = create(comp, *syntax.right, context);

    auto result =
        comp.emplace<OpenRangeExpression>(comp.getVoidType(), left, right, syntax.sourceRange());
    if (left.bad() || right.bad())
        return badExpr(comp, result);

    if (!(left.type->isNumeric() && right.type->isNumeric()) &&
        !(left.isImplicitString() && right.isImplicitString())) {
        auto& diag = context.addDiag(diag::BadOpenRange, syntax.colon.location());
        diag << left.sourceRange << right.sourceRange << *left.type << *right.type;
        return badExpr(comp, result);
    }

    return *result;
}

bool OpenRangeExpression::propagateType(const BindContext& context, const Type& newType) {
    contextDetermined(context, left_, newType);
    contextDetermined(context, right_, newType);
    return true;
}

ConstantValue OpenRangeExpression::evalImpl(EvalContext&) const {
    // Should never enter this expecting a real result.
    return nullptr;
}

bool OpenRangeExpression::verifyConstantImpl(EvalContext& context) const {
    return left().verifyConstant(context) && right().verifyConstant(context);
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
            THROW_UNREACHABLE;
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
            THROW_UNREACHABLE;
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
                THROW_UNREACHABLE;
        }
    }

#undef OP
    THROW_UNREACHABLE;
}

} // namespace slang
