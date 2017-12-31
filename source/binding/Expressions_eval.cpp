//------------------------------------------------------------------------------
// Expressions_eval.cpp
// Constant expression evaluation.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Expressions.h"

#include "binding/Statements.h"

namespace slang {

bool Expression::evalBool(EvalContext& context) const {
    ConstantValue result = eval(context);
    if (!result.isInteger())
        return false;

    return (bool)(logic_t)result.integer();
}

ConstantValue Expression::eval(EvalContext& context) const {
    switch (kind) {
        case ExpressionKind::Invalid: return nullptr;
        case ExpressionKind::IntegerLiteral: return as<IntegerLiteral>().eval(context);
        case ExpressionKind::RealLiteral: return as<RealLiteral>().eval(context);
        case ExpressionKind::UnbasedUnsizedIntegerLiteral: return as<UnbasedUnsizedIntegerLiteral>().eval(context);
        case ExpressionKind::VariableRef: return as<VariableRefExpression>().eval(context);
        case ExpressionKind::ParameterRef: return as<ParameterRefExpression>().eval(context);
        case ExpressionKind::UnaryOp: return as<UnaryExpression>().eval(context);
        case ExpressionKind::BinaryOp: return as<BinaryExpression>().eval(context);
        case ExpressionKind::ConditionalOp: return as<ConditionalExpression>().eval(context);
        case ExpressionKind::Select: return as<SelectExpression>().eval(context);
        case ExpressionKind::Concatenation: return as<ConcatenationExpression>().eval(context);
        case ExpressionKind::Call: return as<CallExpression>().eval(context);
        case ExpressionKind::Conversion: return as<ConversionExpression>().eval(context);
    }
    THROW_UNREACHABLE;
}

ConstantValue IntegerLiteral::eval(EvalContext&) const {
    uint16_t width = (uint16_t)type->getBitWidth();
    SVInt result = getValue();

    // TODO: truncation?
    if (width > result.getBitWidth())
        result = extend(result, width, type->as<IntegralType>().isSigned);
    return result;
}

ConstantValue RealLiteral::eval(EvalContext&) const {
    return value;
}

ConstantValue UnbasedUnsizedIntegerLiteral::eval(EvalContext&) const {
    uint16_t width = (uint16_t)type->getBitWidth();
    bool isSigned = type->as<IntegralType>().isSigned;

    switch (value.value) {
        case 0: return SVInt(width, 0, isSigned);
        case 1: {
            SVInt tmp(width, 0, isSigned);
            tmp.setAllOnes();
            return tmp;
        }
        case logic_t::X_VALUE: return SVInt::createFillX(width, isSigned);
        case logic_t::Z_VALUE: return SVInt::createFillZ(width, isSigned);
        default: THROW_UNREACHABLE;
    }
}

ConstantValue VariableRefExpression::eval(EvalContext& context) const {
    ConstantValue* v = context.findLocal(&symbol);
    ASSERT(v);
    return *v;
}

ConstantValue ParameterRefExpression::eval(EvalContext&) const {
    return symbol.getValue();
}

ConstantValue UnaryExpression::eval(EvalContext& context) const {
    SVInt v = operand().eval(context).integer();

#define OP(k, v) case UnaryOperator::k: return v;
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
    }
    THROW_UNREACHABLE;
#undef OP
}

ConstantValue BinaryExpression::eval(EvalContext& context) const {
    SVInt l = left().eval(context).integer();
    SVInt r = right().eval(context).integer();

    // TODO: more robust lvalue handling
    ConstantValue* lvalue = nullptr;
    if (isAssignment())
        lvalue = context.findLocal(&((const VariableRefExpression&)left()).symbol);

#define OP(k, v) case BinaryOperator::k: return v
#define ASSIGN(k, v) case BinaryOperator::k: ASSERT(lvalue); *lvalue = v; return *lvalue
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
        OP(WildcardEquality, SVInt(wildcardEqual(l, r)));
        OP(WildcardInequality, SVInt(!wildcardEqual(l, r)));
        OP(GreaterThanEqual, SVInt(l >= r));
        OP(GreaterThan, SVInt(l > r));
        OP(LessThanEqual, SVInt(l <= r));
        OP(LessThan, SVInt(l < r));
        OP(LogicalAnd, SVInt(l && r));
        OP(LogicalOr, SVInt(l || r));
        OP(LogicalImplication, SVInt(SVInt::logicalImplication(l, r)));
        OP(LogicalEquivalence, SVInt(SVInt::logicalEquivalence(l, r)));
        OP(Power, l.pow(r));
        OP(Replication, r.replicate(l));
        ASSIGN(Assignment, r);
        ASSIGN(AddAssignment, l + r);
        ASSIGN(SubtractAssignment, l - r);
        ASSIGN(MultiplyAssignment, l * r);
        ASSIGN(DivideAssignment, l / r);
        ASSIGN(ModAssignment, l % r);
        ASSIGN(AndAssignment, l & r);
        ASSIGN(OrAssignment, l | r);
        ASSIGN(XorAssignment, l ^ r);
        ASSIGN(LogicalLeftShiftAssignment, l.shl(r));
        ASSIGN(LogicalRightShiftAssignment, l.lshr(r));
        ASSIGN(ArithmeticLeftShiftAssignment, l.shl(r));
        ASSIGN(ArithmeticRightShiftAssignment, l.ashr(r));
    }
    THROW_UNREACHABLE;
#undef OP
#undef ASSIGN
}

ConstantValue ConditionalExpression::eval(EvalContext& context) const {
    SVInt cond = pred().eval(context).integer();
    logic_t pred = (logic_t)cond;

    if (pred.isUnknown()) {
        // do strange combination operation
        SVInt l = left().eval(context).integer();
        SVInt r = right().eval(context).integer();
        return SVInt::conditional(cond, l, r);
    }
    else if (pred) {
        return left().eval(context);
    }
    else {
        return right().eval(context);
    }
}

ConstantValue SelectExpression::eval(EvalContext& context) const {
    SVInt value = expr().eval(context).integer();
    ConstantRange range = expr().type->as<IntegralType>().getBitVectorRange();

    SVInt msb = left().eval(context).integer();
    SVInt lsbOrWidth = right().eval(context).integer();

    if (msb.hasUnknown() || lsbOrWidth.hasUnknown()) {
        // If any part of an address is unknown, then the whole thing returns
        // 'x; let's handle this here so everywhere else we can assume the inputs
        // are normal numbers
        return SVInt::createFillX((uint16_t)type->getBitWidth(), false);
    }

    // SVInt uses little endian ranges starting from zero; we need to translate from the
    // actual range used in the declaration of the variable.
    int16_t actualMsb = int16_t(msb.as<int>().value() - range.lower());
    if (!range.isLittleEndian())
        actualMsb = int16_t(range.width() - (uint32_t)actualMsb - 1);

    switch (kind) {
        case SyntaxKind::BitSelect: {
            return value.bitSelect(actualMsb, actualMsb);
        }
        case SyntaxKind::SimpleRangeSelect: {
            int16_t actualLsb = int16_t(lsbOrWidth.as<int>().value() - range.lower());
            if (!range.isLittleEndian())
                actualLsb = int16_t(range.width() - (uint32_t)actualLsb - 1);

            return value.bitSelect(actualLsb, actualMsb);
        }
        case SyntaxKind::AscendingRangeSelect: {
            int16_t width = lsbOrWidth.as<int16_t>().value();
            return value.bitSelect(actualMsb, actualMsb + width);
        }
        case SyntaxKind::DescendingRangeSelect: {
            int16_t width = lsbOrWidth.as<int16_t>().value();
            return value.bitSelect(actualMsb - width, actualMsb);
        }
        default:
            THROW_UNREACHABLE;
    }
}

ConstantValue ConcatenationExpression::eval(EvalContext& context) const {
    SmallVectorSized<SVInt, 8> values;
    for (auto operand : operands())
        values.append(operand->eval(context).integer());

    // TODO: add support for other Nary Expressions, like stream concatenation
    //switch (expr.syntax.kind) {
    //  case SyntaxKind::ConcatenationExpression: return concatenate(values);
    //}

    return concatenate(values);
}

ConstantValue CallExpression::eval(EvalContext& context) const {
    // Evaluate all argument in the current stack frame.
    SmallVectorSized<ConstantValue, 8> args;
    for (auto arg : arguments())
        args.emplace(arg->eval(context));

    // If this is a system function we will just evaluate it directly
    if (subroutine.systemFunctionKind != SystemFunction::Unknown) {
        switch (subroutine.systemFunctionKind) {
            case SystemFunction::Unknown: break;
            case SystemFunction::clog2: return SVInt(clog2(args[0].integer()));
            case SystemFunction::bits:
            case SystemFunction::low:
            case SystemFunction::high:
            case SystemFunction::left:
            case SystemFunction::right:
            case SystemFunction::size:
            case SystemFunction::increment: {
                //TODO: add support for things other than integral types
                const auto& argType = arguments()[0]->type->as<IntegralType>();
                ConstantRange range = argType.getBitVectorRange();
                switch (subroutine.systemFunctionKind) {
                    case SystemFunction::bits:  return SVInt(argType.bitWidth);
                    case SystemFunction::low:   return SVInt(range.lower());
                    case SystemFunction::high:  return SVInt(range.upper());
                    case SystemFunction::left:  return SVInt(range.left);
                    case SystemFunction::right: return SVInt(range.right);
                    case SystemFunction::size:  return SVInt(argType.bitWidth);
                    case SystemFunction::increment: return SVInt(range.isLittleEndian() ? 1 : -1);
                    default: THROW_UNREACHABLE;
                }
                break;
            }
        }
    }

    // Push a new stack frame, push argument values as locals.
    context.pushFrame();
    span<const FormalArgumentSymbol* const> formals = subroutine.arguments;
    for (uint32_t i = 0; i < formals.size(); i++)
        context.createLocal(formals[i], args[i]);

    VariableSymbol callValue(subroutine.name, subroutine.location);
    callValue.type = subroutine.returnType;
    context.createLocal(&callValue, nullptr);

    subroutine.getBody()->eval(context);

    // Pop the frame and return the value
    return context.popFrame();
}

ConstantValue ConversionExpression::eval(EvalContext& context) const {
    ConstantValue value = operand().eval(context);
    switch (conversionKind) {
        case ConversionKind::IntExtension:
            ASSERT(value.isInteger() && value.integer().getBitWidth() == operand().type->getBitWidth());
            return extend(value.integer(), (uint16_t)type->getBitWidth(), type->as<IntegralType>().isSigned);

        default:
            THROW_UNREACHABLE;
    }
}

}