//------------------------------------------------------------------------------
// Expressions_eval.cpp
// Constant expression evaluation.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Expressions.h"

#include "binding/Statements.h"
#include "symbols/ASTVisitor.h"

namespace {

using namespace slang;

struct EvalVisitor {
    template<typename T>
    ConstantValue visit(const T& expr, EvalContext& context) {
        // If the expression is already known to be constant just return the value we have.
        if (expr.constant)
            return *expr.constant;

        if (expr.bad())
            return nullptr;

        // Otherwise evaluate and return that.
        return expr.evalImpl(context);
    }

    ConstantValue visitInvalid(const Expression&) {
        return nullptr;
    }
};

class LValueVisitor {
    HAS_METHOD_TRAIT(evalLValueImpl);

public:
    template<typename T>
    LValue visit(const T& expr, EvalContext& context) {
        if constexpr (has_evalLValueImpl_v<T, LValue, EvalContext&>) {
            if (expr.bad())
                return nullptr;

            return expr.evalLValueImpl(context);
        }
        else {
            (void)expr;
            (void)context;
            THROW_UNREACHABLE;
        }
    }

    LValue visitInvalid(const Expression&) {
        return nullptr;
    }
};

ConstantValue evalBinaryOperator(BinaryOperator op, const ConstantValue& cvl, const ConstantValue& cvr) {
    // TODO: handle non-integer
    if (!cvl.isInteger() || !cvr.isInteger())
        return nullptr;

    const SVInt& l = cvl.integer();
    const SVInt& r = cvr.integer();

#define OP(k, v) case BinaryOperator::k: return v
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
    }
    THROW_UNREACHABLE;
#undef OP
}

}

namespace slang {

bool Expression::evalBool(EvalContext& context) const {
    ConstantValue result = eval(context);
    if (!result.isInteger())
        return false;

    return (bool)(logic_t)result.integer();
}

ConstantValue Expression::eval(EvalContext& context) const {
    EvalVisitor visitor;
    return visit(visitor, context);
}

LValue Expression::evalLValue(EvalContext& context) const {
    LValueVisitor visitor;
    return visit(visitor, context);
}

ConstantValue IntegerLiteral::evalImpl(EvalContext&) const {
    SVInt result = getValue();
    ASSERT(result.getBitWidth() == type->getBitWidth());
    return result;
}

ConstantValue RealLiteral::evalImpl(EvalContext&) const {
    return value;
}

ConstantValue UnbasedUnsizedIntegerLiteral::evalImpl(EvalContext&) const {
    bitwidth_t width = type->getBitWidth();
    bool isSigned = type->isSigned();

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

ConstantValue NullLiteral::evalImpl(EvalContext&) const {
    return ConstantValue::NullPlaceholder{};
}

ConstantValue StringLiteral::evalImpl(EvalContext&) const {
    // TODO: truncation / resizing?
    if (value.empty())
        return SVInt(8, 0, false);

    // TODO: store SVInt locally
    return SVInt(type->getBitWidth(), as_bytes(make_span(value)), false);
}

ConstantValue NamedValueExpression::evalImpl(EvalContext& context) const {
    switch (symbol.kind) {
        case SymbolKind::Parameter:
            return symbol.as<ParameterSymbol>().getValue();
        case SymbolKind::EnumValue:
            return symbol.as<EnumValueSymbol>().value;
        default:
            ConstantValue* v = context.findLocal(&symbol);
            // TODO: report error if not constant
            return v ? *v : nullptr;
    }
}

LValue NamedValueExpression::evalLValueImpl(EvalContext& context) const {
    auto cv = context.findLocal(&symbol);
    if (!cv)
        return nullptr;

    return LValue(*cv);
}

ConstantValue UnaryExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = operand().eval(context);
    if (!cv)
        return nullptr;

    // TODO: handle non-integer
    SVInt v = cv.integer();

    // TODO: more robust lvalue handling
    ConstantValue* lvalue = nullptr;
    switch (op) {
        case UnaryOperator::Preincrement:
        case UnaryOperator::Predecrement:
        case UnaryOperator::Postincrement:
        case UnaryOperator::Postdecrement:
            lvalue = context.findLocal(&((const NamedValueExpression&)operand()).symbol);
            ASSERT(lvalue);
            break;
        default:
            break;
    }

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
        case UnaryOperator::Preincrement: *lvalue = ++v; return v;
        case UnaryOperator::Predecrement: *lvalue = --v; return v;
        case UnaryOperator::Postincrement: *lvalue = v + 1; return v;
        case UnaryOperator::Postdecrement: *lvalue = v - 1; return v;
    }
    THROW_UNREACHABLE;
#undef OP
}

ConstantValue BinaryExpression::evalImpl(EvalContext& context) const {
    ConstantValue cvl = left().eval(context);
    ConstantValue cvr = right().eval(context);
    if (!cvl || !cvr)
        return nullptr;

    return evalBinaryOperator(op, cvl, cvr);
}

ConstantValue ConditionalExpression::evalImpl(EvalContext& context) const {
    ConstantValue cp = pred().eval(context);
    if (!cp)
        return nullptr;

    SVInt cond = cp.integer();
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

ConstantValue AssignmentExpression::evalImpl(EvalContext& context) const {
    LValue lvalue = left().evalLValue(context);
    ConstantValue rvalue = right().eval(context);
    if (!lvalue || !rvalue)
        return nullptr;

    // TODO: ensure rhs is truncated to size of lhs

    if (!isCompound())
        lvalue.store(rvalue);
    else {
        rvalue = evalBinaryOperator(*op, lvalue.load(), rvalue);
        lvalue.store(rvalue);
    }

    return rvalue;
}

ConstantValue ElementSelectExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    ConstantValue cs = selector().eval(context);
    if (!cv || !cs)
        return nullptr;

    optional<ConstantRange> range = getRange(cs);
    if (!range) {
        // If any part of an address is unknown, then the whole thing returns 'x.
        return SVInt::createFillX(type->getBitWidth(), false);
    }

    return cv.integer().slice(range->upper(), range->lower());
}

LValue ElementSelectExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    ConstantValue cs = selector().eval(context);
    if (!lval || !cs)
        return nullptr;

    optional<ConstantRange> range = getRange(cs);
    if (!range)
        return nullptr;

    return lval.selectRange(*range);
}

optional<ConstantRange> ElementSelectExpression::getRange(const ConstantValue& selectorValue) const {
    optional<int32_t> index = selectorValue.integer().as<int32_t>();
    if (!index)
        return std::nullopt;

    const Type& t = value().type->getCanonicalType();
    ConstantRange declRange = t.as<IntegralType>().getBitVectorRange();
    int32_t actualIndex = declRange.translateIndex(*index);

    // We're actually selecting elements, which aren't necessarily bits.
    // TODO: handle overflow?
    int32_t width = type->getBitWidth();
    actualIndex *= width;

    return ConstantRange { actualIndex + width - 1, actualIndex };
}

ConstantValue RangeSelectExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    ConstantValue cl = left().eval(context);
    ConstantValue cr = right().eval(context);
    if (!cv || !cl || !cr)
        return nullptr;

    optional<ConstantRange> range = getRange(cl, cr);
    if (!range) {
        // If any part of an address is unknown, then the whole thing returns 'x.
        return SVInt::createFillX(type->getBitWidth(), false);
    }

    return cv.integer().slice(range->upper(), range->lower());
}

LValue RangeSelectExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    ConstantValue cl = left().eval(context);
    ConstantValue cr = right().eval(context);
    if (!lval || !cl || !cr)
        return nullptr;

    optional<ConstantRange> range = getRange(cl, cr);
    if (!range)
        return nullptr;

    return lval.selectRange(*range);
}

optional<ConstantRange> RangeSelectExpression::getRange(const ConstantValue& cl,
                                                        const ConstantValue& cr) const {
    optional<int32_t> l = cl.integer().as<int32_t>();
    optional<int32_t> r = cr.integer().as<int32_t>();
    if (!l || !r)
        return std::nullopt;

    const Type& t = value().type->getCanonicalType();
    ConstantRange declRange = t.as<IntegralType>().getBitVectorRange();
    int32_t msb = declRange.translateIndex(*l);

    // We're actually selecting elements, which aren't necessarily bits.
    int32_t width = 1;
    if (t.kind == SymbolKind::PackedArrayType) {
        // TODO: handle overflow?
        width = (int32_t)t.as<PackedArrayType>().elementType.getBitWidth();
        msb *= width;
    }

    ConstantRange result;
    switch (selectionKind) {
        case RangeSelectionKind::Simple: {
            int32_t lsb = declRange.translateIndex(*r) * width;
            result = { msb, lsb };
            break;
        }
        case RangeSelectionKind::IndexedUp: {
            int32_t count = (*r - 1) * width;
            result = { msb + count, msb };
            break;
        }
        case RangeSelectionKind::IndexedDown: {
            int32_t count = (*r - 1) * width;
            result = { msb, msb - count };
            break;
        }
        default:
            THROW_UNREACHABLE;
    }

    result.left += width - 1;
    return result;
}

ConstantValue MemberAccessExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    if (!cv)
        return nullptr;

    // TODO: handle unpacked
    ASSERT(field.isPacked());
    int32_t offset = (int32_t)field.offset;
    int32_t width = (int32_t)type->getBitWidth();
    return cv.integer().slice(width + offset - 1, offset);
}

LValue MemberAccessExpression::evalLValueImpl(EvalContext& context) const {
    // TODO: handle unpacked
    ASSERT(field.isPacked());
    int32_t offset = (int32_t)field.offset;
    int32_t width = (int32_t)type->getBitWidth();

    return value().evalLValue(context).selectRange({ width + offset - 1, offset });
}

ConstantValue ConcatenationExpression::evalImpl(EvalContext& context) const {
    SmallVectorSized<SVInt, 8> values;
    for (auto operand : operands()) {
        // Skip zero-width replication operands.
        if (operand->type->isVoid())
            continue;

        ConstantValue v = operand->eval(context);
        if (!v)
            return nullptr;

        values.append(v.integer());
    }

    // TODO: add support for other Nary Expressions, like stream concatenation
    //switch (expr.syntax.kind) {
    //  case SyntaxKind::ConcatenationExpression: return concatenate(values);
    //}

    return concatenate(values);
}

ConstantValue ReplicationExpression::evalImpl(EvalContext& context) const {
    if (type->isVoid())
        return SVInt(0);

    ConstantValue v = concat().eval(context);
    ConstantValue c = count().eval(context);
    if (!v || !c)
        return nullptr;

    return v.integer().replicate(c.integer());
}

ConstantValue CallExpression::evalImpl(EvalContext& context) const {
    // Evaluate all argument in the current stack frame.
    SmallVectorSized<ConstantValue, 8> args;
    for (auto arg : arguments()) {
        ConstantValue v = arg->eval(context);
        if (!v)
            return nullptr;
        args.emplace(std::move(v));
    }

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
    context.pushFrame(subroutine);
    span<const FormalArgumentSymbol* const> formals = subroutine.arguments;
    for (uint32_t i = 0; i < formals.size(); i++)
        context.createLocal(formals[i], args[i]);

    context.createLocal(subroutine.returnValVar);

    subroutine.getBody()->eval(context);

    // Pop the frame and return the value
    return context.popFrame();
}

ConstantValue ConversionExpression::evalImpl(EvalContext& context) const {
    ConstantValue value = operand().eval(context);
    if (!value)
        return nullptr;

    switch (conversionKind) {
        case ConversionKind::IntToFloat:
            // TODO: make this more robust
            return (double)value.integer().as<int64_t>().value();

        case ConversionKind::IntExtension:
            ASSERT(value.isInteger() && value.integer().getBitWidth() == operand().type->getBitWidth());
            return extend(value.integer(), (uint16_t)type->getBitWidth(), type->as<IntegralType>().isSigned);

        case ConversionKind::IntTruncation:
            // TODO: add a truncate() method
            return value.integer().slice(type->getBitWidth() - 1, 0);

        case ConversionKind::FloatExtension:
            return value;

        default:
            THROW_UNREACHABLE;
    }
}

}