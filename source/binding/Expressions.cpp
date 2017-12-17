//------------------------------------------------------------------------------
// Expressions.cpp
// Expression creation and analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Expressions.h"

#include "binding/Statements.h"
#include "symbols/TypeSymbols.h"

namespace slang {

const InvalidExpression InvalidExpression::Instance(nullptr, ErrorType::Instance);

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
        case ExpressionKind::TernaryOp: return as<TernaryExpression>().eval(context);
        case ExpressionKind::Select: return as<SelectExpression>().eval(context);
        case ExpressionKind::NaryOp: return as<NaryExpression>().eval(context);
        case ExpressionKind::Call: return as<CallExpression>().eval(context);
    }
    THROW_UNREACHABLE;
}

IntegerLiteral::IntegerLiteral(BumpAllocator& alloc, const Type& type, const SVInt& value,
                               const ExpressionSyntax& syntax) :
    Expression(ExpressionKind::IntegerLiteral, type, syntax),
    valueStorage(value.getBitWidth(), value.isSigned(), value.hasUnknown())
{
    if (value.isSingleWord())
        valueStorage.val = *value.getRawData();
    else {
        valueStorage.pVal = (uint64_t*)alloc.allocate(sizeof(uint64_t) * value.getNumWords(), alignof(uint64_t));
        memcpy(valueStorage.pVal, value.getRawData(), sizeof(uint64_t) * value.getNumWords());
    }
}

ConstantValue IntegerLiteral::eval(EvalContext&) const {
    uint16_t width = (uint16_t)type->getBitWidth();
    SVInt result = getValue();

    // TODO: truncation?
    if (width > result.getBitWidth())
        result = extend(result, width, type->as<IntegralType>().isSigned);
    return { *type, result };
}

ConstantValue RealLiteral::eval(EvalContext&) const {
    return { *type, value };
}

ConstantValue UnbasedUnsizedIntegerLiteral::eval(EvalContext&) const {
    uint16_t width = (uint16_t)type->getBitWidth();
    bool isSigned = type->as<IntegralType>().isSigned;

    switch (value.value) {
        case 0: return { *type, SVInt(width, 0, isSigned) };
        case 1: {
            SVInt tmp(width, 0, isSigned);
            tmp.setAllOnes();
            return { *type, tmp };
        }
        case logic_t::X_VALUE: return { *type, SVInt::createFillX(width, isSigned) };
        case logic_t::Z_VALUE: return { *type, SVInt::createFillZ(width, isSigned) };
        default: THROW_UNREACHABLE;
    }
}

ConstantValue VariableRefExpression::eval(EvalContext& context) const {
    ConstantValue* v = context.findLocal(&symbol);
    ASSERT(v);
    return *v;
}

ConstantValue ParameterRefExpression::eval(EvalContext&) const {
    return *symbol.value;
}

ConstantValue UnaryExpression::eval(EvalContext& context) const {
    SVInt v = operand().eval(context).integer();

#define OP(k, v) case UnaryOperator::k: return { *type, v };
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

bool BinaryExpression::isAssignment() const {
    switch (op) {
        case BinaryOperator::Assignment:
        case BinaryOperator::AddAssignment:
        case BinaryOperator::SubtractAssignment:
        case BinaryOperator::MultiplyAssignment:
        case BinaryOperator::DivideAssignment:
        case BinaryOperator::ModAssignment:
        case BinaryOperator::AndAssignment:
        case BinaryOperator::OrAssignment:
        case BinaryOperator::XorAssignment:
        case BinaryOperator::LogicalLeftShiftAssignment:
        case BinaryOperator::LogicalRightShiftAssignment:
        case BinaryOperator::ArithmeticLeftShiftAssignment:
        case BinaryOperator::ArithmeticRightShiftAssignment:
            return true;
        default:
            return false;
    }
}

ConstantValue BinaryExpression::eval(EvalContext& context) const {
    SVInt l = left().eval(context).integer();
    SVInt r = right().eval(context).integer();

    // TODO: more robust lvalue handling
    ConstantValue* lvalue = nullptr;
    if (isAssignment()) {
        lvalue = context.findLocal(&((const VariableRefExpression&)left()).symbol);
        ASSERT(lvalue);
    }

#define OP(k, v) case BinaryOperator::k: return { *type, v }
#define ASSIGN(k, v) case BinaryOperator::k: *lvalue = { *type, v }; return *lvalue
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

ConstantValue TernaryExpression::eval(EvalContext& context) const {
    SVInt cond = pred().eval(context).integer();
    logic_t pred = (logic_t)cond;

    if (pred.isUnknown()) {
        // do strange combination operation
        SVInt l = left().eval(context).integer();
        SVInt r = right().eval(context).integer();
        return { *type, SVInt::conditional(cond, l, r) };
    }
    else if (pred) {
        return { *type, left().eval(context).integer() };
    }
    else {
        return { *type, right().eval(context).integer() };
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
        return { *type, SVInt::createFillX((uint16_t)type->getBitWidth(), false) };
    }

    // SVInt uses little endian ranges starting from zero; we need to translate from the
    // actual range used in the declaration of the variable.
    int16_t actualMsb = int16_t(msb.as<int>().value() - range.lower());
    if (!range.isLittleEndian())
        actualMsb = int16_t(range.width() - actualMsb - 1);

    switch (kind) {
        case SyntaxKind::BitSelect: {
            return { *type, value.bitSelect(actualMsb, actualMsb) };
        }
        case SyntaxKind::SimpleRangeSelect: {
            int16_t actualLsb = int16_t(lsbOrWidth.as<int>().value() - range.lower());
            if (!range.isLittleEndian())
                actualLsb = int16_t(range.width() - actualLsb - 1);

            return { *type, value.bitSelect(actualLsb, actualMsb) };
        }
        case SyntaxKind::AscendingRangeSelect: {
            int16_t width = lsbOrWidth.as<int16_t>().value();
            return { *type, value.bitSelect(actualMsb, actualMsb + width) };
        }
        case SyntaxKind::DescendingRangeSelect: {
            int16_t width = lsbOrWidth.as<int16_t>().value();
            return { *type, value.bitSelect(actualMsb - width, actualMsb) };
        }
        default:
            THROW_UNREACHABLE;
    }
}

ConstantValue NaryExpression::eval(EvalContext& context) const {
    SmallVectorSized<SVInt, 8> values;
    for (auto operand : operands())
        values.append(operand->eval(context).integer());

    // TODO: add support for other Nary Expressions, like stream concatenation
    //switch (expr.syntax.kind) {
      //  case SyntaxKind::ConcatenationExpression: return concatenate(values);
    //}

    return { *type, concatenate(values) };
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
            case SystemFunction::clog2: return { *type, SVInt(clog2(args[0].integer())) };
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
                    case SystemFunction::bits:  return { *type, SVInt(argType.bitWidth) };
                    case SystemFunction::low:   return { *type, SVInt(range.lower()) };
                    case SystemFunction::high:  return { *type, SVInt(range.upper()) };
                    case SystemFunction::left:  return { *type, SVInt(range.left) };
                    case SystemFunction::right: return { *type, SVInt(range.right) };
                    case SystemFunction::size:  return { *type, SVInt(argType.bitWidth) };
                    case SystemFunction::increment: return { *type, SVInt(range.isLittleEndian() ? 1 : -1) };
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

void Expression::propagateType(const Type& newType) {
    // SystemVerilog rules for width propagation are subtle and very specific
    // to each individual operator type. They also mainly only apply to
    // expressions of integral type (which will be the majority in most designs).
    switch (kind) {
        case ExpressionKind::Invalid:
            return;
        case ExpressionKind::IntegerLiteral:
            as<IntegerLiteral>().propagateType(newType);
            break;
        case ExpressionKind::RealLiteral:
            as<RealLiteral>().propagateType(newType);
            break;
        case ExpressionKind::UnbasedUnsizedIntegerLiteral:
            as<UnbasedUnsizedIntegerLiteral>().propagateType(newType);
            break;
        case ExpressionKind::Call:
        case ExpressionKind::VariableRef:
        case ExpressionKind::ParameterRef:
        case ExpressionKind::NaryOp:
        case ExpressionKind::Select:
            // all operands are self determined
            type = &newType;
            break;
        case ExpressionKind::UnaryOp:
            as<UnaryExpression>().propagateType(newType);
            break;
        case ExpressionKind::BinaryOp:
            as<BinaryExpression>().propagateType(newType);
            break;
        case ExpressionKind::TernaryOp:
            as<TernaryExpression>().propagateType(newType);
            break;
    }
}

void IntegerLiteral::propagateType(const Type& newType) {
    type = &newType;
}

void RealLiteral::propagateType(const Type& newType) {
    type = &newType;
}

void UnbasedUnsizedIntegerLiteral::propagateType(const Type& newType) {
    type = &newType;
}

void UnaryExpression::propagateType(const Type& newType) {
    // If a type of real is propagated to an expression of a non-real type, the type of the
    // direct sub-expression is changed, but it is not propagated any further down.
    bool doNotPropagateRealDownToNonReal = newType.isFloating() && !type->isFloating();

    switch (op) {
        case UnaryOperator::Plus:
        case UnaryOperator::Minus:
        case UnaryOperator::BitwiseNot:
            type = &newType;
            if (!doNotPropagateRealDownToNonReal)
                operand().propagateType(newType);
            break;
        case UnaryOperator::BitwiseAnd:
        case UnaryOperator::BitwiseOr:
        case UnaryOperator::BitwiseXor:
        case UnaryOperator::BitwiseNand:
        case UnaryOperator::BitwiseNor:
        case UnaryOperator::BitwiseXnor:
        case UnaryOperator::LogicalNot:
            // Type is already set (always 1 bit) and operand is self determined
            break;
    }
}

void BinaryExpression::propagateType(const Type& newType) {
    // If a type of real is propagated to an expression of a non-real type, the type of the
    // direct sub-expression is changed, but it is not propagated any further down.
    bool doNotPropagateRealDownToNonReal = newType.isFloating() && !type->isFloating();

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
            if (!doNotPropagateRealDownToNonReal) {
                left().propagateType(newType);
                right().propagateType(newType);
            }
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
            // Relational expressions are essentially self-detetermined, the logic
            // for how the left and right operands effect each other is handled
            // at creation time.
            break;
        case BinaryOperator::LogicalAnd:
        case BinaryOperator::LogicalOr:
        case BinaryOperator::LogicalImplication:
        case BinaryOperator::LogicalEquivalence:
            // Type is already set (always 1 bit) and operands are self determined
            break;
        case BinaryOperator::LogicalShiftLeft:
        case BinaryOperator::LogicalShiftRight:
        case BinaryOperator::ArithmeticShiftLeft:
        case BinaryOperator::ArithmeticShiftRight:
        case BinaryOperator::Power:
            // Only the left hand side gets propagated; the rhs is self determined
            type = &newType;
            if (!doNotPropagateRealDownToNonReal)
                left().propagateType(newType);
            break;
        case BinaryOperator::Assignment:
        case BinaryOperator::AddAssignment:
        case BinaryOperator::SubtractAssignment:
        case BinaryOperator::MultiplyAssignment:
        case BinaryOperator::DivideAssignment:
        case BinaryOperator::ModAssignment:
        case BinaryOperator::AndAssignment:
        case BinaryOperator::OrAssignment:
        case BinaryOperator::XorAssignment:
        case BinaryOperator::LogicalLeftShiftAssignment:
        case BinaryOperator::LogicalRightShiftAssignment:
        case BinaryOperator::ArithmeticLeftShiftAssignment:
        case BinaryOperator::ArithmeticRightShiftAssignment:
            // Essentially self determined, logic handled at creation time.
            break;
        case BinaryOperator::Replication:
            // all operands are self determined
            type = &newType;
            break;
    }
}

void TernaryExpression::propagateType(const Type& newType) {
    // If a type of real is propagated to an expression of a non-real type, the type of the
    // direct sub-expression is changed, but it is not propagated any further down.
    bool doNotPropagateRealDownToNonReal = newType.isFloating() && !type->isFloating();

    // predicate is self determined
    type = &newType;
    if (!doNotPropagateRealDownToNonReal) {
        left().propagateType(newType);
        right().propagateType(newType);
    }
}

UnaryOperator getUnaryOperator(const ExpressionSyntax& syntax) {
    switch (syntax.kind) {
        case SyntaxKind::UnaryPlusExpression: return UnaryOperator::Plus;
        case SyntaxKind::UnaryMinusExpression: return UnaryOperator::Minus;
        case SyntaxKind::UnaryBitwiseNotExpression: return UnaryOperator::BitwiseNot;
        case SyntaxKind::UnaryBitwiseAndExpression: return UnaryOperator::BitwiseAnd;
        case SyntaxKind::UnaryBitwiseOrExpression: return UnaryOperator::BitwiseOr;
        case SyntaxKind::UnaryBitwiseXorExpression: return UnaryOperator::BitwiseXor;
        case SyntaxKind::UnaryBitwiseNandExpression: return UnaryOperator::BitwiseNand;
        case SyntaxKind::UnaryBitwiseNorExpression: return UnaryOperator::BitwiseNor;
        case SyntaxKind::UnaryBitwiseXnorExpression: return UnaryOperator::BitwiseXnor;
        case SyntaxKind::UnaryLogicalNotExpression: return UnaryOperator::LogicalNot;
        default: THROW_UNREACHABLE;
    }
}

BinaryOperator getBinaryOperator(const ExpressionSyntax& syntax) {
    switch (syntax.kind) {
        case SyntaxKind::AddExpression: return BinaryOperator::Add;
        case SyntaxKind::SubtractExpression: return BinaryOperator::Subtract;
        case SyntaxKind::MultiplyExpression: return BinaryOperator::Multiply;
        case SyntaxKind::DivideExpression: return BinaryOperator::Divide;
        case SyntaxKind::ModExpression: return BinaryOperator::Mod;
        case SyntaxKind::BinaryAndExpression: return BinaryOperator::BinaryAnd;
        case SyntaxKind::BinaryOrExpression: return BinaryOperator::BinaryOr;
        case SyntaxKind::BinaryXorExpression: return BinaryOperator::BinaryXor;
        case SyntaxKind::BinaryXnorExpression: return BinaryOperator::BinaryXnor;
        case SyntaxKind::EqualityExpression: return BinaryOperator::Equality;
        case SyntaxKind::InequalityExpression: return BinaryOperator::Inequality;
        case SyntaxKind::CaseEqualityExpression: return BinaryOperator::CaseEquality;
        case SyntaxKind::CaseInequalityExpression: return BinaryOperator::CaseInequality;
        case SyntaxKind::GreaterThanEqualExpression: return BinaryOperator::GreaterThanEqual;
        case SyntaxKind::GreaterThanExpression: return BinaryOperator::GreaterThan;
        case SyntaxKind::LessThanEqualExpression: return BinaryOperator::LessThanEqual;
        case SyntaxKind::LessThanExpression: return BinaryOperator::LessThan;
        case SyntaxKind::WildcardEqualityExpression: return BinaryOperator::WildcardEquality;
        case SyntaxKind::WildcardInequalityExpression: return BinaryOperator::WildcardInequality;
        case SyntaxKind::LogicalAndExpression: return BinaryOperator::LogicalAnd;
        case SyntaxKind::LogicalOrExpression: return BinaryOperator::LogicalOr;
        case SyntaxKind::LogicalImplicationExpression: return BinaryOperator::LogicalImplication;
        case SyntaxKind::LogicalEquivalenceExpression: return BinaryOperator::LogicalEquivalence;
        case SyntaxKind::LogicalShiftLeftExpression: return BinaryOperator::LogicalShiftLeft;
        case SyntaxKind::LogicalShiftRightExpression: return BinaryOperator::LogicalShiftRight;
        case SyntaxKind::ArithmeticShiftLeftExpression: return BinaryOperator::ArithmeticShiftLeft;
        case SyntaxKind::ArithmeticShiftRightExpression: return BinaryOperator::ArithmeticShiftRight;
        case SyntaxKind::PowerExpression: return BinaryOperator::Power;
        case SyntaxKind::MultipleConcatenationExpression: return BinaryOperator::Replication;
        case SyntaxKind::AssignmentExpression: return BinaryOperator::Assignment;
        case SyntaxKind::AddAssignmentExpression: return BinaryOperator::AddAssignment;
        case SyntaxKind::SubtractAssignmentExpression: return BinaryOperator::SubtractAssignment;
        case SyntaxKind::MultiplyAssignmentExpression: return BinaryOperator::MultiplyAssignment;
        case SyntaxKind::DivideAssignmentExpression: return BinaryOperator::DivideAssignment;
        case SyntaxKind::ModAssignmentExpression: return BinaryOperator::ModAssignment;
        case SyntaxKind::AndAssignmentExpression: return BinaryOperator::AndAssignment;
        case SyntaxKind::OrAssignmentExpression: return BinaryOperator::OrAssignment;
        case SyntaxKind::XorAssignmentExpression: return BinaryOperator::XorAssignment;
        case SyntaxKind::LogicalLeftShiftAssignmentExpression: return BinaryOperator::LogicalLeftShiftAssignment;
        case SyntaxKind::LogicalRightShiftAssignmentExpression: return BinaryOperator::LogicalRightShiftAssignment;
        case SyntaxKind::ArithmeticLeftShiftAssignmentExpression: return BinaryOperator::ArithmeticLeftShiftAssignment;
        case SyntaxKind::ArithmeticRightShiftAssignmentExpression: return BinaryOperator::ArithmeticRightShiftAssignment;
        default: THROW_UNREACHABLE;
    }
}

}
