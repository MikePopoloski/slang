//------------------------------------------------------------------------------
// Expressions_eval.cpp
// Constant expression evaluation.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/Expressions.h"
#include "slang/binding/Statements.h"
#include "slang/compilation/Compilation.h"
#include "slang/symbols/ASTVisitor.h"

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

    ConstantValue visitInvalid(const Expression&, EvalContext&) { return nullptr; }
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

    LValue visitInvalid(const Expression&, EvalContext&) { return nullptr; }
};

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

ConstantValue evalBinaryOperator(BinaryOperator op, const ConstantValue& cvl,
                                 const ConstantValue& cvr) {
    if (!cvl || !cvr)
        return nullptr;

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
                OP(WildcardEquality, SVInt(wildcardEqual(l, r)));
                OP(WildcardInequality, SVInt(!wildcardEqual(l, r)));
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
    else if (cvl.isUnpacked()) {
        span<const ConstantValue> la = cvl.elements();
        span<const ConstantValue> ra = cvr.elements();
        ASSERT(la.size() == ra.size());

        for (ptrdiff_t i = 0; i < la.size(); i++) {
            ConstantValue result = evalBinaryOperator(op, la[i], ra[i]);
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

bool isTrue(const ConstantValue& cv) {
    if (cv.isInteger())
        return (bool)(logic_t)cv.integer();
    if (cv.isReal())
        return (bool)cv.real();
    if (cv.isShortReal())
        return (bool)cv.shortReal();
    return false;
}

bool isFalse(const ConstantValue& cv) {
    if (cv.isInteger()) {
        logic_t l = (logic_t)cv.integer();
        return !l.isUnknown() && l.value == 0;
    }
    if (cv.isReal())
        return !(bool)cv.real();
    if (cv.isShortReal())
        return !(bool)cv.shortReal();
    if (cv.isNullHandle())
        return true;

    return false;
}

bool checkArrayIndex(EvalContext& context, const Type& type, const ConstantValue& cs,
                     const std::string& str, SourceRange sourceRange, int32_t& result) {
    optional<int32_t> index = cs.integer().as<int32_t>();
    if (index && type.isString()) {
        if (*index < 0 || size_t(*index) >= str.size()) {
            context.addDiag(DiagCode::NoteStringIndexInvalid, sourceRange) << cs << str.size();
            return false;
        }

        result = *index;
        return true;
    }

    ConstantRange range = type.getArrayRange();
    if (!index || !range.containsPoint(*index)) {
        context.addDiag(DiagCode::NoteArrayIndexInvalid, sourceRange) << cs << type;
        return false;
    }

    result = range.translateIndex(*index);
    return true;
}

SVInt convertIntToInt(const SVInt& integer, bitwidth_t width, bool isSigned, bool isFourState) {
    SVInt result = integer;
    if (!isFourState)
        result.flattenUnknowns();

    // [11.8.3] says that during an assignment we sign extend iff the rhs is signed.
    // That means we should resize first, and only then change the sign flag if desired.
    if (width != result.getBitWidth())
        result = result.resize(width);

    result.setSigned(isSigned);
    return result;
}

std::string convertIntToStr(const SVInt& integer) {
    // Conversion is described in [6.16]: take each 8 bit chunk,
    // remove it if it's zero, otherwise add as character to the string.
    int32_t msb = int32_t(integer.getBitWidth() - 1);
    int32_t extraBits = int32_t(integer.getBitWidth() % 8);

    std::string result;
    if (extraBits) {
        auto c = integer.slice(msb, msb - extraBits + 1).as<uint8_t>();
        if (c && *c)
            result.push_back(char(*c));
        msb -= extraBits;
    }

    while (msb >= 7) {
        auto c = integer.slice(msb, msb - 7).as<uint8_t>();
        if (c && *c)
            result.push_back(char(*c));
        msb -= 8;
    }

    return result;
}

} // namespace

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

ConstantValue Expression::eval() const {
    EvalContext context;
    return eval(context);
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
    return real_t(value);
}

ConstantValue UnbasedUnsizedIntegerLiteral::evalImpl(EvalContext&) const {
    bitwidth_t width = type->getBitWidth();
    bool isSigned = type->isSigned();

    switch (value.value) {
        case 0:
            return SVInt(width, 0, isSigned);
        case 1: {
            SVInt tmp(width, 0, isSigned);
            tmp.setAllOnes();
            return tmp;
        }
        case logic_t::X_VALUE:
            return SVInt::createFillX(width, isSigned);
        case logic_t::Z_VALUE:
            return SVInt::createFillZ(width, isSigned);
        default:
            THROW_UNREACHABLE;
    }
}

ConstantValue NullLiteral::evalImpl(EvalContext&) const {
    return ConstantValue::NullPlaceholder{};
}

ConstantValue StringLiteral::evalImpl(EvalContext&) const {
    return *intStorage;
}

ConstantValue NamedValueExpression::evalImpl(EvalContext& context) const {
    if (!verifyAccess(context))
        return nullptr;

    switch (symbol.kind) {
        case SymbolKind::Parameter:
            return symbol.as<ParameterSymbol>().getValue();
        case SymbolKind::EnumValue:
            return symbol.as<EnumValueSymbol>().getValue();
        default:
            ConstantValue* v = context.findLocal(&symbol);
            if (v)
                return *v;
            break;
    }

    // If we reach this point, the variable was not found, which should mean that
    // it's not actually constant.
    context.addDiag(DiagCode::NoteNonConstVariable, sourceRange) << symbol.name;
    context.addDiag(DiagCode::NoteDeclarationHere, symbol.location);
    return nullptr;
}

LValue NamedValueExpression::evalLValueImpl(EvalContext& context) const {
    if (!verifyAccess(context))
        return nullptr;

    auto cv = context.findLocal(&symbol);
    if (!cv) {
        context.addDiag(DiagCode::NoteNonConstVariable, sourceRange) << symbol.name;
        context.addDiag(DiagCode::NoteDeclarationHere, symbol.location);
        return nullptr;
    }

    return LValue(*cv);
}

bool NamedValueExpression::verifyAccess(EvalContext& context) const {
    if (context.isScriptEval())
        return true;

    // Hierarchical names are disallowed in constant expressions and constant functions
    if (isHierarchical) {
        context.addDiag(DiagCode::NoteHierarchicalNameInCE, sourceRange) << symbol.name;
        return false;
    }

    const EvalContext::Frame& frame = context.topFrame();
    const SubroutineSymbol* subroutine = frame.subroutine;
    if (!subroutine)
        return true;

    // Constant functions have a bunch of additional restrictions. See [13.4.4]:
    // - All parameter values used within the function shall be defined before the use of
    //   the invoking constant function call.
    // - All identifiers that are not parameters or functions shall be declared locally to
    //   the current function.
    if (symbol.kind != SymbolKind::Parameter) {
        const Scope* scope = symbol.getScope();
        while (scope && scope != subroutine)
            scope = scope->getParent();

        if (scope != subroutine) {
            context.addDiag(DiagCode::NoteFunctionIdentifiersMustBeLocal, sourceRange);
            context.addDiag(DiagCode::NoteDeclarationHere, symbol.location);
            return false;
        }
    }
    else {
        LookupLocation location = LookupLocation::after(symbol);
        const Scope* commonParent = subroutine->getParent();
        const Scope* scope = symbol.getScope();
        while (scope && scope != commonParent) {
            location = LookupLocation::before(scope->asSymbol());
            scope = scope->getParent();
        }

        if (!(location < frame.lookupLocation)) {
            context.addDiag(DiagCode::NoteParamUsedInCEBeforeDecl, sourceRange) << symbol.name;
            context.addDiag(DiagCode::NoteDeclarationHere, symbol.location);
            return false;
        }
    }

    return true;
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

ConstantValue BinaryExpression::evalImpl(EvalContext& context) const {
    ConstantValue cvl = left().eval(context);
    if (!cvl)
        return nullptr;

    // Handle short-circuiting operators up front, as we need to avoid
    // evaluating the rhs entirely in those cases.
    if (isShortCircuitOp(op)) {
        switch (op) {
            case BinaryOperator::LogicalOr:
                if (isTrue(cvl))
                    return SVInt(true);
                break;
            case BinaryOperator::LogicalAnd:
                if (isFalse(cvl))
                    return SVInt(false);
                break;
            case BinaryOperator::LogicalImplication:
                if (isFalse(cvl))
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

        if (cvl.isUnpacked()) {
            span<const ConstantValue> la = cvl.elements();
            span<const ConstantValue> ra = cvr.elements();
            ASSERT(la.size() == ra.size());

            ConstantValue resultValue = type->getDefaultValue();
            span<ConstantValue> result = resultValue.elements();
            ASSERT(la.size() == result.size());

            const Type& ct = type->getCanonicalType();
            ConstantValue defaultElement =
                ct.isUnpackedArray() ? ct.as<UnpackedArrayType>().elementType.getDefaultValue()
                                     : ct.as<PackedArrayType>().elementType.getDefaultValue();

            // [11.4.11] says that if both sides are unpacked arrays, we
            // check each element. If they are equal, take it in the result,
            // otherwise use the default.
            for (ptrdiff_t i = 0; i < la.size(); i++) {
                ConstantValue comp = evalBinaryOperator(BinaryOperator::Equality, la[i], ra[i]);
                if (!comp)
                    return nullptr;

                logic_t l = (logic_t)comp.integer();
                if (l.isUnknown() || !l)
                    result[i] = defaultElement;
                else
                    result[i] = la[i];
            }

            return resultValue;
        }

        return type->getDefaultValue();
    }

    if (isTrue(cp))
        return left().eval(context);
    else
        return right().eval(context);
}

ConstantValue AssignmentExpression::evalImpl(EvalContext& context) const {
    LValue lvalue = left().evalLValue(context);
    ConstantValue rvalue = right().eval(context);
    if (!lvalue || !rvalue)
        return nullptr;

    if (isCompound())
        rvalue = evalBinaryOperator(*op, lvalue.load(), rvalue);

    lvalue.store(rvalue);
    return rvalue;
}

ConstantValue ElementSelectExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    ConstantValue cs = selector().eval(context);
    if (!cv || !cs)
        return nullptr;

    std::string str = value().type->isString() ? cv.str() : "";

    int32_t index;
    if (!checkArrayIndex(context, *value().type, cs, str, sourceRange, index))
        return nullptr;

    if (value().type->isUnpackedArray())
        return cv.elements()[index];

    if (value().type->isString())
        return cv.getSlice(index, index);

    // For packed arrays, we're selecting bit ranges, not necessarily single bits.
    int32_t width = (int32_t)type->getBitWidth();
    index *= width;
    return cv.integer().slice(index + width - 1, index);
}

LValue ElementSelectExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    ConstantValue cs = selector().eval(context);
    if (!lval || !cs)
        return nullptr;

    std::string str = value().type->isString() ? lval.load().str() : "";

    int32_t index;
    if (!checkArrayIndex(context, *value().type, cs, str, sourceRange, index))
        return nullptr;

    if (value().type->isUnpackedArray())
        return lval.selectIndex(index);

    if (value().type->isString())
        return lval.selectRange({ index, index });

    // For packed arrays, we're selecting bit ranges, not necessarily single bits.
    int32_t width = (int32_t)type->getBitWidth();
    index *= width;
    return lval.selectRange({ index + width - 1, index });
}

ConstantValue RangeSelectExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    ConstantValue cl = left().eval(context);
    ConstantValue cr = right().eval(context);
    if (!cv || !cl || !cr)
        return nullptr;

    optional<ConstantRange> range = getRange(context, cl, cr);
    if (!range)
        return nullptr;

    return cv.getSlice(range->upper(), range->lower());
}

LValue RangeSelectExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    ConstantValue cl = left().eval(context);
    ConstantValue cr = right().eval(context);
    if (!lval || !cl || !cr)
        return nullptr;

    optional<ConstantRange> range = getRange(context, cl, cr);
    if (!range)
        return nullptr;

    return lval.selectRange(*range);
}

optional<ConstantRange> RangeSelectExpression::getRange(EvalContext& context,
                                                        const ConstantValue& cl,
                                                        const ConstantValue& cr) const {
    ConstantRange result;
    const Type& valueType = *value().type;
    ConstantRange valueRange = valueType.getArrayRange();

    if (selectionKind == RangeSelectionKind::Simple) {
        // If this is a simple part select, the range has already been fully validated at bind time.
        result = type->getArrayRange();
    }
    else {
        optional<int32_t> l = cl.integer().as<int32_t>();
        if (!l) {
            context.addDiag(DiagCode::NoteArrayIndexInvalid, sourceRange) << cl << valueType;
            return std::nullopt;
        }

        optional<int32_t> r = cr.integer().as<int32_t>();
        result = getIndexedRange(selectionKind, *l, *r, valueRange.isLittleEndian());

        if (!valueRange.containsPoint(result.left) || !valueRange.containsPoint(result.right)) {
            auto& diag = context.addDiag(DiagCode::NotePartSelectInvalid, sourceRange);
            diag << result.left << result.right;
            diag << valueType;
            return std::nullopt;
        }
    }

    if (!result.isLittleEndian())
        result.reverse();

    result.left = valueRange.translateIndex(result.left);
    result.right = valueRange.translateIndex(result.right);

    if (!valueType.isPackedArray())
        return result;

    // For packed arrays we're potentially selecting multi-bit elements.
    int32_t width =
        (int32_t)valueType.getCanonicalType().as<PackedArrayType>().elementType.getBitWidth();

    result.left *= width;
    result.right *= width;
    result.left += width - 1;

    return result;
}

ConstantValue MemberAccessExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    if (!cv)
        return nullptr;

    int32_t offset = (int32_t)field.offset;
    if (value().type->isUnpackedStruct())
        return cv.elements()[offset];

    int32_t width = (int32_t)type->getBitWidth();
    return cv.integer().slice(width + offset - 1, offset);
}

LValue MemberAccessExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    if (!lval)
        return nullptr;

    int32_t offset = (int32_t)field.offset;
    if (value().type->isUnpackedStruct())
        return lval.selectIndex(offset);

    int32_t width = (int32_t)type->getBitWidth();
    return lval.selectRange({ width + offset - 1, offset });
}

ConstantValue ConcatenationExpression::evalImpl(EvalContext& context) const {
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
            context.addDiag(DiagCode::NoteReplicationCountInvalid, count().sourceRange) << c;
            return nullptr;
        }

        std::string result;
        for (int32_t i = 0; i < *optCount; i++)
            result.append(v.str());

        return result;
    }

    return v.integer().replicate(c.integer());
}

ConstantValue CallExpression::evalImpl(EvalContext& context) const {
    // Delegate system calls to their appropriate handler.
    // TODO: handle non-constant system calls.
    if (isSystemCall())
        return std::get<1>(subroutine)->eval(context, arguments());

    // Evaluate all argument in the current stack frame.
    SmallVectorSized<ConstantValue, 8> args;
    for (auto arg : arguments()) {
        ConstantValue v = arg->eval(context);
        if (!v)
            return nullptr;
        args.emplace(std::move(v));
    }

    // Push a new stack frame, push argument values as locals.
    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    context.pushFrame(symbol, sourceRange.start(), lookupLocation);
    span<const FormalArgumentSymbol* const> formals = symbol.arguments;
    for (uint32_t i = 0; i < formals.size(); i++)
        context.createLocal(formals[i], args[i]);

    context.createLocal(symbol.returnValVar);

    bool succeeded = symbol.getBody()->eval(context);
    ConstantValue result = context.popFrame();

    return succeeded ? result : nullptr;
}

ConstantValue ConversionExpression::evalImpl(EvalContext& context) const {
    ConstantValue value = operand().eval(context);
    if (!value)
        return nullptr;

    const Type& to = *type;
    if (to.isIntegral()) {
        if (value.isReal())
            return SVInt::fromDouble(to.getBitWidth(), value.real(), to.isSigned());

        if (value.isShortReal())
            return SVInt::fromFloat(to.getBitWidth(), value.shortReal(), to.isSigned());

        return convertIntToInt(value.integer(), to.getBitWidth(), to.isSigned(), to.isFourState());
    }

    if (to.isFloating()) {
        if (value.isReal())
            return shortreal_t((float)value.real());

        if (value.isShortReal())
            return real_t(value.shortReal());

        if (to.getBitWidth() == 64)
            return real_t(value.integer().toDouble());

        ASSERT(to.getBitWidth() == 32);
        return shortreal_t(value.integer().toFloat());
    }

    if (to.isString())
        return convertIntToStr(value.integer());

    // TODO: other types
    THROW_UNREACHABLE;
}

ConstantValue DataTypeExpression::evalImpl(EvalContext&) const {
    return nullptr;
}

} // namespace slang