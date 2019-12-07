//------------------------------------------------------------------------------
// Expressions_eval.cpp
// Constant expression evaluation.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/Expressions.h"
#include "slang/binding/Statements.h"
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
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
    template<typename T, typename Arg>
    using evalLValue_t = decltype(std::declval<T>().evalLValueImpl(std::declval<Arg>()));

public:
    template<typename T>
    LValue visit(const T& expr, EvalContext& context) {
        if constexpr (is_detected_v<evalLValue_t, T, EvalContext&>) {
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

struct VerifyVisitor {
    template<typename T>
    bool visit(const T& expr, EvalContext& context) {
        if (expr.bad())
            return false;

        return expr.verifyConstantImpl(context);
    }

    bool visitInvalid(const Expression&, EvalContext&) { return false; }
};

bool checkArrayIndex(EvalContext& context, const Type& type, const ConstantValue& cs,
                     const std::string& str, SourceRange sourceRange, int32_t& result) {
    optional<int32_t> index = cs.integer().as<int32_t>();
    if (index && type.isString()) {
        if (*index < 0 || size_t(*index) >= str.size()) {
            context.addDiag(diag::NoteStringIndexInvalid, sourceRange) << cs << str.size();
            return false;
        }

        result = *index;
        return true;
    }

    ConstantRange range = type.getArrayRange();
    if (!index || !range.containsPoint(*index)) {
        context.addDiag(diag::NoteArrayIndexInvalid, sourceRange) << cs << type;
        return false;
    }

    result = range.translateIndex(*index);
    return true;
}

} // namespace

namespace slang {

ConstantValue Expression::eval(EvalContext& context) const {
    EvalVisitor visitor;
    return visit(visitor, context);
}

LValue Expression::evalLValue(EvalContext& context) const {
    LValueVisitor visitor;
    return visit(visitor, context);
}

bool Expression::verifyConstant(EvalContext& context) const {
    VerifyVisitor visitor;
    return visit(visitor, context);
}

ConstantValue NamedValueExpression::evalImpl(EvalContext& context) const {
    if (!verifyConstantImpl(context))
        return nullptr;

    switch (symbol.kind) {
        case SymbolKind::Parameter:
            // Special case for parameters: if this parameter is the child of a
            // definition symbol, the value it has isn't real (because it's not
            // part of a real instance). Just return nullptr here so that we don't
            // end up reporting a spurious error for a definition that is never
            // instantiated. If it does ever get instantiated, we'll catch any real
            // errors in the instance itself.
            if (symbol.getParentScope()->asSymbol().kind == SymbolKind::Definition)
                return nullptr;

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
    context.addDiag(diag::NoteNonConstVariable, sourceRange) << symbol.name;
    context.addDiag(diag::NoteDeclarationHere, symbol.location);
    return nullptr;
}

LValue NamedValueExpression::evalLValueImpl(EvalContext& context) const {
    if (!verifyConstantImpl(context))
        return nullptr;

    auto cv = context.findLocal(&symbol);
    if (!cv) {
        context.addDiag(diag::NoteNonConstVariable, sourceRange) << symbol.name;
        context.addDiag(diag::NoteDeclarationHere, symbol.location);
        return nullptr;
    }

    return LValue(*cv);
}

bool NamedValueExpression::verifyConstantImpl(EvalContext& context) const {
    if (context.isScriptEval())
        return true;

    // Hierarchical names are disallowed in constant expressions and constant functions
    if (isHierarchical) {
        context.addDiag(diag::NoteHierarchicalNameInCE, sourceRange) << symbol.name;
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
    if (symbol.kind != SymbolKind::Parameter && symbol.kind != SymbolKind::EnumValue) {
        const Scope* scope = symbol.getParentScope();
        while (scope && scope != subroutine)
            scope = scope->asSymbol().getParentScope();

        if (scope != subroutine) {
            context.addDiag(diag::NoteFunctionIdentifiersMustBeLocal, sourceRange);
            context.addDiag(diag::NoteDeclarationHere, symbol.location);
            return false;
        }
    }
    else {
        bool isBefore;
        auto frameScope = frame.lookupLocation.getScope();
        if (!frameScope || symbol.getParentScope() == frameScope)
            isBefore = LookupLocation::after(symbol) < frame.lookupLocation;
        else {
            // If the two locations are not in the same compilation unit, assume that it's ok.
            auto compare = symbol.isBeforeInCompilationUnit(frameScope->asSymbol());
            isBefore = compare.value_or(true);
        }

        if (!isBefore) {
            context.addDiag(diag::NoteIdUsedInCEBeforeDecl, sourceRange) << symbol.name;
            context.addDiag(diag::NoteDeclarationHere, symbol.location);
            return false;
        }
    }

    return true;
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
        return cv.elements()[size_t(index)];

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

    const std::string& str = value().type->isString() ? lval.load().str() : "";

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

bool ElementSelectExpression::verifyConstantImpl(EvalContext& context) const {
    return value().verifyConstant(context) && selector().verifyConstant(context);
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

bool RangeSelectExpression::verifyConstantImpl(EvalContext& context) const {
    return value().verifyConstant(context) && left().verifyConstant(context) &&
           right().verifyConstant(context);
}

optional<ConstantRange> RangeSelectExpression::getRange(EvalContext& context,
                                                        const ConstantValue& cl,
                                                        const ConstantValue& cr) const {
    ConstantRange result;
    const Type& valueType = *value().type;
    ConstantRange valueRange = valueType.getArrayRange();

    if (selectionKind == RangeSelectionKind::Simple) {
        result = type->getArrayRange();
    }
    else {
        optional<int32_t> l = cl.integer().as<int32_t>();
        if (!l) {
            context.addDiag(diag::NoteArrayIndexInvalid, sourceRange) << cl << valueType;
            return std::nullopt;
        }

        optional<int32_t> r = cr.integer().as<int32_t>();
        result = getIndexedRange(selectionKind, *l, *r, valueRange.isLittleEndian());
    }

    if (!valueRange.containsPoint(result.left) || !valueRange.containsPoint(result.right)) {
        auto& diag = context.addDiag(diag::NotePartSelectInvalid, sourceRange);
        diag << result.left << result.right;
        diag << valueType;
        return std::nullopt;
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

    // TODO: handle unpacked unions
    if (value().type->isUnpackedStruct())
        return cv.elements()[field.offset];

    int32_t offset = (int32_t)field.offset;
    int32_t width = (int32_t)type->getBitWidth();
    return cv.integer().slice(width + offset - 1, offset);
}

LValue MemberAccessExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    if (!lval)
        return nullptr;

    // TODO: handle unpacked unions
    int32_t offset = (int32_t)field.offset;
    if (value().type->isUnpackedStruct())
        return lval.selectIndex(offset);

    int32_t width = (int32_t)type->getBitWidth();
    return lval.selectRange({ width + offset - 1, offset });
}

bool MemberAccessExpression::verifyConstantImpl(EvalContext& context) const {
    return value().verifyConstant(context);
}

ConstantValue CallExpression::evalImpl(EvalContext& context) const {
    // Delegate system calls to their appropriate handler.
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
    if (!context.pushFrame(symbol, sourceRange.start(), lookupLocation))
        return nullptr;

    span<const FormalArgumentSymbol* const> formals = symbol.arguments;
    for (size_t i = 0; i < formals.size(); i++)
        context.createLocal(formals[i], args[i]);

    context.createLocal(symbol.returnValVar);

    using ER = Statement::EvalResult;
    ER er = symbol.getBody(&context).eval(context);

    ConstantValue result = std::move(*context.findLocal(symbol.returnValVar));
    context.popFrame();

    if (er == ER::Fail)
        return nullptr;

    ASSERT(er == ER::Success || er == ER::Return);
    return result;
}

bool CallExpression::verifyConstantImpl(EvalContext& context) const {
    for (auto arg : arguments()) {
        if (!arg->verifyConstant(context))
            return false;
    }

    if (isSystemCall())
        return std::get<1>(subroutine)->verifyConstant(context, arguments());

    // TODO: implement all rules here
    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    if (!context.pushFrame(symbol, sourceRange.start(), lookupLocation))
        return false;

    bool result = symbol.getBody().verifyConstant(context);
    context.popFrame();
    return result;
}

ConstantValue ConversionExpression::evalImpl(EvalContext& context) const {
    ConstantValue value = operand().eval(context);

    const Type& to = *type;
    if (to.isIntegral())
        return value.convertToInt(to.getBitWidth(), to.isSigned(), to.isFourState());

    if (to.isFloating()) {
        switch (to.getBitWidth()) {
            case 32:
                return value.convertToShortReal();
            case 64:
                return value.convertToReal();
            default:
                THROW_UNREACHABLE;
        }
    }

    if (to.isString())
        return value.convertToStr();

    // TODO: other types
    THROW_UNREACHABLE;
}

bool ConversionExpression::verifyConstantImpl(EvalContext& context) const {
    return operand().verifyConstant(context);
}

ConstantValue DataTypeExpression::evalImpl(EvalContext&) const {
    return nullptr;
}

ConstantValue AssignmentPatternExpressionBase::evalImpl(EvalContext& context) const {
    if (type->isIntegral()) {
        SmallVectorSized<SVInt, 8> values;
        for (auto elem : elements()) {
            ConstantValue v = elem->eval(context);
            if (!v)
                return nullptr;

            values.append(v.integer());
        }

        return SVInt::concat(values);
    }
    else {
        std::vector<ConstantValue> values;
        for (auto elem : elements()) {
            values.emplace_back(elem->eval(context));
            if (values.back().bad())
                return nullptr;
        }

        return values;
    }
}

bool AssignmentPatternExpressionBase::verifyConstantImpl(EvalContext& context) const {
    for (auto elem : elements()) {
        if (!elem->verifyConstant(context))
            return false;
    }
    return true;
}

} // namespace slang