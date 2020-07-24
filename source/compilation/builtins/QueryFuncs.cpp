//------------------------------------------------------------------------------
// QueryFuncs.cpp
// Built-in system functions to query data about types and arrays
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/symbols/TypePrinter.h"

namespace slang::Builtins {

class BitsFunction : public SystemSubroutine {
public:
    BitsFunction() : SystemSubroutine("$bits", SubroutineKind::Function) {}

    const Expression& bindArgument(size_t, const BindContext& context,
                                   const ExpressionSyntax& syntax) const final {
        BindContext nonConstCtx = makeNonConst(context);
        return Expression::bind(syntax, nonConstCtx, BindFlags::AllowDataType);
    }

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        if (!args[0]->type->isBitstreamType())
            return badArg(context, *args[0]);

        // TODO: not allowed on some dynamic types

        return comp.getIntegerType();
    }

    ConstantValue eval(const Scope&, EvalContext&, const Args& args) const final {
        // TODO: support for unpacked sizes
        return SVInt(32, args[0]->type->getBitWidth(), true);
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }
};

class TypenameFunction : public SystemSubroutine {
public:
    TypenameFunction() : SystemSubroutine("$typename", SubroutineKind::Function) {}

    const Expression& bindArgument(size_t, const BindContext& context,
                                   const ExpressionSyntax& syntax) const final {
        BindContext nonConstCtx = makeNonConst(context);
        return Expression::bind(syntax, nonConstCtx, BindFlags::AllowDataType);
    }

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        return comp.getStringType();
    }

    ConstantValue eval(const Scope&, EvalContext&, const Args& args) const final {
        TypePrinter printer;
        printer.append(*args[0]->type);

        return printer.toString();
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }
};

class ArrayQueryFunction : public SystemSubroutine {
public:
    using SystemSubroutine::SystemSubroutine;

    const Expression& bindArgument(size_t index, const BindContext& context,
                                   const ExpressionSyntax& syntax) const final {
        BindFlags flags = index == 0 ? BindFlags::AllowDataType : BindFlags::None;
        return Expression::bind(syntax, makeNonConst(context), flags);
    }

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 2))
            return comp.getErrorType();

        auto& type = *args[0]->type;
        if ((!type.isIntegral() && !type.isUnpackedArray() && !type.isString()) || type.isScalar())
            return badArg(context, *args[0]);

        // Spec says we have to disallow this case.
        if (!type.hasFixedRange() && args[0]->kind == ExpressionKind::DataType) {
            context.addDiag(diag::QueryOnDynamicType, args[0]->sourceRange) << name;
            return comp.getErrorType();
        }

        if (args.size() > 1) {
            if (!args[1]->type->isIntegral())
                return badArg(context, *args[1]);

            // Try to verify the dimension index if it's a constant.
            if (!context.inUnevaluatedBranch() && !checkDim(context, args))
                return comp.getErrorType();
        }

        return comp.getIntegerType();
    }

    bool verifyConstant(EvalContext& , const Args& , SourceRange ) const final {
        /*if (!args[0]->type->hasFixedRange()) {
            context.addDiag(diag::DynamicDimensionNotConst, range) << name << *args[0]->type;
            return false;
        }*/

        return true;
    }

protected:
    struct DimResult {
        ConstantRange range;
        bool hardFail = false;
        bool isDynamic = false;
        bool outOfRange = false;

        DimResult() : hardFail(true) {}
        DimResult(ConstantRange range) : range(range) {}
        DimResult(size_t dynamicSize) : range{ 0, int32_t(dynamicSize) - 1 }, isDynamic(true) {}

        static DimResult OutOfRange() {
            DimResult result;
            result.hardFail = false;
            result.outOfRange = true;
            return result;
        }
    };

    static DimResult getDim(EvalContext& context, const Args& args) {
        // If an index expression is provided, evaluate it. Otherwise default to 1.
        ConstantValue iv;
        int32_t index = 1;
        if (args.size() > 1) {
            iv = args[1]->eval(context);
            if (!iv)
                return {};

            optional<int32_t> oi = iv.integer().as<int32_t>();
            if (!oi || *oi <= 0)
                return DimResult::OutOfRange();

            index = *oi;
        }

        // Unwrap each dimension until we reach the right index.
        const Type* type = args[0]->type;
        for (int32_t i = 0; i < index - 1; i++) {
            // If this is not an array, we have nothing to index into
            // and the index we were provided is invalid.
            if (!type->isArray())
                return DimResult::OutOfRange();

            type = type->getArrayElementType();
        }

        // We're pointing at the right dimension, so figure out its range.
        // If fixed size, just return that range.
        if (type->hasFixedRange() && !type->isScalar())
            return type->getFixedRange();

        // Otherwise, this had better be a dynamic array or string.
        if (!type->isString() && !type->isUnpackedArray())
            return DimResult::OutOfRange();

        // This is a dynamically sized thing, so we need to evaluate the expression
        // in order to know its current size. We can only do that if the index is 1
        // because otherwise we won't know which subelement this refers to.
        if (index != 1) {
            context.addDiag(diag::DynamicDimensionIndex, args[0]->sourceRange)
                << iv << args[1]->sourceRange;
            return {};
        }

        ConstantValue cv = args[0]->eval(context);
        if (!cv)
            return {};

        if (cv.isString())
            return cv.str().size();

        return cv.elements().size();
    }

    static bool checkDim(const BindContext& context, const Args& args) {
        // Similar logic to what's above, except we're just verifying a constant index here.
        // It's ok for it not to be constant, it will be evaluated at runtime.
        ConstantValue iv = context.tryEval(*args[1]);
        if (!iv)
            return true;

        auto error = [&] {
            context.addDiag(diag::DimensionIndexInvalid, args[1]->sourceRange)
                << iv << *args[0]->type;
            return false;
        };

        optional<int32_t> index = iv.integer().as<int32_t>();
        if (!index || *index <= 0)
            return error();

        const Type* type = args[0]->type;
        for (int32_t i = 0; i < *index - 1; i++) {
            if (!type->isArray())
                return error();
            type = type->getArrayElementType();
        }

        if (type->hasFixedRange() && !type->isScalar())
            return true;

        if (!type->isString() && !type->isUnpackedArray())
            return error();

        if (*index != 1) {
            context.addDiag(diag::DynamicDimensionIndex, args[0]->sourceRange)
                << iv << args[1]->sourceRange;
            return false;
        }

        return true;
    }
};

#define SUBROUTINE(className, base, ...)                                                      \
    class className : public base {                                                           \
    public:                                                                                   \
        className() : base(__VA_ARGS__) {}                                                    \
        ConstantValue eval(const Scope&, EvalContext& context, const Args& args) const final; \
    }

#define FUNC SubroutineKind::Function

SUBROUTINE(LowFunction, ArrayQueryFunction, "$low", FUNC);
SUBROUTINE(HighFunction, ArrayQueryFunction, "$high", FUNC);
SUBROUTINE(LeftFunction, ArrayQueryFunction, "$left", FUNC);
SUBROUTINE(RightFunction, ArrayQueryFunction, "$right", FUNC);
SUBROUTINE(SizeFunction, ArrayQueryFunction, "$size", FUNC);
SUBROUTINE(IncrementFunction, ArrayQueryFunction, "$increment", FUNC);

ConstantValue LowFunction::eval(const Scope&, EvalContext& context, const Args& args) const {
    DimResult dim = getDim(context, args);
    if (dim.hardFail)
        return nullptr;

    if (dim.outOfRange)
        return SVInt::createFillX(32, true);

    if (dim.isDynamic)
        return SVInt(32, 0, true);

    return SVInt(32, uint64_t(dim.range.lower()), true);
}

ConstantValue HighFunction::eval(const Scope&, EvalContext& context, const Args& args) const {
    DimResult dim = getDim(context, args);
    if (dim.hardFail)
        return nullptr;

    if (dim.outOfRange)
        return SVInt::createFillX(32, true);

    if (dim.isDynamic)
        return SVInt(32, uint64_t(dim.range.right), true);

    return SVInt(32, uint64_t(dim.range.upper()), true);
}

ConstantValue LeftFunction::eval(const Scope&, EvalContext& context, const Args& args) const {
    DimResult dim = getDim(context, args);
    if (dim.hardFail)
        return nullptr;

    if (dim.outOfRange)
        return SVInt::createFillX(32, true);

    return SVInt(32, uint64_t(dim.range.left), true);
}

ConstantValue RightFunction::eval(const Scope&, EvalContext& context, const Args& args) const {
    DimResult dim = getDim(context, args);
    if (dim.hardFail)
        return nullptr;

    if (dim.outOfRange)
        return SVInt::createFillX(32, true);

    return SVInt(32, uint64_t(dim.range.right), true);
}

ConstantValue SizeFunction::eval(const Scope&, EvalContext& context, const Args& args) const {
    DimResult dim = getDim(context, args);
    if (dim.hardFail)
        return nullptr;

    if (dim.outOfRange)
        return SVInt::createFillX(32, true);

    if (dim.isDynamic)
        return SVInt(32, uint64_t(dim.range.right + 1), true);

    return SVInt(32, dim.range.width(), true);
}

ConstantValue IncrementFunction::eval(const Scope&, EvalContext& context, const Args& args) const {
    DimResult dim = getDim(context, args);
    if (dim.hardFail)
        return nullptr;

    if (dim.outOfRange)
        return SVInt::createFillX(32, true);

    if (dim.isDynamic)
        return SVInt(32, uint64_t(-1), true);

    return SVInt(32, uint64_t(dim.range.isLittleEndian() ? 1 : -1), true);
}

void registerQueryFuncs(Compilation& c) {
#define REGISTER(name) c.addSystemSubroutine(std::make_unique<name##Function>())
    REGISTER(Bits);
    REGISTER(Typename);
    REGISTER(Low);
    REGISTER(High);
    REGISTER(Left);
    REGISTER(Right);
    REGISTER(Size);
    REGISTER(Increment);
#undef REGISTER
}

} // namespace slang::Builtins