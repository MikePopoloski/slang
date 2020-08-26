//------------------------------------------------------------------------------
// QueryFuncs.cpp
// Built-in system functions to query data about types and arrays
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/symbols/TypePrinter.h"

namespace slang::Builtins {

class BitsFunction : public SystemSubroutine {
public:
    BitsFunction() : SystemSubroutine("$bits", SubroutineKind::Function) {}

    const Expression& bindArgument(size_t, const BindContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
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

        if (args[0]->kind == ExpressionKind::DataType && !args[0]->type->isFixedSize()) {
            auto& diag = context.addDiag(diag::QueryOnDynamicType, args[0]->sourceRange) << name;
            if (args[0]->type->location)
                diag.addNote(diag::NoteDeclarationHere, args[0]->type->location);
            return comp.getErrorType();
        }
        return comp.getIntegerType();
    }

    ConstantValue eval(const Scope&, EvalContext& context, const Args& args) const final {
        auto width = args[0]->type->bitstreamWidth();
        if (!width) {
            if (args[0]->kind == ExpressionKind::DataType) {
                auto& diag = context.addDiag(diag::ConstEvalBitsNotFixedSize, args[0]->sourceRange);
                diag << *args[0]->type;
                return nullptr;
            }
            else {
                ConstantValue cv = args[0]->eval(context);
                if (!cv)
                    return nullptr;
                width = cv.bitstreamWidth();
            }
        }

        // TODO: width > INT_MAX
        return SVInt(32, width, true);
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }
};

class TypenameFunction : public SystemSubroutine {
public:
    TypenameFunction() : SystemSubroutine("$typename", SubroutineKind::Function) {}

    const Expression& bindArgument(size_t, const BindContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
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
                                   const ExpressionSyntax& syntax, const Args&) const final {
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

        int32_t knownIndex = 0;
        if (args.size() > 1) {
            if (!args[1]->type->isIntegral())
                return badArg(context, *args[1]);

            // Try to verify the dimension index if it's a constant.
            if (!context.inUnevaluatedBranch() && !checkDim(context, args, knownIndex))
                return comp.getErrorType();
        }
        else {
            // Index defaults to 1 if not provided.
            knownIndex = 1;
        }

        if (type.isAssociativeArray()) {
            // If the first argument is an associative array and we know we're selecting it,
            // ensure that the index type is integral.
            auto indexType = type.getAssociativeIndexType();
            if (knownIndex && (!indexType || !indexType->isIntegral())) {
                context.addDiag(diag::QueryOnAssociativeWildcard, args[0]->sourceRange) << name;
                return comp.getErrorType();
            }

            // If the index is known, the result type is the index type.
            if (knownIndex)
                return *indexType;

            // If the index is unknown, we don't know if they will select the associative array
            // or some other dimension. Use the index type if it's larger than a normal integer,
            // and otherwise just use an integer result type.
            if (indexType->getBitWidth() > 32)
                return *indexType;
        }

        return comp.getIntegerType();
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }

protected:
    struct DimResult {
        AssociativeArray map;
        const Type* indexType = nullptr;
        ConstantRange range;
        bool hardFail = false;
        bool isDynamic = false;
        bool outOfRange = false;

        DimResult() : hardFail(true) {}
        DimResult(ConstantRange range) : range(range) {}
        DimResult(size_t dynamicSize) : range{ 0, int32_t(dynamicSize) - 1 }, isDynamic(true) {}
        DimResult(AssociativeArray&& map, const Type* indexType) :
            map(std::move(map)), indexType(indexType) {}

        static DimResult OutOfRange() {
            DimResult result;
            result.hardFail = false;
            result.outOfRange = true;
            return result;
        }
    };

    DimResult getDim(EvalContext& context, const Args& args) const {
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

        // This only works on associative arrays if they have an integral index type.
        const Type* indexType = nullptr;
        if (type->isAssociativeArray()) {
            indexType = type->getAssociativeIndexType();
            if (!indexType || !indexType->isIntegral()) {
                context.addDiag(diag::QueryOnAssociativeWildcard, args[0]->sourceRange) << name;
                return {};
            }
        }

        ConstantValue cv = args[0]->eval(context);
        if (!cv)
            return {};

        if (cv.isString())
            return cv.str().size();

        // This silly collection of std::moves is to avoid copying the array out
        // when the constant value owning it will not survive this function.
        if (cv.isMap())
            return DimResult(std::move(*std::move(cv).map()), indexType);

        return cv.size();
    }

    static bool checkDim(const BindContext& context, const Args& args, int32_t& resultIndex) {
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

        resultIndex = *index;
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

    // For associative arrays, $low returns the first key, or 'x if no elements.
    if (dim.indexType) {
        if (dim.map.empty())
            return SVInt::createFillX(dim.indexType->getBitWidth(), dim.indexType->isSigned());
        return dim.map.begin()->first;
    }

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

    // For associative arrays, $high returns the last key, or 'x if no elements.
    if (dim.indexType) {
        if (dim.map.empty())
            return SVInt::createFillX(dim.indexType->getBitWidth(), dim.indexType->isSigned());
        return dim.map.rbegin()->first;
    }

    return SVInt(32, uint64_t(dim.range.upper()), true);
}

ConstantValue LeftFunction::eval(const Scope&, EvalContext& context, const Args& args) const {
    DimResult dim = getDim(context, args);
    if (dim.hardFail)
        return nullptr;

    if (dim.outOfRange)
        return SVInt::createFillX(32, true);

    if (dim.indexType)
        return SVInt(dim.indexType->getBitWidth(), 0, dim.indexType->isSigned());

    return SVInt(32, uint64_t(dim.range.left), true);
}

ConstantValue RightFunction::eval(const Scope&, EvalContext& context, const Args& args) const {
    DimResult dim = getDim(context, args);
    if (dim.hardFail)
        return nullptr;

    if (dim.outOfRange)
        return SVInt::createFillX(32, true);

    // For associative arrays, $right returns maximum possible index value.
    if (dim.indexType) {
        SVInt result(dim.indexType->getBitWidth(), 0, dim.indexType->isSigned());
        result.setAllOnes();
        return result;
    }

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

    if (dim.indexType)
        return SVInt(dim.indexType->getBitWidth(), dim.map.size(), dim.indexType->isSigned());

    return SVInt(32, dim.range.width(), true);
}

ConstantValue IncrementFunction::eval(const Scope&, EvalContext& context, const Args& args) const {
    DimResult dim = getDim(context, args);
    if (dim.hardFail)
        return nullptr;

    if (dim.outOfRange)
        return SVInt::createFillX(32, true);

    if (dim.isDynamic || dim.indexType)
        return SVInt(32, uint64_t(-1), true);

    return SVInt(32, uint64_t(dim.range.isLittleEndian() ? 1 : -1), true);
}

class ArrayDimensionFunction : public SystemSubroutine {
public:
    ArrayDimensionFunction(const std::string& name, bool unpackedOnly) :
        SystemSubroutine(name, FUNC), unpackedOnly(unpackedOnly) {}

    const Expression& bindArgument(size_t, const BindContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        return Expression::bind(syntax, makeNonConst(context), BindFlags::AllowDataType);
    }

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        auto& type = *args[0]->type;
        if (!type.isIntegral() && !type.isUnpackedArray() && !type.isString())
            return badArg(context, *args[0]);

        // Spec says we have to disallow this case.
        if (!type.hasFixedRange() && args[0]->kind == ExpressionKind::DataType) {
            context.addDiag(diag::QueryOnDynamicType, args[0]->sourceRange) << name;
            return comp.getErrorType();
        }

        return comp.getIntegerType();
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }

    ConstantValue eval(const Scope&, EvalContext&, const Args& args) const final {
        // Count the number of dimensions by unwrapping arrays.
        uint64_t count = 0;
        const Type* type = args[0]->type;
        while (type->isArray()) {
            if (unpackedOnly && !type->isUnpackedArray())
                break;

            count++;
            type = type->getArrayElementType();
        }

        // Strings and simple bit vectors count as a (packed) dimension.
        if (!unpackedOnly && (type->isString() || (type->isIntegral() && !type->isScalar()))) {
            count++;
        }

        return SVInt(32, count, true);
    }

private:
    bool unpackedOnly;
};

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

    c.addSystemSubroutine(std::make_unique<ArrayDimensionFunction>("$dimensions", false));
    c.addSystemSubroutine(std::make_unique<ArrayDimensionFunction>("$unpacked_dimensions", true));
}

} // namespace slang::Builtins
