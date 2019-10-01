//------------------------------------------------------------------------------
// BuiltInSubroutines.cpp
// Built-in system subroutine handlers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "BuiltInSubroutines.h"

#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/text/SFormat.h"

namespace slang::Builtins {

const Type& IntegerMathFunction::checkArguments(const BindContext& context, const Args& args,
                                                SourceRange range) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, false, args, range, 1, 1))
        return comp.getErrorType();

    if (!args[0]->type->isIntegral()) {
        context.addDiag(diag::BadSystemSubroutineArg, args[0]->sourceRange)
            << *args[0]->type << kindStr();
        return comp.getErrorType();
    }

    return comp.getIntegerType();
}

const Type& DataQueryFunction::checkArguments(const BindContext& context, const Args& args,
                                              SourceRange range) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, false, args, range, 1, 1))
        return comp.getErrorType();

    if (!args[0]->type->isBitstreamType()) {
        context.addDiag(diag::BadSystemSubroutineArg, args[0]->sourceRange)
            << *args[0]->type << kindStr();
        return comp.getErrorType();
    }

    // TODO: not allowed on some dynamic types

    return comp.getIntegerType();
}

const Type& ArrayQueryFunction::checkArguments(const BindContext& context, const Args& args,
                                               SourceRange range) const {
    // TODO: support optional second argument
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, false, args, range, 1, 1))
        return comp.getErrorType();

    auto& type = *args[0]->type;
    if (!type.isIntegral() && !type.isUnpackedArray()) {
        context.addDiag(diag::BadSystemSubroutineArg, args[0]->sourceRange) << type << kindStr();
        return comp.getErrorType();
    }

    // TODO: not allowed on some dynamic types

    return comp.getIntegerType();
}

SFormatFunction::SFormatFunction() : SystemSubroutine("$sformatf", SubroutineKind::Function) {
}

const Type& SFormatFunction::checkArguments(const BindContext& context, const Args& args,
                                            SourceRange range) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, false, args, range, 1, INT32_MAX))
        return comp.getErrorType();

    const Type& ft = *args[0]->type;
    if (!ft.isIntegral() && !ft.isString() && !ft.isByteArray()) {
        context.addDiag(diag::InvalidFormatStringType, args[0]->sourceRange) << *args[0]->type;
        return comp.getErrorType();
    }

    // If the format string is known at compile time, check it for correctness now.
    if (args[0]->constant) {
        ConstantValue formatStr = args[0]->constant->convertToStr();
        if (formatStr) {
            Diagnostics diags;
            SmallVectorSized<SFormat::Arg, 8> specs;
            if (!SFormat::parseArgs(formatStr.str(), args[0]->sourceRange.start(), specs, diags)) {
                context.scope.addDiags(diags);
                return comp.getErrorType();
            }

            // TODO: check the rest of the args as well
        }
    }

    return comp.getStringType();
}

ConstantValue SFormatFunction::eval(EvalContext& context, const Args& args) const {
    ConstantValue formatStr = args[0]->eval(context).convertToStr();
    if (!formatStr)
        return nullptr;

    SmallVectorSized<SFormat::TypedValue, 8> values;
    for (auto arg : args.subspan(1)) {
        auto&& value = arg->eval(context);
        if (!value)
            return nullptr;

        values.emplace(std::move(value), arg->type, arg->sourceRange);
    }

    Diagnostics diags;
    auto result = SFormat::format(formatStr.str(), args[0]->sourceRange.start(), values,
                                  context.getCurrentScope(), diags);
    if (!diags.empty())
        context.addDiags(diags);

    if (!result)
        return nullptr;

    return *result;
}

const Type& DisplayTask::checkArguments(const BindContext& context, const Args& args,
                                        SourceRange) const {
    auto& comp = context.getCompilation();
    if (!checkFormatArgs(context, args))
        return comp.getErrorType();

    return comp.getVoidType();
}

const Type& SimpleControlTask::checkArguments(const BindContext& context, const Args& args,
                                              SourceRange range) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, false, args, range, 0, 0))
        return comp.getErrorType();

    return comp.getVoidType();
}

const Type& FinishControlTask::checkArguments(const BindContext& context, const Args& args,
                                              SourceRange range) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, false, args, range, 0, 1))
        return comp.getErrorType();

    // TODO: check optional first arg

    return comp.getVoidType();
}

const Type& FatalTask::checkArguments(const BindContext& context, const Args& args,
                                      SourceRange) const {
    auto& comp = context.getCompilation();
    if (!args.empty()) {
        // TODO: check finish number
        if (args[0]->bad())
            return comp.getErrorType();

        if (!checkFormatArgs(context, args.subspan(1)))
            return comp.getErrorType();
    }

    return comp.getVoidType();
}

const Type& NonConstantFunction::checkArguments(const BindContext& context, const Args& args,
                                                SourceRange range) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, false, args, range, 0, 0))
        return comp.getErrorType();

    return returnType;
}

ConstantValue Clog2Function::eval(EvalContext& context, const Args& args) const {
    ConstantValue v = args[0]->eval(context);
    if (!v)
        return nullptr;

    return SVInt(32, clog2(v.integer()), true);
}

ConstantValue BitsFunction::eval(EvalContext&, const Args& args) const {
    // TODO: support for unpacked sizes
    return SVInt(32, args[0]->type->getBitWidth(), true);
}

ConstantValue LowFunction::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)range.lower(), true);
}

ConstantValue HighFunction::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)range.upper(), true);
}

ConstantValue LeftFunction::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)range.left, true);
}

ConstantValue RightFunction::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)range.right, true);
}

ConstantValue SizeFunction::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, range.width(), true);
}

ConstantValue IncrementFunction::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)(range.isLittleEndian() ? 1 : -1), true);
}

EnumFirstLastMethod::EnumFirstLastMethod(const std::string& name, bool first) :
    SystemSubroutine(name, SubroutineKind::Function), first(first) {
}

const Type& EnumFirstLastMethod::checkArguments(const BindContext& context, const Args& args,
                                                SourceRange range) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, true, args, range, 0, 0))
        return comp.getErrorType();

    return *args.at(0)->type;
}

ConstantValue EnumFirstLastMethod::eval(EvalContext&, const Args& args) const {
    // Expression isn't actually evaluated here; we know the value to return at compile time.
    const EnumType& type = args.at(0)->type->getCanonicalType().as<EnumType>();

    auto range = type.values();
    if (range.begin() == range.end())
        return nullptr;

    const EnumValueSymbol* value;
    if (first) {
        value = &*range.begin();
    }
    else {
        for (auto it = range.begin();;) {
            auto prev = it++;
            if (it == range.end()) {
                value = &*prev;
                break;
            }
        }
    }

    return value->getValue();
}

const Type& EnumNumMethod::checkArguments(const BindContext& context, const Args& args,
                                          SourceRange range) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, true, args, range, 0, 0))
        return comp.getErrorType();

    return comp.getIntegerType();
}

ConstantValue EnumNumMethod::eval(EvalContext&, const Args& args) const {
    // Expression isn't actually evaluated here; we know the value to return at compile time.
    const EnumType& type = args.at(0)->type->getCanonicalType().as<EnumType>();
    return SVInt(32, (uint64_t)type.values().size(), true);
}

const Type& ArrayReductionMethod::checkArguments(const BindContext& context, const Args& args,
                                                 SourceRange range) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, true, args, range, 0, 0))
        return comp.getErrorType();

    auto& type = *args[0]->type;
    ASSERT(type.isUnpackedArray());

    auto& elemType = type.getCanonicalType().as<UnpackedArrayType>().elementType;
    if (!elemType.isIntegral()) {
        context.addDiag(diag::ArrayReductionIntegral, args[0]->sourceRange);
        return comp.getErrorType();
    }

    return elemType;
}

#define MAKE_REDUCTION_METHOD(typeName, sourceName, op)                          \
    class Array##typeName##Method : public ArrayReductionMethod {                \
    public:                                                                      \
        Array##typeName##Method() : ArrayReductionMethod(sourceName) {}          \
                                                                                 \
        ConstantValue eval(EvalContext& context, const Args& args) const final { \
            ConstantValue arr = args[0]->eval(context);                          \
            if (!arr)                                                            \
                return nullptr;                                                  \
                                                                                 \
            SVInt result = arr.elements()[0].integer();                          \
            for (auto& elem : arr.elements().subspan(1))                         \
                result op elem.integer();                                        \
                                                                                 \
            return result;                                                       \
        }                                                                        \
    };

MAKE_REDUCTION_METHOD(Or, "or", |=)
MAKE_REDUCTION_METHOD(And, "and", &=)
MAKE_REDUCTION_METHOD(Xor, "xor", ^=)

#undef MAKE_REDUCTION_METHOD

void registerAll(Compilation& c) {
#define REGISTER(name) c.addSystemSubroutine(std::make_unique<name##Function>())
    REGISTER(Clog2);
    REGISTER(Bits);
    REGISTER(Low);
    REGISTER(High);
    REGISTER(Left);
    REGISTER(Right);
    REGISTER(Size);
    REGISTER(Increment);
    REGISTER(SFormat);
#undef REGISTER

#define REGISTER(type, name) c.addSystemSubroutine(std::make_unique<type>(name))
    REGISTER(DisplayTask, "$display");
    REGISTER(DisplayTask, "$displayb");
    REGISTER(DisplayTask, "$displayo");
    REGISTER(DisplayTask, "$displayh");
    REGISTER(DisplayTask, "$write");
    REGISTER(DisplayTask, "$writeb");
    REGISTER(DisplayTask, "$writeo");
    REGISTER(DisplayTask, "$writeh");
    REGISTER(DisplayTask, "$strobe");
    REGISTER(DisplayTask, "$strobeb");
    REGISTER(DisplayTask, "$strobeo");
    REGISTER(DisplayTask, "$strobeh");
    REGISTER(DisplayTask, "$monitor");
    REGISTER(DisplayTask, "$monitorb");
    REGISTER(DisplayTask, "$monitoro");
    REGISTER(DisplayTask, "$monitorh");

    REGISTER(DisplayTask, "$error");
    REGISTER(DisplayTask, "$warning");
    REGISTER(DisplayTask, "$info");

    REGISTER(FatalTask, "$fatal");

    REGISTER(FinishControlTask, "$finish");
    REGISTER(FinishControlTask, "$stop");

    REGISTER(SimpleControlTask, "$exit");
    REGISTER(SimpleControlTask, "$monitoron");
    REGISTER(SimpleControlTask, "$monitoroff");
#undef REGISTER

#define REGISTER(name, returnType) \
    c.addSystemSubroutine(std::make_unique<NonConstantFunction>(name, returnType))

    auto& uintType = c.getType(32, IntegralFlags::Unsigned);
    REGISTER("$time", c.getTimeType());
    REGISTER("$stime", uintType);
    REGISTER("$realtime", c.getRealTimeType());

    // TODO: optional argument to random functions
    REGISTER("$random", c.getIntType());
    REGISTER("$urandom", uintType);

#undef REGISTER

#define REGISTER(kind, name, ...) \
    c.addSystemMethod(kind, std::make_unique<name##Method>(__VA_ARGS__))
    REGISTER(SymbolKind::EnumType, EnumFirstLast, "first", true);
    REGISTER(SymbolKind::EnumType, EnumFirstLast, "last", false);
    REGISTER(SymbolKind::EnumType, EnumNum, );
    REGISTER(SymbolKind::UnpackedArrayType, ArrayOr, );
    REGISTER(SymbolKind::UnpackedArrayType, ArrayAnd, );
    REGISTER(SymbolKind::UnpackedArrayType, ArrayXor, );
#undef REGISTER
}

} // namespace slang::Builtins