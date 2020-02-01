//------------------------------------------------------------------------------
// MiscSystemFuncs.cpp
// Built-in miscellaneous system functions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/text/SFormat.h"

namespace slang::Builtins {

class SFormatFunction : public SystemSubroutine {
public:
    SFormatFunction() : SystemSubroutine("$sformatf", SubroutineKind::Function) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, INT32_MAX))
            return comp.getErrorType();

        const Type& ft = *args[0]->type;
        if (!ft.canBeStringLike()) {
            context.addDiag(diag::InvalidStringArg, args[0]->sourceRange) << ft;
            return comp.getErrorType();
        }

        if (!checkFormatValues(context, args))
            return comp.getErrorType();

        return comp.getStringType();
    }

    ConstantValue eval(EvalContext& context, const Args& args) const final {
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

    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

class ValuePlusArgsFunction : public SystemSubroutine {
public:
    ValuePlusArgsFunction() : SystemSubroutine("$value$plusargs", SubroutineKind::Function) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, 2))
            return comp.getErrorType();

        const Type& ft = *args[0]->type;
        if (!ft.canBeStringLike()) {
            context.addDiag(diag::InvalidStringArg, args[0]->sourceRange) << ft;
            return comp.getErrorType();
        }

        if (!context.requireLValue(*args[1], args[1]->sourceRange.start()))
            return comp.getErrorType();

        // TODO: if the first argument is known at compile time, do more specific
        // checking of the second argument.
        const Type& st = *args[1]->type;
        if (!st.canBeStringLike() && !st.isFloating())
            return badArg(context, *args[1]);

        return comp.getIntType();
    }

    ConstantValue eval(EvalContext&, const Args&) const final { return nullptr; }
    bool verifyConstant(EvalContext&, const Args&) const final { return false; }
};

void registerMiscSystemFuncs(Compilation& c) {
#define REGISTER(name) c.addSystemSubroutine(std::make_unique<name##Function>())
    REGISTER(SFormat);
    REGISTER(ValuePlusArgs);
#undef REGISTER
}

} // namespace slang::Builtins