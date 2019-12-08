//------------------------------------------------------------------------------
// MiscSystemFuncs.cpp
// Built-in miscellaneous system functions.
//
// File is under the MIT license; see LICENSE for details.
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
        if (!ft.isIntegral() && !ft.isString() && !ft.isByteArray()) {
            context.addDiag(diag::InvalidStringArg, args[0]->sourceRange) << *args[0]->type;
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

void registerMiscSystemFuncs(Compilation& c) {
#define REGISTER(name) c.addSystemSubroutine(std::make_unique<name##Function>())
    REGISTER(SFormat);
#undef REGISTER
}

} // namespace slang::Builtins