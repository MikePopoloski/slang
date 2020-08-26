//------------------------------------------------------------------------------
// MiscSystemFuncs.cpp
// Built-in miscellaneous system functions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/FormatHelpers.h"
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"

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

        if (!FmtHelpers::checkSFormatArgs(context, args))
            return comp.getErrorType();

        return comp.getStringType();
    }

    ConstantValue eval(const Scope& scope, EvalContext& context, const Args& args) const final {
        ConstantValue formatStr = args[0]->eval(context).convertToStr();
        if (!formatStr)
            return nullptr;

        auto result = FmtHelpers::formatArgs(formatStr.str(), args[0]->sourceRange.start(), scope,
                                             context, args.subspan(1));
        if (!result)
            return nullptr;

        return *result;
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }
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

        if (!args[1]->verifyAssignable(context))
            return comp.getErrorType();

        // TODO: if the first argument is known at compile time, do more specific
        // checking of the second argument.
        const Type& st = *args[1]->type;
        if (!st.canBeStringLike() && !st.isFloating())
            return badArg(context, *args[1]);

        return comp.getIntType();
    }

    ConstantValue eval(const Scope&, EvalContext&, const Args&) const final { return nullptr; }
    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }
};

void registerMiscSystemFuncs(Compilation& c) {
#define REGISTER(name) c.addSystemSubroutine(std::make_unique<name##Function>())
    REGISTER(SFormat);
    REGISTER(ValuePlusArgs);
#undef REGISTER
}

} // namespace slang::Builtins
