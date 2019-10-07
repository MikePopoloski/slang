//------------------------------------------------------------------------------
// MathFuncs.cpp
// Built-in math system functions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"

namespace slang::Builtins {

class IntegerMathFunction : public SystemSubroutine {
public:
    using SystemSubroutine::SystemSubroutine;

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
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

    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

#define SUBROUTINE(className, base, ...)                                        \
    class className : public base {                                             \
    public:                                                                     \
        className() : base(__VA_ARGS__) {}                                      \
        ConstantValue eval(EvalContext& context, const Args& args) const final; \
    }

#define FUNC SubroutineKind::Function
SUBROUTINE(Clog2Function, IntegerMathFunction, "$clog2", FUNC);

ConstantValue Clog2Function::eval(EvalContext& context, const Args& args) const {
    ConstantValue v = args[0]->eval(context);
    if (!v)
        return nullptr;

    return SVInt(32, clog2(v.integer()), true);
}

void registerMathFuncs(Compilation& c) {
#define REGISTER(name) c.addSystemSubroutine(std::make_unique<name##Function>())
    REGISTER(Clog2);
#undef REGISTER
}

} // namespace slang::Builtins