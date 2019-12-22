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

class Clog2Function : public SystemSubroutine {
public:
    Clog2Function() : SystemSubroutine("$clog2", SubroutineKind::Function) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        if (!args[0]->type->isIntegral())
            return badArg(context, *args[0]);

        return comp.getIntegerType();
    }

    bool verifyConstant(EvalContext&, const Args&) const final { return true; }

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        ConstantValue v = args[0]->eval(context);
        if (!v)
            return nullptr;

        return SVInt(32, clog2(v.integer()), true);
    }
};

template<double Func(double)>
class RealMath1Function : public SimpleSystemSubroutine {
public:
    RealMath1Function(Compilation& comp, const std::string& name) :
        SimpleSystemSubroutine(name, SubroutineKind::Function, 1, { &comp.getRealType() },
                               comp.getRealType(), false) {}

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        ConstantValue v = args[0]->eval(context);
        if (!v)
            return nullptr;

        double result = Func(v.real());
        return real_t(result);
    }
};

template<double Func(double, double)>
class RealMath2Function : public SimpleSystemSubroutine {
public:
    RealMath2Function(Compilation& comp, const std::string& name) :
        SimpleSystemSubroutine(name, SubroutineKind::Function, 2,
                               { &comp.getRealType(), &comp.getRealType() }, comp.getRealType(),
                               false) {}

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        ConstantValue a = args[0]->eval(context);
        ConstantValue b = args[1]->eval(context);
        if (!a || !b)
            return nullptr;

        double result = Func(a.real(), b.real());
        return real_t(result);
    }
};

void registerMathFuncs(Compilation& c) {
    c.addSystemSubroutine(std::make_unique<Clog2Function>());

#define REGISTER(name, func) \
    c.addSystemSubroutine(std::make_unique<RealMath1Function<(func)>>(c, name))

    REGISTER("$ln", std::log);
    REGISTER("$log10", std::log10);
    REGISTER("$exp", std::exp);
    REGISTER("$sqrt", std::sqrt);
    REGISTER("$floor", std::floor);
    REGISTER("$ceil", std::ceil);
    REGISTER("$sin", std::sin);
    REGISTER("$cos", std::cos);
    REGISTER("$tan", std::tan);
    REGISTER("$asin", std::asin);
    REGISTER("$acos", std::acos);
    REGISTER("$atan", std::atan);
    REGISTER("$sinh", std::sinh);
    REGISTER("$cosh", std::cosh);
    REGISTER("$tanh", std::tanh);
    REGISTER("$asinh", std::asinh);
    REGISTER("$acosh", std::acosh);
    REGISTER("$atanh", std::atanh);

#undef REGISTER
#define REGISTER(name, func) \
    c.addSystemSubroutine(std::make_unique<RealMath2Function<(func)>>(c, name))

    REGISTER("$pow", std::pow);
    REGISTER("$atan2", std::atan2);
    REGISTER("$hypot", std::hypot);

#undef REGISTER
}

} // namespace slang::Builtins