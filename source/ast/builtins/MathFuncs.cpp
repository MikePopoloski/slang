//------------------------------------------------------------------------------
// MathFuncs.cpp
// Built-in math system functions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "Builtins.h"
#include <cmath>

#include "slang/ast/Bitstream.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/types/Type.h"

namespace slang::ast::builtins {

class Clog2Function : public SystemSubroutine {
public:
    Clog2Function() : SystemSubroutine(KnownSystemName::Clog2, SubroutineKind::Function) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        if (!args[0]->type->isIntegral())
            return badArg(context, *args[0]);

        return comp.getIntegerType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        ConstantValue v = args[0]->eval(context);
        if (!v)
            return nullptr;

        auto ci = v.integer();
        ci.flattenUnknowns();
        return SVInt(32, clog2(ci), true);
    }
};

class CountBitsFunction : public SystemSubroutine {
public:
    CountBitsFunction() : SystemSubroutine(KnownSystemName::CountBits, SubroutineKind::Function) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, INT32_MAX))
            return comp.getErrorType();

        if (!args[0]->type->isBitstreamType())
            return badArg(context, *args[0]);

        if (!Bitstream::checkClassAccess(*args[0]->type, context, args[0]->sourceRange))
            return comp.getErrorType();

        for (auto arg : args.subspan(1)) {
            if (!arg->type->isIntegral())
                return badArg(context, *arg);
        }

        return comp.getIntType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        auto value = Bitstream::convertToBitVector(args[0]->eval(context), range, context);
        if (!value)
            return nullptr;

        // Figure out which bit values we're checking -- the caller can
        // pass any number of arguments; we always take the LSB and compare
        // that against all bits, counting each one that matches.
        //
        // This array tracks which bit values we've already counted: 0, 1, X, or Z
        bool seen[4]{};
        uint64_t count = 0;
        const SVInt& iv = value.integer();

        for (auto arg : args.subspan(1)) {
            ConstantValue v = arg->eval(context);
            if (!v)
                return nullptr;

            logic_t bit = v.integer()[0];
            if (bit.value == 0) {
                if (!seen[0]) {
                    count += iv.countZeros();
                    seen[0] = true;
                }
            }
            else if (bit.value == 1) {
                if (!seen[1]) {
                    count += iv.countOnes();
                    seen[1] = true;
                }
            }
            else if (bit.value == logic_t::X_VALUE) {
                if (!seen[2]) {
                    count += iv.countXs();
                    seen[2] = true;
                }
            }
            else if (bit.value == logic_t::Z_VALUE) {
                if (!seen[3]) {
                    count += iv.countZs();
                    seen[3] = true;
                }
            }
        }

        return SVInt(32, count, true);
    }
};

class CountOnesFunction : public SystemSubroutine {
public:
    CountOnesFunction() : SystemSubroutine(KnownSystemName::CountOnes, SubroutineKind::Function) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        if (!args[0]->type->isBitstreamType())
            return badArg(context, *args[0]);

        if (!Bitstream::checkClassAccess(*args[0]->type, context, args[0]->sourceRange))
            return comp.getErrorType();

        return comp.getIntType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        auto value = Bitstream::convertToBitVector(args[0]->eval(context), range, context);
        if (!value)
            return nullptr;

        const SVInt& iv = value.integer();
        uint64_t count = iv.countOnes();
        return SVInt(32, count, true);
    }
};

class BooleanBitVectorFunction : public SystemSubroutine {
public:
    enum BVFKind { OneHot, OneHot0, IsUnknown };

    BooleanBitVectorFunction(KnownSystemName knownNameId, BVFKind kind) :
        SystemSubroutine(knownNameId, SubroutineKind::Function), kind(kind) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        if (!args[0]->type->isBitstreamType())
            return badArg(context, *args[0]);

        if (!Bitstream::checkClassAccess(*args[0]->type, context, args[0]->sourceRange))
            return comp.getErrorType();

        return comp.getBitType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        auto value = Bitstream::convertToBitVector(args[0]->eval(context), range, context);
        if (!value)
            return nullptr;

        const SVInt& iv = value.integer();
        switch (kind) {
            case OneHot:
                return SVInt(1, uint64_t(iv.countOnes() == 1), false);
            case OneHot0:
                return SVInt(1, uint64_t(iv.countOnes() <= 1), false);
            case IsUnknown:
                return SVInt(1, uint64_t(iv.hasUnknown()), false);
        }
        SLANG_UNREACHABLE;
    }

private:
    BVFKind kind;
};

template<double Func(double)>
class RealMath1Function : public SimpleSystemSubroutine {
public:
    RealMath1Function(const Builtins& builtins, KnownSystemName knownNameId) :
        SimpleSystemSubroutine(knownNameId, SubroutineKind::Function, 1, {&builtins.realType},
                               builtins.realType, false) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
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
    RealMath2Function(const Builtins& builtins, KnownSystemName knownNameId) :
        SimpleSystemSubroutine(knownNameId, SubroutineKind::Function, 2,
                               {&builtins.realType, &builtins.realType}, builtins.realType, false) {
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        ConstantValue a = args[0]->eval(context);
        ConstantValue b = args[1]->eval(context);
        if (!a || !b)
            return nullptr;

        double result = Func(a.real(), b.real());
        return real_t(result);
    }
};

void Builtins::registerMathFuncs() {
    using parsing::KnownSystemName;

    addSystemSubroutine(std::make_shared<Clog2Function>());
    addSystemSubroutine(std::make_shared<CountBitsFunction>());
    addSystemSubroutine(std::make_shared<CountOnesFunction>());

#define REGISTER(name, kind) \
    addSystemSubroutine(     \
        std::make_shared<BooleanBitVectorFunction>(name, BooleanBitVectorFunction::kind))

    REGISTER(KnownSystemName::OneHot, OneHot);
    REGISTER(KnownSystemName::OneHot0, OneHot0);
    REGISTER(KnownSystemName::IsUnknown, IsUnknown);

#undef REGISTER
#define REGISTER(name, func) \
    addSystemSubroutine(std::make_shared<RealMath1Function<(func)>>(*this, name))

    REGISTER(KnownSystemName::Ln, std::log);
    REGISTER(KnownSystemName::Log10, std::log10);
    REGISTER(KnownSystemName::Exp, std::exp);
    REGISTER(KnownSystemName::Sqrt, std::sqrt);
    REGISTER(KnownSystemName::Floor, std::floor);
    REGISTER(KnownSystemName::Ceil, std::ceil);
    REGISTER(KnownSystemName::Sin, std::sin);
    REGISTER(KnownSystemName::Cos, std::cos);
    REGISTER(KnownSystemName::Tan, std::tan);
    REGISTER(KnownSystemName::Asin, std::asin);
    REGISTER(KnownSystemName::Acos, std::acos);
    REGISTER(KnownSystemName::Atan, std::atan);
    REGISTER(KnownSystemName::Sinh, std::sinh);
    REGISTER(KnownSystemName::Cosh, std::cosh);
    REGISTER(KnownSystemName::Tanh, std::tanh);
    REGISTER(KnownSystemName::Asinh, std::asinh);
    REGISTER(KnownSystemName::Acosh, std::acosh);
    REGISTER(KnownSystemName::Atanh, std::atanh);

#undef REGISTER
#define REGISTER(name, func) \
    addSystemSubroutine(std::make_shared<RealMath2Function<(func)>>(*this, name))

    REGISTER(KnownSystemName::Pow, std::pow);
    REGISTER(KnownSystemName::Atan2, std::atan2);
    REGISTER(KnownSystemName::Hypot, std::hypot);

#undef REGISTER
}

} // namespace slang::ast::builtins
