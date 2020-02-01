//------------------------------------------------------------------------------
// ConversionFuncs.cpp
// Built-in conversion system functions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"

namespace slang::Builtins {

class SignedConversionFunction : public SystemSubroutine {
public:
    SignedConversionFunction(const std::string& name, bool toSigned) :
        SystemSubroutine(name, SubroutineKind::Function), toSigned(toSigned) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        auto& type = *args[0]->type;
        if (!type.isIntegral())
            return badArg(context, *args[0]);

        auto flags = type.getIntegralFlags() & ~IntegralFlags::Signed;
        if (toSigned)
            flags |= IntegralFlags::Signed;

        return comp.getType(type.getBitWidth(), flags);
    }

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        const Type& to = *args[0]->type;
        return val.convertToInt(to.getBitWidth(), toSigned, to.isFourState());
    }

    bool verifyConstant(EvalContext&, const Args&) const final { return true; }

private:
    bool toSigned;
};

class RtoIFunction : public SimpleSystemSubroutine {
public:
    RtoIFunction(Compilation& comp) :
        SimpleSystemSubroutine("$rtoi", SubroutineKind::Function, 1, { &comp.getRealType() },
                               comp.getIntegerType(), false) {}

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        return SVInt(32, (uint64_t)val.real(), true);
    }
};

class ItoRFunction : public SimpleSystemSubroutine {
public:
    ItoRFunction(Compilation& comp) :
        SimpleSystemSubroutine("$itor", SubroutineKind::Function, 1, { &comp.getIntegerType() },
                               comp.getRealType(), false) {}

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        int32_t i = val.integer().as<int32_t>().value_or(0);
        return real_t(double(i));
    }
};

class RealToBitsFunction : public SimpleSystemSubroutine {
public:
    RealToBitsFunction(Compilation& comp) :
        SimpleSystemSubroutine("$realtobits", SubroutineKind::Function, 1, { &comp.getRealType() },
                               comp.getType(64, IntegralFlags::Unsigned), false) {}

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        // TODO: bit_cast
        double d = val.real();
        uint64_t result;
        memcpy(&result, &d, sizeof(uint64_t));
        return SVInt(64, result, false);
    }
};

class BitsToRealFunction : public SimpleSystemSubroutine {
public:
    BitsToRealFunction(Compilation& comp) :
        SimpleSystemSubroutine("$bitstoreal", SubroutineKind::Function, 1,
                               { &comp.getType(64, IntegralFlags::Unsigned) }, comp.getRealType(),
                               false) {}

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        // TODO: bit_cast
        uint64_t i = val.integer().as<uint64_t>().value_or(0);
        double result;
        memcpy(&result, &i, sizeof(double));

        return real_t(result);
    }
};

class ShortRealToBitsFunction : public SimpleSystemSubroutine {
public:
    ShortRealToBitsFunction(Compilation& comp) :
        SimpleSystemSubroutine("$shortrealtobits", SubroutineKind::Function, 1,
                               { &comp.getShortRealType() },
                               comp.getType(32, IntegralFlags::Unsigned), false) {}

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        // TODO: bit_cast
        float f = val.shortReal();
        uint32_t result;
        memcpy(&result, &f, sizeof(uint32_t));
        return SVInt(32, result, false);
    }
};

class BitsToShortRealFunction : public SimpleSystemSubroutine {
public:
    BitsToShortRealFunction(Compilation& comp) :
        SimpleSystemSubroutine("$bitstoshortreal", SubroutineKind::Function, 1,
                               { &comp.getType(32, IntegralFlags::Unsigned) },
                               comp.getShortRealType(), false) {}

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        // TODO: bit_cast
        uint32_t i = val.integer().as<uint32_t>().value_or(0);
        float result;
        memcpy(&result, &i, sizeof(float));

        return shortreal_t(result);
    }
};

void registerConversionFuncs(Compilation& c) {
#define REGISTER(name, ...) c.addSystemSubroutine(std::make_unique<name##Function>(__VA_ARGS__))
    REGISTER(SignedConversion, "$signed", true);
    REGISTER(SignedConversion, "$unsigned", false);

    REGISTER(RtoI, c);
    REGISTER(ItoR, c);
    REGISTER(RealToBits, c);
    REGISTER(BitsToReal, c);
    REGISTER(ShortRealToBits, c);
    REGISTER(BitsToShortReal, c);
#undef REGISTER
}

} // namespace slang::Builtins