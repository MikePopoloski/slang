//------------------------------------------------------------------------------
// ConversionFuncs.cpp
// Built-in conversion system functions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Compilation.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/types/Type.h"

// TODO: remove once AppleClang finally adds support for this
template<typename Dest, typename Source>
inline Dest bit_cast(const Source& src) noexcept {
    static_assert(sizeof(Dest) == sizeof(Source),
                  "bit_cast requires source and destination to be the same size");
    static_assert(std::is_trivially_copyable<Dest>::value,
                  "bit_cast requires the destination type to be copyable");
    static_assert(std::is_trivially_copyable<Source>::value,
                  "bit_cast requires the source type to be copyable");
    Dest dst;
    std::memcpy(&dst, &src, sizeof(Dest));
    return dst;
}

namespace slang::ast::builtins {

class SignedConversionFunction : public SystemSubroutine {
public:
    SignedConversionFunction(const std::string& name, bool toSigned) :
        SystemSubroutine(name, SubroutineKind::Function), toSigned(toSigned) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
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

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        const Type& to = *args[0]->type;
        return val.convertToInt(to.getBitWidth(), toSigned, to.isFourState());
    }

private:
    bool toSigned;
};

class RtoIFunction : public SimpleSystemSubroutine {
public:
    explicit RtoIFunction(Compilation& comp) :
        SimpleSystemSubroutine("$rtoi", SubroutineKind::Function, 1, {&comp.getRealType()},
                               comp.getIntegerType(), false) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        return SVInt(32, (uint64_t)val.real(), true);
    }
};

class ItoRFunction : public SystemSubroutine {
public:
    explicit ItoRFunction(Compilation&) : SystemSubroutine("$itor", SubroutineKind::Function) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        if (!args[0]->type->isNumeric())
            return badArg(context, *args[0]);

        return comp.getRealType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        return val.convertToReal();
    }
};

class RealToBitsFunction : public SimpleSystemSubroutine {
public:
    explicit RealToBitsFunction(Compilation& comp) :
        SimpleSystemSubroutine("$realtobits", SubroutineKind::Function, 1, {&comp.getRealType()},
                               comp.getType(64, IntegralFlags::Unsigned), false) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        return SVInt(64, bit_cast<uint64_t>(val.real()), false);
    }
};

class BitsToRealFunction : public SimpleSystemSubroutine {
public:
    explicit BitsToRealFunction(Compilation& comp) :
        SimpleSystemSubroutine("$bitstoreal", SubroutineKind::Function, 1,
                               {&comp.getType(64, IntegralFlags::Unsigned)}, comp.getRealType(),
                               false) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        uint64_t i = val.integer().as<uint64_t>().value_or(0);
        return real_t(bit_cast<double>(i));
    }
};

class ShortRealToBitsFunction : public SimpleSystemSubroutine {
public:
    explicit ShortRealToBitsFunction(Compilation& comp) :
        SimpleSystemSubroutine("$shortrealtobits", SubroutineKind::Function, 1,
                               {&comp.getShortRealType()},
                               comp.getType(32, IntegralFlags::Unsigned), false) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        return SVInt(32, bit_cast<uint32_t>(val.shortReal()), false);
    }
};

class BitsToShortRealFunction : public SimpleSystemSubroutine {
public:
    explicit BitsToShortRealFunction(Compilation& comp) :
        SimpleSystemSubroutine("$bitstoshortreal", SubroutineKind::Function, 1,
                               {&comp.getType(32, IntegralFlags::Unsigned)},
                               comp.getShortRealType(), false) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        uint32_t i = val.integer().as<uint32_t>().value_or(0);
        return shortreal_t(bit_cast<float>(i));
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

} // namespace slang::ast::builtins
