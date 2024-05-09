//------------------------------------------------------------------------------
// ConversionFuncs.cpp
// Built-in conversion system functions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "Builtins.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/types/Type.h"

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
    explicit RtoIFunction(const Builtins& builtins) :
        SimpleSystemSubroutine("$rtoi", SubroutineKind::Function, 1, {&builtins.realType},
                               builtins.integerType, false) {}

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
    ItoRFunction() : SystemSubroutine("$itor", SubroutineKind::Function) {}

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
    explicit RealToBitsFunction(const Builtins& builtins) :
        SimpleSystemSubroutine("$realtobits", SubroutineKind::Function, 1, {&builtins.realType},
                               builtins.ulongIntType, false) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        return SVInt(64, std::bit_cast<uint64_t>(val.real()), false);
    }
};

class BitsToRealFunction : public SimpleSystemSubroutine {
public:
    explicit BitsToRealFunction(const Builtins& builtins) :
        SimpleSystemSubroutine("$bitstoreal", SubroutineKind::Function, 1, {&builtins.ulongIntType},
                               builtins.realType, false) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        uint64_t i = val.integer().as<uint64_t>().value_or(0);
        return real_t(std::bit_cast<double>(i));
    }
};

class ShortRealToBitsFunction : public SimpleSystemSubroutine {
public:
    explicit ShortRealToBitsFunction(const Builtins& builtins) :
        SimpleSystemSubroutine("$shortrealtobits", SubroutineKind::Function, 1,
                               {&builtins.shortRealType}, builtins.uintType, false) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        return SVInt(32, std::bit_cast<uint32_t>(val.shortReal()), false);
    }
};

class BitsToShortRealFunction : public SimpleSystemSubroutine {
public:
    explicit BitsToShortRealFunction(const Builtins& builtins) :
        SimpleSystemSubroutine("$bitstoshortreal", SubroutineKind::Function, 1,
                               {&builtins.uintType}, builtins.shortRealType, false) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        uint32_t i = val.integer().as<uint32_t>().value_or(0);
        return shortreal_t(std::bit_cast<float>(i));
    }
};

void Builtins::registerConversionFuncs() {
#define REGISTER(name, ...) addSystemSubroutine(std::make_shared<name##Function>(__VA_ARGS__))
    REGISTER(SignedConversion, "$signed", true);
    REGISTER(SignedConversion, "$unsigned", false);

    REGISTER(RtoI, *this);
    REGISTER(ItoR, );
    REGISTER(RealToBits, *this);
    REGISTER(BitsToReal, *this);
    REGISTER(ShortRealToBits, *this);
    REGISTER(BitsToShortReal, *this);
#undef REGISTER
}

} // namespace slang::ast::builtins
