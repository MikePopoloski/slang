//------------------------------------------------------------------------------
// BuiltInSubroutines.h
// Built-in system subroutine handlers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/SystemSubroutine.h"

namespace slang::Builtins {

class IntegerMathFunction : public SystemSubroutine {
public:
    using SystemSubroutine::SystemSubroutine;
    const Type& checkArguments(const BindContext& context, const Args& args) const final;
    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

class DataQueryFunction : public SystemSubroutine {
public:
    using SystemSubroutine::SystemSubroutine;
    const Type& checkArguments(const BindContext& context, const Args& args) const final;
    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

class ArrayQueryFunction : public SystemSubroutine {
public:
    using SystemSubroutine::SystemSubroutine;
    const Type& checkArguments(const BindContext& context, const Args& args) const final;
    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

class EnumFirstLastMethod : public SystemSubroutine {
public:
    EnumFirstLastMethod(const std::string& name, bool first);
    const Type& checkArguments(const BindContext& context, const Args& args) const final;
    ConstantValue eval(EvalContext& context, const Args& args) const final;
    bool verifyConstant(EvalContext&, const Args&) const final { return true; }

private:
    bool first;
};

class EnumNumMethod : public SystemSubroutine {
public:
    EnumNumMethod() : SystemSubroutine("num") {}
    const Type& checkArguments(const BindContext& context, const Args& args) const final;
    ConstantValue eval(EvalContext& context, const Args& args) const final;
    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

#define SUBROUTINE(className, base, ...)                                        \
    class className : public base {                                             \
    public:                                                                     \
        className() : base(__VA_ARGS__) {}                                      \
        ConstantValue eval(EvalContext& context, const Args& args) const final; \
    }

SUBROUTINE(Clog2Subroutine, IntegerMathFunction, "$clog2");

SUBROUTINE(BitsSubroutine, DataQueryFunction, "$bits", SystemSubroutineFlags::AllowDataTypeArg);

SUBROUTINE(LowSubroutine, ArrayQueryFunction, "$low");
SUBROUTINE(HighSubroutine, ArrayQueryFunction, "$high");
SUBROUTINE(LeftSubroutine, ArrayQueryFunction, "$left");
SUBROUTINE(RightSubroutine, ArrayQueryFunction, "$right");
SUBROUTINE(SizeSubroutine, ArrayQueryFunction, "$size");
SUBROUTINE(IncrementSubroutine, ArrayQueryFunction, "$increment");

#undef SUBROUTINE

} // namespace slang::Builtins