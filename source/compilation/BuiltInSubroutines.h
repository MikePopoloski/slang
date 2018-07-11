//------------------------------------------------------------------------------
// BuiltInSubroutines.h
// Built-in system subroutine handlers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "binding/SystemSubroutine.h"

namespace slang::Builtins {

class IntegerMathFunction : public SystemSubroutine {
public:
    using SystemSubroutine::SystemSubroutine;
    const Type& checkArguments(Compilation& compilation, const Args& args) const final;
};

class DataQueryFunction : public SystemSubroutine {
public:
    using SystemSubroutine::SystemSubroutine;
    const Type& checkArguments(Compilation& compilation, const Args& args) const final;
};

class ArrayQueryFunction : public SystemSubroutine {
public:
    using SystemSubroutine::SystemSubroutine;
    const Type& checkArguments(Compilation& compilation, const Args& args) const final;
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

}