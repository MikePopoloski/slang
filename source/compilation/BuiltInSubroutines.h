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

#define SUBROUTINE(name, className, base)                                       \
    class className : public base {                                             \
    public:                                                                     \
        className() : base(name) {}                                             \
        ConstantValue eval(EvalContext& context, const Args& args) const final; \
    }

SUBROUTINE("$clog2", Clog2Subroutine, IntegerMathFunction);
SUBROUTINE("$bits", BitsSubroutine, DataQueryFunction);
SUBROUTINE("$low", LowSubroutine, ArrayQueryFunction);
SUBROUTINE("$high", HighSubroutine, ArrayQueryFunction);
SUBROUTINE("$left", LeftSubroutine, ArrayQueryFunction);
SUBROUTINE("$right", RightSubroutine, ArrayQueryFunction);
SUBROUTINE("$size", SizeSubroutine, ArrayQueryFunction);
SUBROUTINE("$increment", IncrementSubroutine, ArrayQueryFunction);

#undef SUBROUTINE

}