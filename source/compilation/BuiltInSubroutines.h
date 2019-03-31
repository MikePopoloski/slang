//------------------------------------------------------------------------------
// BuiltInSubroutines.h
// Built-in system subroutine handlers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/SystemSubroutine.h"

namespace slang {
class Compilation;
}

namespace slang::Builtins {

class SystemTaskBase : public SystemSubroutine {
public:
    SystemTaskBase(const std::string& name) : SystemSubroutine(name, SubroutineKind::Task) {}
    ConstantValue eval(EvalContext&, const Args&) const final { return nullptr; }
    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

class IntegerMathFunction : public SystemSubroutine {
public:
    using SystemSubroutine::SystemSubroutine;
    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final;
    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

class DataQueryFunction : public SystemSubroutine {
public:
    using SystemSubroutine::SystemSubroutine;
    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final;
    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

class ArrayQueryFunction : public SystemSubroutine {
public:
    using SystemSubroutine::SystemSubroutine;
    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final;
    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

class DisplayTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;
    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final;
};

class SimpleControlTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;
    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final;
};

class FinishControlTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;
    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final;
};

class FatalTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;
    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final;
};

class EnumFirstLastMethod : public SystemSubroutine {
public:
    EnumFirstLastMethod(const std::string& name, bool first);
    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final;
    ConstantValue eval(EvalContext& context, const Args& args) const final;
    bool verifyConstant(EvalContext&, const Args&) const final { return true; }

private:
    bool first;
};

class EnumNumMethod : public SystemSubroutine {
public:
    EnumNumMethod() : SystemSubroutine("num", SubroutineKind::Function) {}
    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final;
    ConstantValue eval(EvalContext& context, const Args& args) const final;
    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

#define FUNC SubroutineKind::Function
#define TASK SubroutineKind::Task
#define SUBROUTINE(className, base, ...)                                        \
    class className : public base {                                             \
    public:                                                                     \
        className() : base(__VA_ARGS__) {}                                      \
        ConstantValue eval(EvalContext& context, const Args& args) const final; \
    }

SUBROUTINE(Clog2Subroutine, IntegerMathFunction, "$clog2", FUNC);

SUBROUTINE(BitsSubroutine, DataQueryFunction, "$bits", FUNC,
           SystemSubroutineFlags::AllowDataTypeArg);

SUBROUTINE(LowSubroutine, ArrayQueryFunction, "$low", FUNC);
SUBROUTINE(HighSubroutine, ArrayQueryFunction, "$high", FUNC);
SUBROUTINE(LeftSubroutine, ArrayQueryFunction, "$left", FUNC);
SUBROUTINE(RightSubroutine, ArrayQueryFunction, "$right", FUNC);
SUBROUTINE(SizeSubroutine, ArrayQueryFunction, "$size", FUNC);
SUBROUTINE(IncrementSubroutine, ArrayQueryFunction, "$increment", FUNC);

#undef SUBROUTINE
#undef TASK
#undef FUNC

/// Registers all defined system subroutines with the given compilation object.
void registerAll(Compilation& compilation);

} // namespace slang::Builtins