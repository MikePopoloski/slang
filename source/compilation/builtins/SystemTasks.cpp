//------------------------------------------------------------------------------
// SystemTasks.cpp
// Built-in system tasks.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"

namespace slang::Builtins {

class SystemTaskBase : public SystemSubroutine {
public:
    SystemTaskBase(const std::string& name) : SystemSubroutine(name, SubroutineKind::Task) {}
    ConstantValue eval(EvalContext&, const Args&) const final { return nullptr; }
    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

class DisplayTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange) const final {
        auto& comp = context.getCompilation();
        if (!checkFormatArgs(context, args))
            return comp.getErrorType();

        return comp.getVoidType();
    }
};

class SimpleControlTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, 0))
            return comp.getErrorType();

        return comp.getVoidType();
    }
};

class FinishControlTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, 1))
            return comp.getErrorType();

        // TODO: check optional first arg

        return comp.getVoidType();
    }
};

class FatalTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange) const final {
        auto& comp = context.getCompilation();
        if (!args.empty()) {
            // TODO: check finish number
            if (args[0]->bad())
                return comp.getErrorType();

            if (!checkFormatArgs(context, args.subspan(1)))
                return comp.getErrorType();
        }

        return comp.getVoidType();
    }
};

void registerSystemTasks(Compilation& c) {
#define REGISTER(type, name) c.addSystemSubroutine(std::make_unique<type>(name))
    REGISTER(DisplayTask, "$display");
    REGISTER(DisplayTask, "$displayb");
    REGISTER(DisplayTask, "$displayo");
    REGISTER(DisplayTask, "$displayh");
    REGISTER(DisplayTask, "$write");
    REGISTER(DisplayTask, "$writeb");
    REGISTER(DisplayTask, "$writeo");
    REGISTER(DisplayTask, "$writeh");
    REGISTER(DisplayTask, "$strobe");
    REGISTER(DisplayTask, "$strobeb");
    REGISTER(DisplayTask, "$strobeo");
    REGISTER(DisplayTask, "$strobeh");
    REGISTER(DisplayTask, "$monitor");
    REGISTER(DisplayTask, "$monitorb");
    REGISTER(DisplayTask, "$monitoro");
    REGISTER(DisplayTask, "$monitorh");

    REGISTER(DisplayTask, "$error");
    REGISTER(DisplayTask, "$warning");
    REGISTER(DisplayTask, "$info");

    REGISTER(FatalTask, "$fatal");

    REGISTER(FinishControlTask, "$finish");
    REGISTER(FinishControlTask, "$stop");

    REGISTER(SimpleControlTask, "$exit");
    REGISTER(SimpleControlTask, "$monitoron");
    REGISTER(SimpleControlTask, "$monitoroff");
#undef REGISTER
}

} // namespace slang::Builtins