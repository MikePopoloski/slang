//------------------------------------------------------------------------------
// SystemTasks.cpp
// Built-in system tasks.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"

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

    bool allowEmptyArgument(size_t) const final { return true; }

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

static bool checkFinishNum(const BindContext& context, const Expression& arg) {
    if (arg.constant && arg.constant->isInteger()) {
        auto& val = arg.constant->integer();
        if (val == 0 || val == 1 || val == 2)
            return true;
    }

    context.addDiag(diag::BadFinishNum, arg.sourceRange);
    return false;
}

class FinishControlTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, 1))
            return comp.getErrorType();

        if (args.size() == 1) {
            if (!checkFinishNum(context, *args[0]))
                return comp.getErrorType();
        }

        return comp.getVoidType();
    }
};

class FatalTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    bool allowEmptyArgument(size_t index) const final { return index != 0; }

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange) const final {
        auto& comp = context.getCompilation();
        if (!args.empty()) {
            if (args[0]->bad())
                return comp.getErrorType();

            if (!checkFinishNum(context, *args[0]))
                return comp.getErrorType();

            if (!checkFormatArgs(context, args.subspan(1)))
                return comp.getErrorType();
        }

        return comp.getVoidType();
    }
};

class FileDisplayTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    bool allowEmptyArgument(size_t index) const final { return index != 0; }

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, INT32_MAX))
            return comp.getErrorType();

        if (!args[0]->type->isIntegral()) {
            context.addDiag(diag::BadSystemSubroutineArg, args[0]->sourceRange)
                << *args[0]->type << kindStr();
            return comp.getErrorType();
        }

        if (!checkFormatArgs(context, args.subspan(1)))
            return comp.getErrorType();

        return comp.getVoidType();
    }
};

class StringOutputTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    bool allowEmptyArgument(size_t index) const final { return index != 0; }

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, INT32_MAX))
            return comp.getErrorType();

        if (!context.requireLValue(*args[0], args[0]->sourceRange.start()))
            return comp.getErrorType();

        const Type& ft = *args[0]->type;
        if (!ft.canBeStringLike()) {
            context.addDiag(diag::InvalidStringArg, args[0]->sourceRange) << ft;
            return comp.getErrorType();
        }

        if (!checkFormatArgs(context, args.subspan(1)))
            return comp.getErrorType();

        return comp.getVoidType();
    }
};

class StringFormatTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, INT32_MAX))
            return comp.getErrorType();

        if (!context.requireLValue(*args[0], args[0]->sourceRange.start()))
            return comp.getErrorType();

        for (size_t i = 0; i < 2; i++) {
            const Type& ft = *args[i]->type;
            if (!ft.canBeStringLike()) {
                context.addDiag(diag::InvalidStringArg, args[i]->sourceRange) << ft;
                return comp.getErrorType();
            }
        }

        if (!checkFormatArgs(context, args.subspan(2)))
            return comp.getErrorType();

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

    REGISTER(FileDisplayTask, "$fdisplay");
    REGISTER(FileDisplayTask, "$fdisplayb");
    REGISTER(FileDisplayTask, "$fdisplayo");
    REGISTER(FileDisplayTask, "$fdisplayh");
    REGISTER(FileDisplayTask, "$fwrite");
    REGISTER(FileDisplayTask, "$fwriteb");
    REGISTER(FileDisplayTask, "$fwriteo");
    REGISTER(FileDisplayTask, "$fwriteh");
    REGISTER(FileDisplayTask, "$fstrobe");
    REGISTER(FileDisplayTask, "$fstrobeb");
    REGISTER(FileDisplayTask, "$fstrobeo");
    REGISTER(FileDisplayTask, "$fstrobeh");
    REGISTER(FileDisplayTask, "$fmonitor");
    REGISTER(FileDisplayTask, "$fmonitorb");
    REGISTER(FileDisplayTask, "$fmonitoro");
    REGISTER(FileDisplayTask, "$fmonitorh");

    REGISTER(StringOutputTask, "$swrite");
    REGISTER(StringOutputTask, "$swriteb");
    REGISTER(StringOutputTask, "$swriteo");
    REGISTER(StringOutputTask, "$swriteh");

    REGISTER(DisplayTask, "$error");
    REGISTER(DisplayTask, "$warning");
    REGISTER(DisplayTask, "$info");

    REGISTER(FatalTask, "$fatal");

    REGISTER(FinishControlTask, "$finish");
    REGISTER(FinishControlTask, "$stop");

    REGISTER(SimpleControlTask, "$exit");
    REGISTER(SimpleControlTask, "$monitoron");
    REGISTER(SimpleControlTask, "$monitoroff");

    REGISTER(StringFormatTask, "$sformat");
#undef REGISTER
}

} // namespace slang::Builtins