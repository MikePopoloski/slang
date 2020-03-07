//------------------------------------------------------------------------------
// SystemTasks.cpp
// Built-in system tasks
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"

namespace slang::Builtins {

class SystemTaskBase : public SystemSubroutine {
public:
    explicit SystemTaskBase(const std::string& name) :
        SystemSubroutine(name, SubroutineKind::Task) {}
    ConstantValue eval(EvalContext&, const Args&) const final { return nullptr; }
    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

class SimpleSystemTask : public SimpleSystemSubroutine {
public:
    SimpleSystemTask(const std::string& name, const Type& returnType, size_t requiredArgs = 0,
                     const std::vector<const Type*>& argTypes = {}) :
        SimpleSystemSubroutine(name, SubroutineKind::Task, requiredArgs, argTypes, returnType,
                               false) {}

    ConstantValue eval(EvalContext&, const Args&) const final { return nullptr; }
    bool verifyConstant(EvalContext&, const Args&) const final { return false; }
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

        if (!args[0]->type->isIntegral())
            return badArg(context, *args[0]);

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

        if (!args[0]->verifyAssignable(context))
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

        if (!args[0]->verifyAssignable(context))
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

class ReadWriteMemTask : public SystemTaskBase {
public:
    ReadWriteMemTask(const std::string& name, bool isInput) :
        SystemTaskBase(name), isInput(isInput) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, 4))
            return comp.getErrorType();

        if (isInput && !args[1]->verifyAssignable(context))
            return comp.getErrorType();

        if (!args[0]->type->canBeStringLike())
            return badArg(context, *args[0]);

        if (!args[1]->type->isUnpackedArray())
            return badArg(context, *args[1]);

        const Type* t = args[1]->type;
        do {
            t = &t->getCanonicalType().as<UnpackedArrayType>().elementType;
        } while (t->isUnpackedArray());

        if (!t->isIntegral())
            return badArg(context, *args[1]);

        if (args.size() >= 3) {
            if (!args[2]->type->isIntegral())
                return badArg(context, *args[2]);

            if (args.size() == 4) {
                if (!args[3]->type->isIntegral())
                    return badArg(context, *args[3]);
            }
        }

        return comp.getVoidType();
    }

private:
    bool isInput;
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

    REGISTER(StringFormatTask, "$sformat");
#undef REGISTER

    c.addSystemSubroutine(std::make_unique<ReadWriteMemTask>("$readmemb", true));
    c.addSystemSubroutine(std::make_unique<ReadWriteMemTask>("$readmemh", true));
    c.addSystemSubroutine(std::make_unique<ReadWriteMemTask>("$writememb", false));
    c.addSystemSubroutine(std::make_unique<ReadWriteMemTask>("$writememh", false));

#define TASK(name, required, ...)                             \
    c.addSystemSubroutine(std::make_unique<SimpleSystemTask>( \
        name, c.getVoidType(), required, std::vector<const Type*>{ __VA_ARGS__ }))

    TASK("$exit", 0, );

    TASK("$monitoron", 0, );
    TASK("$monitoroff", 0, );

    TASK("$dumpfile", 0, &c.getStringType());
    TASK("$dumpon", 0, );
    TASK("$dumpoff", 0, );
    TASK("$dumpall", 0, );
    TASK("$dumplimit", 1, &c.getIntType());
    TASK("$dumpflush", 0, );
    TASK("$dumpportson", 0, &c.getStringType());
    TASK("$dumpportsoff", 0, &c.getStringType());
    TASK("$dumpportsall", 0, &c.getStringType());
    TASK("$dumpportslimit", 1, &c.getIntType(), &c.getStringType());
    TASK("$dumpportsflush", 0, &c.getStringType());

#undef TASK
}

} // namespace slang::Builtins