//------------------------------------------------------------------------------
// SystemTasks.cpp
// Built-in system tasks
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/FormatHelpers.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/mir/Procedure.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::Builtins {

class SystemTaskBase : public SystemSubroutine {
public:
    explicit SystemTaskBase(const std::string& name) :
        SystemSubroutine(name, SubroutineKind::Task) {}
    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }
};

class SimpleSystemTask : public SimpleSystemSubroutine {
public:
    SimpleSystemTask(const std::string& name, const Type& returnType, size_t requiredArgs = 0,
                     const std::vector<const Type*>& argTypes = {}) :
        SimpleSystemSubroutine(name, SubroutineKind::Task, requiredArgs, argTypes, returnType,
                               false) {}

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }
};

class DisplayTask : public SystemTaskBase {
public:
    LiteralBase defaultIntFmt;

    DisplayTask(const std::string& name, LiteralBase defaultIntFmt) :
        SystemTaskBase(name), defaultIntFmt(defaultIntFmt) {}

    bool allowEmptyArgument(size_t) const final { return true; }

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!FmtHelpers::checkDisplayArgs(context, args))
            return comp.getErrorType();

        return comp.getVoidType();
    }

    void lower(mir::Procedure& proc, const Args& args) const final {
        FmtHelpers::lowerFormatArgs(proc, args, defaultIntFmt, /* newline */ true);
    }
};

class FinishControlTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, 1))
            return comp.getErrorType();

        if (args.size() == 1) {
            if (!FmtHelpers::checkFinishNum(context, *args[0]))
                return comp.getErrorType();
        }

        return comp.getVoidType();
    }
};

class FatalTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    bool allowEmptyArgument(size_t index) const final { return index != 0; }

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!args.empty()) {
            if (args[0]->bad())
                return comp.getErrorType();

            if (!FmtHelpers::checkFinishNum(context, *args[0]))
                return comp.getErrorType();

            if (!FmtHelpers::checkDisplayArgs(context, args.subspan(1)))
                return comp.getErrorType();
        }

        return comp.getVoidType();
    }
};

class FileDisplayTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    bool allowEmptyArgument(size_t index) const final { return index != 0; }

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, INT32_MAX))
            return comp.getErrorType();

        if (!args[0]->type->isIntegral())
            return badArg(context, *args[0]);

        if (!FmtHelpers::checkDisplayArgs(context, args.subspan(1)))
            return comp.getErrorType();

        return comp.getVoidType();
    }
};

class StringOutputTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    bool allowEmptyArgument(size_t index) const final { return index != 0; }

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
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

        if (!FmtHelpers::checkDisplayArgs(context, args.subspan(1)))
            return comp.getErrorType();

        return comp.getVoidType();
    }
};

class StringFormatTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
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

        if (!FmtHelpers::checkDisplayArgs(context, args.subspan(2)))
            return comp.getErrorType();

        return comp.getVoidType();
    }
};

class ReadWriteMemTask : public SystemTaskBase {
public:
    ReadWriteMemTask(const std::string& name, bool isInput) :
        SystemTaskBase(name), isInput(isInput) {}

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
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
            if (t->isAssociativeArray()) {
                auto indexType = t->getAssociativeIndexType();
                if (indexType && !indexType->isIntegral()) {
                    context.addDiag(diag::QueryOnAssociativeNonIntegral, args[1]->sourceRange)
                        << name;
                    return comp.getErrorType();
                }
            }
            t = t->getArrayElementType();
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

class PrintTimeScaleTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    const Expression& bindArgument(size_t argIndex, const BindContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        if (argIndex == 0) {
            auto& comp = context.getCompilation();
            if (!NameSyntax::isKind(syntax.kind)) {
                context.addDiag(diag::ExpectedModuleName, syntax.sourceRange());
                return *comp.emplace<InvalidExpression>(nullptr, comp.getErrorType());
            }

            return HierarchicalReferenceExpression::fromSyntax(comp, syntax.as<NameSyntax>(),
                                                               context);
        }

        return SystemTaskBase::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, 1))
            return comp.getErrorType();

        if (args.size() > 0) {
            auto& sym = *args[0]->as<HierarchicalReferenceExpression>().symbol;
            if (sym.kind != SymbolKind::Instance || !sym.as<InstanceSymbol>().isModule()) {
                if (!context.scope.isUninstantiated())
                    context.addDiag(diag::ExpectedModuleName, args[0]->sourceRange);
                return comp.getErrorType();
            }
        }

        return comp.getVoidType();
    }
};

class DumpVarsTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    const Expression& bindArgument(size_t argIndex, const BindContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        if (argIndex > 0) {
            auto& comp = context.getCompilation();
            if (!NameSyntax::isKind(syntax.kind)) {
                context.addDiag(diag::ExpectedModOrVarName, syntax.sourceRange());
                return *comp.emplace<InvalidExpression>(nullptr, comp.getErrorType());
            }

            auto& ref =
                HierarchicalReferenceExpression::fromSyntax(comp, syntax.as<NameSyntax>(), context);

            if (ref.kind == ExpressionKind::HierarchicalReference) {
                auto& sym = *ref.as<HierarchicalReferenceExpression>().symbol;
                if (sym.kind != SymbolKind::Variable &&
                    (sym.kind != SymbolKind::Instance || !sym.as<InstanceSymbol>().isModule())) {
                    if (!context.scope.isUninstantiated())
                        context.addDiag(diag::ExpectedModOrVarName, ref.sourceRange);
                    return *comp.emplace<InvalidExpression>(&ref, comp.getErrorType());
                }
            }

            return ref;
        }

        return SystemTaskBase::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, INT32_MAX))
            return comp.getErrorType();

        if (args.size() > 0) {
            if (!args[0]->type->isIntegral())
                return badArg(context, *args[0]);
        }

        return comp.getVoidType();
    }
};

class DumpPortsTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    bool allowEmptyArgument(size_t argIndex) const final { return argIndex == 0; }

    const Expression& bindArgument(size_t argIndex, const BindContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        if (NameSyntax::isKind(syntax.kind)) {
            return HierarchicalReferenceExpression::fromSyntax(context.getCompilation(),
                                                               syntax.as<NameSyntax>(), context);
        }

        return SystemTaskBase::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, INT32_MAX))
            return comp.getErrorType();

        for (size_t i = 0; i < args.size(); i++) {
            if (args[i]->kind == ExpressionKind::EmptyArgument)
                continue;

            if (args[i]->kind == ExpressionKind::HierarchicalReference) {
                auto& sym = *args[i]->as<HierarchicalReferenceExpression>().symbol;
                if (i == args.size() - 1 && sym.isValue()) {
                    // Last arg can be a string-like value; all others must be module names.
                    auto& type = sym.as<ValueSymbol>().getType();
                    if (!type.canBeStringLike()) {
                        context.addDiag(diag::BadSystemSubroutineArg, args[i]->sourceRange)
                            << type << kindStr();
                        return context.getCompilation().getErrorType();
                    }
                }
                else if (sym.kind != SymbolKind::Instance || !sym.as<InstanceSymbol>().isModule()) {
                    if (!context.scope.isUninstantiated())
                        context.addDiag(diag::ExpectedModuleName, args[i]->sourceRange);
                    return comp.getErrorType();
                }
            }
            else if (i != args.size() - 1 || !args[i]->type->canBeStringLike()) {
                // Last arg can be a string-like value; all others must be module names.
                return badArg(context, *args[i]);
            }
        }

        return comp.getVoidType();
    }
};

class CastTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, 2))
            return comp.getErrorType();

        if (!args[0]->type->isSingular()) {
            context.addDiag(diag::CastArgSingular, args[0]->sourceRange) << *args[0]->type;
            return comp.getErrorType();
        }

        if (!args[1]->type->isSingular()) {
            context.addDiag(diag::CastArgSingular, args[1]->sourceRange) << *args[1]->type;
            return comp.getErrorType();
        }

        return comp.getIntType();
    }
};

class AssertControlTask : public SystemTaskBase {
public:
    explicit AssertControlTask(const std::string& name) :
        SystemTaskBase(name), isFullMethod(name == "$assertcontrol") {}

    const Expression& bindArgument(size_t argIndex, const BindContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        if ((isFullMethod && argIndex < 4) || (!isFullMethod && argIndex == 0) ||
            !NameSyntax::isKind(syntax.kind)) {
            return SystemTaskBase::bindArgument(argIndex, context, syntax, args);
        }

        return HierarchicalReferenceExpression::fromSyntax(context.getCompilation(),
                                                           syntax.as<NameSyntax>(), context);
    }

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, isFullMethod ? 1 : 0, INT32_MAX))
            return comp.getErrorType();

        for (size_t i = 0; i < args.size(); i++) {
            // If this is $assertcontrol, the first four args are integer expressions.
            // Otherwise, only the first arg is an integer expression. The rest, in both
            // cases, are hierarchical references.
            if ((isFullMethod && i < 4) || (!isFullMethod && i == 0)) {
                if (!args[i]->type->isIntegral())
                    return badArg(context, *args[i]);
            }
            else {
                if (args[i]->kind != ExpressionKind::HierarchicalReference ||
                    !args[i]->as<HierarchicalReferenceExpression>().symbol->isScope()) {
                    if (!context.scope.isUninstantiated())
                        context.addDiag(diag::ExpectedScopeOrAssert, args[i]->sourceRange);
                    return comp.getErrorType();
                }
            }
        }

        return comp.getVoidType();
    }

private:
    bool isFullMethod;
};

class StochasticTask : public SystemSubroutine {
public:
    StochasticTask(const std::string& name, SubroutineKind subroutineKind, size_t inputArgs,
                   size_t outputArgs) :
        SystemSubroutine(name, subroutineKind),
        inputArgs(inputArgs), outputArgs(outputArgs) {}

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        size_t totalArgs = inputArgs + outputArgs;
        if (!checkArgCount(context, false, args, range, totalArgs, totalArgs))
            return comp.getErrorType();

        for (size_t i = 0; i < inputArgs; i++) {
            if (!args[i]->type->isIntegral())
                return badArg(context, *args[i]);
        }

        for (size_t i = inputArgs; i < totalArgs; i++) {
            if (!args[i]->type->isIntegral())
                return badArg(context, *args[i]);

            if (!args[i]->verifyAssignable(context))
                return comp.getErrorType();
        }

        return kind == SubroutineKind::Function ? comp.getIntType() : comp.getVoidType();
    }

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }

    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }

private:
    size_t inputArgs;
    size_t outputArgs;
};

class SdfAnnotateTask : public SystemTaskBase {
public:
    SdfAnnotateTask() : SystemTaskBase("$sdf_annotate") {}

    const Expression& bindArgument(size_t argIndex, const BindContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        if (argIndex == 1) {
            auto& comp = context.getCompilation();
            if (!NameSyntax::isKind(syntax.kind)) {
                context.addDiag(diag::ExpectedModuleInstance, syntax.sourceRange());
                return *comp.emplace<InvalidExpression>(nullptr, comp.getErrorType());
            }

            auto& ref =
                HierarchicalReferenceExpression::fromSyntax(comp, syntax.as<NameSyntax>(), context);

            if (ref.kind == ExpressionKind::HierarchicalReference) {
                auto& sym = *ref.as<HierarchicalReferenceExpression>().symbol;
                if (sym.kind != SymbolKind::Instance || !sym.as<InstanceSymbol>().isModule()) {
                    if (!context.scope.isUninstantiated())
                        context.addDiag(diag::ExpectedModuleInstance, ref.sourceRange);
                    return *comp.emplace<InvalidExpression>(&ref, comp.getErrorType());
                }
            }

            return ref;
        }

        return SystemTaskBase::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 7))
            return comp.getErrorType();

        for (size_t i = 0; i < args.size(); i++) {
            if (i != 1 && !args[0]->type->canBeStringLike())
                return badArg(context, *args[i]);
        }

        return comp.getVoidType();
    }
};

void registerSystemTasks(Compilation& c) {
#define REGISTER(type, name, base) c.addSystemSubroutine(std::make_unique<type>(name, base))
    REGISTER(DisplayTask, "$display", LiteralBase::Decimal);
    REGISTER(DisplayTask, "$displayb", LiteralBase::Binary);
    REGISTER(DisplayTask, "$displayo", LiteralBase::Octal);
    REGISTER(DisplayTask, "$displayh", LiteralBase::Hex);
    REGISTER(DisplayTask, "$write", LiteralBase::Decimal);
    REGISTER(DisplayTask, "$writeb", LiteralBase::Binary);
    REGISTER(DisplayTask, "$writeo", LiteralBase::Octal);
    REGISTER(DisplayTask, "$writeh", LiteralBase::Hex);
    REGISTER(DisplayTask, "$strobe", LiteralBase::Decimal);
    REGISTER(DisplayTask, "$strobeb", LiteralBase::Binary);
    REGISTER(DisplayTask, "$strobeo", LiteralBase::Octal);
    REGISTER(DisplayTask, "$strobeh", LiteralBase::Hex);
    REGISTER(DisplayTask, "$monitor", LiteralBase::Decimal);
    REGISTER(DisplayTask, "$monitorb", LiteralBase::Binary);
    REGISTER(DisplayTask, "$monitoro", LiteralBase::Octal);
    REGISTER(DisplayTask, "$monitorh", LiteralBase::Hex);

    REGISTER(DisplayTask, "$error", LiteralBase::Decimal);
    REGISTER(DisplayTask, "$warning", LiteralBase::Decimal);
    REGISTER(DisplayTask, "$info", LiteralBase::Decimal);

#undef REGISTER
#define REGISTER(type, name) c.addSystemSubroutine(std::make_unique<type>(name))
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

    REGISTER(FatalTask, "$fatal");

    REGISTER(FinishControlTask, "$finish");
    REGISTER(FinishControlTask, "$stop");

    REGISTER(StringFormatTask, "$sformat");

    REGISTER(PrintTimeScaleTask, "$printtimescale");

    REGISTER(DumpVarsTask, "$dumpvars");
    REGISTER(DumpPortsTask, "$dumpports");

    REGISTER(CastTask, "$cast");

#undef REGISTER

    auto int_t = &c.getIntType();
    auto string_t = &c.getStringType();

    c.addSystemSubroutine(std::make_unique<ReadWriteMemTask>("$readmemb", true));
    c.addSystemSubroutine(std::make_unique<ReadWriteMemTask>("$readmemh", true));
    c.addSystemSubroutine(std::make_unique<ReadWriteMemTask>("$writememb", false));
    c.addSystemSubroutine(std::make_unique<ReadWriteMemTask>("$writememh", false));
    c.addSystemSubroutine(std::make_unique<SimpleSystemTask>("$system", *int_t, 0,
                                                             std::vector<const Type*>{ string_t }));
    c.addSystemSubroutine(std::make_unique<SdfAnnotateTask>());

#define TASK(name, required, ...)                             \
    c.addSystemSubroutine(std::make_unique<SimpleSystemTask>( \
        name, c.getVoidType(), required, std::vector<const Type*>{ __VA_ARGS__ }))

    TASK("$exit", 0, );

    TASK("$timeformat", 0, int_t, int_t, string_t, int_t);

    TASK("$monitoron", 0, );
    TASK("$monitoroff", 0, );

    TASK("$dumpfile", 0, string_t);
    TASK("$dumpon", 0, );
    TASK("$dumpoff", 0, );
    TASK("$dumpall", 0, );
    TASK("$dumplimit", 1, int_t);
    TASK("$dumpflush", 0, );
    TASK("$dumpportson", 0, string_t);
    TASK("$dumpportsoff", 0, string_t);
    TASK("$dumpportsall", 0, string_t);
    TASK("$dumpportslimit", 1, int_t, string_t);
    TASK("$dumpportsflush", 0, string_t);

#undef TASK

#define ASSERTCTRL(name) c.addSystemSubroutine(std::make_unique<AssertControlTask>(name))
    ASSERTCTRL("$assertcontrol");
    ASSERTCTRL("$asserton");
    ASSERTCTRL("$assertoff");
    ASSERTCTRL("$assertkill");
    ASSERTCTRL("$assertpasson");
    ASSERTCTRL("$assertpassoff");
    ASSERTCTRL("$assertfailon");
    ASSERTCTRL("$assertfailoff");
    ASSERTCTRL("$assertnonvacuouson");
    ASSERTCTRL("$assertvacuousoff");

#undef ASSERTCTRL

#define TASK(name, kind, input, output) \
    c.addSystemSubroutine(std::make_unique<StochasticTask>(name, kind, input, output))
    TASK("$q_initialize", SubroutineKind::Task, 3, 1);
    TASK("$q_add", SubroutineKind::Task, 3, 1);
    TASK("$q_remove", SubroutineKind::Task, 2, 2);
    TASK("$q_exam", SubroutineKind::Task, 2, 2);
    TASK("$q_full", SubroutineKind::Function, 1, 1);

#undef TASK
}

} // namespace slang::Builtins
