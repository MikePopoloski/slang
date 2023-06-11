//------------------------------------------------------------------------------
// SystemTasks.cpp
// Built-in system tasks
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "../FmtHelpers.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast::builtins {

using namespace syntax;

class SystemTaskBase : public SystemSubroutine {
public:
    explicit SystemTaskBase(const std::string& name) :
        SystemSubroutine(name, SubroutineKind::Task) {}

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class SimpleSystemTask : public SimpleSystemSubroutine {
public:
    SimpleSystemTask(const std::string& name, const Type& returnType, size_t requiredArgs = 0,
                     const std::vector<const Type*>& argTypes = {}) :
        SimpleSystemSubroutine(name, SubroutineKind::Task, requiredArgs, argTypes, returnType,
                               false) {}

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class DisplayTask : public SystemTaskBase {
public:
    LiteralBase defaultIntFmt;

    DisplayTask(const std::string& name, LiteralBase defaultIntFmt) :
        SystemTaskBase(name), defaultIntFmt(defaultIntFmt) {}

    bool allowEmptyArgument(size_t) const final { return true; }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange,
                               const Expression*) const override {
        auto& comp = context.getCompilation();
        if (!FmtHelpers::checkDisplayArgs(context, args))
            return comp.getErrorType();

        return comp.getVoidType();
    }
};

struct MonitorVisitor : public ASTVisitor<MonitorVisitor, true, true> {
    const ASTContext& context;

    MonitorVisitor(const ASTContext& context) : context(context) {}

    void handle(const ValueExpressionBase& expr) {
        if (VariableSymbol::isKind(expr.symbol.kind) &&
            expr.symbol.as<VariableSymbol>().lifetime == VariableLifetime::Automatic) {
            context.addDiag(diag::AutoVarTraced, expr.sourceRange) << expr.symbol.name;
        }
    }
};

class MonitorTask : public DisplayTask {
public:
    using DisplayTask::DisplayTask;

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression* iterOrThis) const final {
        auto& result = DisplayTask::checkArguments(context, args, range, iterOrThis);
        if (result.isError())
            return result;

        // Additional restriction for monitor tasks: automatic variables cannot be referenced.
        MonitorVisitor visitor(context);
        for (auto arg : args)
            arg->visit(visitor);

        return result;
    }
};

class FinishControlTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
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

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange,
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

class StaticAssertTask : public SystemSubroutine {
public:
    StaticAssertTask() : SystemSubroutine("$static_assert", SubroutineKind::Task) {}

    bool allowEmptyArgument(size_t index) const final { return index != 0; }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();

        std::string_view message;
        const Expression* condition = nullptr;

        if (!args.empty()) {
            for (auto arg : args) {
                if (arg->bad())
                    return comp.getErrorType();
            }

            if (!context.requireBooleanConvertible(*args[0]) || !context.eval(*args[0]))
                return comp.getErrorType();

            auto msg = ElabSystemTaskSymbol::createMessage(context, args.subspan(1));
            if (!msg)
                return comp.getErrorType();

            condition = args[0];
            message = *msg;
        }

        ElabSystemTaskSymbol::reportStaticAssert(*context.scope, range.start(), message, condition);

        return comp.getVoidType();
    }

    ConstantValue eval(EvalContext&, const Args&, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
};

class FileDisplayTask : public SystemTaskBase {
public:
    using SystemTaskBase::SystemTaskBase;

    bool allowEmptyArgument(size_t index) const final { return index != 0; }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const override {
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

class FileMonitorTask : public FileDisplayTask {
public:
    using FileDisplayTask::FileDisplayTask;

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression* iterOrThis) const final {
        auto& result = FileDisplayTask::checkArguments(context, args, range, iterOrThis);
        if (result.isError())
            return result;

        // Additional restriction for monitor tasks: automatic variables cannot be referenced.
        MonitorVisitor visitor(context);
        for (auto arg : args.subspan(1))
            arg->visit(visitor);

        return result;
    }
};

class StringOutputTask : public SystemTaskBase {
public:
    explicit StringOutputTask(const std::string& name) : SystemTaskBase(name) {
        hasOutputArgs = true;
    }

    bool allowEmptyArgument(size_t index) const final { return index != 0; }

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        if (argIndex == 0)
            return Expression::bindLValue(syntax, context);
        return Expression::bind(syntax, context);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, INT32_MAX))
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
    explicit StringFormatTask(const std::string& name) : SystemTaskBase(name) {
        hasOutputArgs = true;
    }

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        if (argIndex == 0)
            return Expression::bindLValue(syntax, context);
        return Expression::bind(syntax, context);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, INT32_MAX))
            return comp.getErrorType();

        for (size_t i = 0; i < 2; i++) {
            const Type& ft = *args[i]->type;
            if (!ft.canBeStringLike()) {
                context.addDiag(diag::InvalidStringArg, args[i]->sourceRange) << ft;
                return comp.getErrorType();
            }
        }

        if (!FmtHelpers::checkSFormatArgs(context, args.subspan(1)))
            return comp.getErrorType();

        return comp.getVoidType();
    }
};

class ReadWriteMemTask : public SystemTaskBase {
public:
    ReadWriteMemTask(const std::string& name, bool isInput) :
        SystemTaskBase(name), isInput(isInput) {
        hasOutputArgs = isInput;
    }

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        if (isInput && argIndex == 1)
            return Expression::bindLValue(syntax, context);
        return Expression::bind(syntax, context);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, 4))
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
            if (!args[2]->type->isNumeric())
                return badArg(context, *args[2]);

            if (args.size() == 4) {
                if (!args[3]->type->isNumeric())
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

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        if (argIndex == 0) {
            auto& comp = context.getCompilation();
            if (!NameSyntax::isKind(syntax.kind)) {
                context.addDiag(diag::ExpectedModuleName, syntax.sourceRange());
                return *comp.emplace<InvalidExpression>(nullptr, comp.getErrorType());
            }

            return ArbitrarySymbolExpression::fromSyntax(comp, syntax.as<NameSyntax>(), context);
        }

        return SystemTaskBase::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, 1))
            return comp.getErrorType();

        if (args.size() > 0) {
            auto& sym = *args[0]->as<ArbitrarySymbolExpression>().symbol;
            if (sym.kind != SymbolKind::Instance || !sym.as<InstanceSymbol>().isModule()) {
                if (!context.scope->isUninstantiated())
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

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        if (argIndex > 0) {
            auto& comp = context.getCompilation();
            if (!NameSyntax::isKind(syntax.kind)) {
                context.addDiag(diag::ExpectedModOrVarName, syntax.sourceRange());
                return *comp.emplace<InvalidExpression>(nullptr, comp.getErrorType());
            }

            auto& ref = ArbitrarySymbolExpression::fromSyntax(comp, syntax.as<NameSyntax>(),
                                                              context);

            if (ref.kind == ExpressionKind::ArbitrarySymbol) {
                auto& sym = *ref.as<ArbitrarySymbolExpression>().symbol;
                if (sym.kind != SymbolKind::Variable && sym.kind != SymbolKind::Net &&
                    (sym.kind != SymbolKind::Instance || !sym.as<InstanceSymbol>().isModule())) {
                    if (!context.scope->isUninstantiated())
                        context.addDiag(diag::ExpectedModOrVarName, ref.sourceRange);
                    return *comp.emplace<InvalidExpression>(&ref, comp.getErrorType());
                }
                else if (VariableSymbol::isKind(sym.kind) &&
                         sym.as<VariableSymbol>().lifetime == VariableLifetime::Automatic) {
                    context.addDiag(diag::AutoVarTraced, ref.sourceRange) << sym.name;
                }
            }

            return ref;
        }

        return SystemTaskBase::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
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

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        if (NameSyntax::isKind(syntax.kind)) {
            return ArbitrarySymbolExpression::fromSyntax(context.getCompilation(),
                                                         syntax.as<NameSyntax>(), context);
        }

        return SystemTaskBase::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, INT32_MAX))
            return comp.getErrorType();

        for (size_t i = 0; i < args.size(); i++) {
            if (args[i]->kind == ExpressionKind::EmptyArgument)
                continue;

            if (args[i]->kind == ExpressionKind::ArbitrarySymbol) {
                auto& sym = *args[i]->as<ArbitrarySymbolExpression>().symbol;
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
                    if (!context.scope->isUninstantiated())
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
    explicit CastTask(const std::string& name) : SystemTaskBase(name) { hasOutputArgs = true; }

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        if (argIndex == 0)
            return Expression::bindLValue(syntax, context);
        return Expression::bind(syntax, context);
    }

    // Return type is 'int' but the actual value is always either 0 or 1
    std::optional<bitwidth_t> getEffectiveWidth() const final { return 1; }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
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

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        if ((isFullMethod && argIndex < 4) || (!isFullMethod && argIndex == 0) ||
            !NameSyntax::isKind(syntax.kind)) {
            return SystemTaskBase::bindArgument(argIndex, context, syntax, args);
        }

        return ArbitrarySymbolExpression::fromSyntax(context.getCompilation(),
                                                     syntax.as<NameSyntax>(), context);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
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
                if (args[i]->kind != ExpressionKind::ArbitrarySymbol ||
                    !args[i]->as<ArbitrarySymbolExpression>().symbol->isScope()) {
                    if (!context.scope->isUninstantiated())
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
        inputArgs(inputArgs), outputArgs(outputArgs) {
        hasOutputArgs = outputArgs > 0;
    }

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        size_t totalArgs = inputArgs + outputArgs;
        if (argIndex >= inputArgs && argIndex < totalArgs)
            return Expression::bindLValue(syntax, context);
        return Expression::bind(syntax, context);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        size_t totalArgs = inputArgs + outputArgs;
        if (!checkArgCount(context, false, args, range, totalArgs, totalArgs))
            return comp.getErrorType();

        for (size_t i = 0; i < totalArgs; i++) {
            if (!args[i]->type->isIntegral())
                return badArg(context, *args[i]);
        }

        return kind == SubroutineKind::Function ? comp.getIntType() : comp.getVoidType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }

private:
    size_t inputArgs;
    size_t outputArgs;
};

class SdfAnnotateTask : public SystemTaskBase {
public:
    SdfAnnotateTask() : SystemTaskBase("$sdf_annotate") {}

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        if (argIndex == 1) {
            auto& comp = context.getCompilation();
            if (!NameSyntax::isKind(syntax.kind)) {
                context.addDiag(diag::ExpectedModuleInstance, syntax.sourceRange());
                return *comp.emplace<InvalidExpression>(nullptr, comp.getErrorType());
            }

            auto& ref = ArbitrarySymbolExpression::fromSyntax(comp, syntax.as<NameSyntax>(),
                                                              context);

            if (ref.kind == ExpressionKind::ArbitrarySymbol) {
                auto& sym = *ref.as<ArbitrarySymbolExpression>().symbol;
                if (sym.kind != SymbolKind::Instance || !sym.as<InstanceSymbol>().isModule()) {
                    if (!context.scope->isUninstantiated())
                        context.addDiag(diag::ExpectedModuleInstance, ref.sourceRange);
                    return *comp.emplace<InvalidExpression>(&ref, comp.getErrorType());
                }
            }

            return ref;
        }

        return SystemTaskBase::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
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

class PlaTask : public SystemTaskBase {
public:
    PlaTask(const std::string& name) : SystemTaskBase(name){};

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();

        if (!checkArgCount(context, false, args, range, 3, 3))
            return comp.getErrorType();

        for (size_t i = 0; i < args.size(); i++) {
            auto& type = *args[i]->type;

            if (i == 0) {
                if (!type.isUnpackedArray()) {
                    return badArg(context, *args[i]);
                }

                auto& elemType = *type.getArrayElementType();
                if (!elemType.isSimpleBitVector() || elemType.isPredefinedInteger()) {
                    return badArg(context, *args[i]);
                }

                if (elemType.hasFixedRange() && !isValidRange(elemType)) {
                    return badRange(context, *args[i]);
                }
            }
            else {
                if (!type.isSimpleBitVector() || type.isPredefinedInteger()) {
                    return badArg(context, *args[i]);
                }
            }

            if (type.hasFixedRange() && !isValidRange(type)) {
                return badRange(context, *args[i]);
            }
        }

        return comp.getVoidType();
    }

private:
    static bool isValidRange(const Type& type) {
        ConstantRange range = type.getFixedRange();
        return range.right >= range.left;
    }

    static const Type& badRange(const ASTContext& context, const Expression& arg) {
        context.addDiag(diag::PlaRangeInAscendingOrder, arg.sourceRange) << *arg.type;
        return context.getCompilation().getErrorType();
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
    REGISTER(MonitorTask, "$strobe", LiteralBase::Decimal);
    REGISTER(MonitorTask, "$strobeb", LiteralBase::Binary);
    REGISTER(MonitorTask, "$strobeo", LiteralBase::Octal);
    REGISTER(MonitorTask, "$strobeh", LiteralBase::Hex);
    REGISTER(MonitorTask, "$monitor", LiteralBase::Decimal);
    REGISTER(MonitorTask, "$monitorb", LiteralBase::Binary);
    REGISTER(MonitorTask, "$monitoro", LiteralBase::Octal);
    REGISTER(MonitorTask, "$monitorh", LiteralBase::Hex);

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
    REGISTER(FileMonitorTask, "$fstrobe");
    REGISTER(FileMonitorTask, "$fstrobeb");
    REGISTER(FileMonitorTask, "$fstrobeo");
    REGISTER(FileMonitorTask, "$fstrobeh");
    REGISTER(FileMonitorTask, "$fmonitor");
    REGISTER(FileMonitorTask, "$fmonitorb");
    REGISTER(FileMonitorTask, "$fmonitoro");
    REGISTER(FileMonitorTask, "$fmonitorh");

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
                                                             std::vector<const Type*>{string_t}));
    c.addSystemSubroutine(std::make_unique<SdfAnnotateTask>());
    c.addSystemSubroutine(std::make_unique<StaticAssertTask>());

#define TASK(name, required, ...)                             \
    c.addSystemSubroutine(std::make_unique<SimpleSystemTask>( \
        name, c.getVoidType(), required, std::vector<const Type*>{__VA_ARGS__}))

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

#define PLA_TASK(name) c.addSystemSubroutine(std::make_unique<PlaTask>(name))
    for (auto& fmt : {"$array", "$plane"}) {
        for (auto& gate : {"$and", "$or", "$nand", "$nor"}) {
            for (auto& type : {"$async", "$sync"}) {
                std::string name(type);
                name.append(gate);
                name.append(fmt);
                PLA_TASK(name);
            }
        }
    }

#undef PLA_TASK
}

} // namespace slang::ast::builtins
