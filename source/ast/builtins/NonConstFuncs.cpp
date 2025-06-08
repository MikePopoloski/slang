//------------------------------------------------------------------------------
// NonConstFuncs.cpp
// Built-in non-constant system functions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "Builtins.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast::builtins {

using namespace syntax;

class FErrorFunc : public SystemSubroutine {
public:
    FErrorFunc() : SystemSubroutine(KnownSystemName::FError, SubroutineKind::Function) {
        hasOutputArgs = true;
    }

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        if (argIndex == 1)
            return Expression::bindLValue(syntax, context);
        return Expression::bind(syntax, context);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, 2))
            return comp.getErrorType();

        if (!args[0]->type->isIntegral())
            return badArg(context, *args[0]);

        const Type& ft = *args[1]->type;
        if (!ft.canBeStringLike()) {
            context.addDiag(diag::InvalidStringArg, args[1]->sourceRange) << ft;
            return comp.getErrorType();
        }

        return comp.getIntegerType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class FGetsFunc : public SystemSubroutine {
public:
    FGetsFunc() : SystemSubroutine(KnownSystemName::FGets, SubroutineKind::Function) {
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
        if (!checkArgCount(context, false, args, range, 2, 2))
            return comp.getErrorType();

        const Type& ft = *args[0]->type;
        if (!ft.canBeStringLike()) {
            context.addDiag(diag::InvalidStringArg, args[0]->sourceRange) << ft;
            return comp.getErrorType();
        }

        if (!args[1]->type->isIntegral())
            return badArg(context, *args[1]);

        return comp.getIntegerType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class ScanfFunc : public SystemSubroutine {
public:
    explicit ScanfFunc(bool isFscanf) :
        SystemSubroutine(isFscanf ? KnownSystemName::FScanf : KnownSystemName::SScanf,
                         SubroutineKind::Function),
        isFscanf(isFscanf) {
        hasOutputArgs = true;
    }

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        if (argIndex >= 2)
            return Expression::bindLValue(syntax, context);
        return Expression::bind(syntax, context);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, INT32_MAX))
            return comp.getErrorType();

        // First argument is an fd or a string.
        if (isFscanf) {
            if (!args[0]->type->isIntegral())
                return badArg(context, *args[0]);
        }
        else {
            if (!args[0]->type->canBeStringLike()) {
                context.addDiag(diag::InvalidStringArg, args[0]->sourceRange) << *args[0]->type;
                return comp.getErrorType();
            }
        }

        // Second arg is a format string.
        if (!args[1]->type->canBeStringLike()) {
            context.addDiag(diag::InvalidStringArg, args[1]->sourceRange) << *args[1]->type;
            return comp.getErrorType();
        }

        // TODO: add some compile-time checking of the format string here
        return comp.getIntegerType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }

private:
    bool isFscanf;
};

class FReadFunc : public SystemSubroutine {
public:
    FReadFunc() : SystemSubroutine(KnownSystemName::FRead, SubroutineKind::Function) {
        hasOutputArgs = true;
    }

    bool allowEmptyArgument(size_t argIndex) const final { return argIndex == 2; }

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        if (argIndex == 0)
            return Expression::bindLValue(syntax, context);
        return Expression::bind(syntax, context);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, 4))
            return comp.getErrorType();

        // First argument is integral or an unpacked array.
        if (!args[0]->type->isIntegral() && !args[0]->type->isUnpackedArray())
            return badArg(context, *args[0]);

        // Second argument is an fd (integral).
        if (!args[1]->type->isIntegral())
            return badArg(context, *args[1]);

        if (args.size() > 2) {
            // Third arg can be empty or integral.
            if (args[2]->kind != ExpressionKind::EmptyArgument && !args[2]->type->isIntegral())
                return badArg(context, *args[2]);

            if (args.size() > 3) {
                // Fourth arg must be integral.
                if (!args[3]->type->isIntegral())
                    return badArg(context, *args[3]);
            }
        }

        return comp.getIntegerType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class RandModeFunc : public SystemSubroutine {
public:
    RandModeFunc(KnownSystemName knownNameId) :
        SystemSubroutine(knownNameId, SubroutineKind::Function) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        // The number of arguments required is 1 if called as a task
        // and 0 if called as a function.
        auto& comp = context.getCompilation();
        size_t numArgs = context.flags.has(ASTFlags::TopLevelStatement) ? 1 : 0;
        if (!checkArgCount(context, true, args, range, numArgs, numArgs))
            return comp.getErrorType();

        if (numArgs) {
            // First argument is integral.
            if (!args[1]->type->isIntegral())
                return badArg(context, *args[1]);
        }

        return numArgs ? comp.getVoidType() : comp.getIntType();
    }

    // Return type is 'int' but the actual value is always either 0 or 1
    std::optional<bitwidth_t> getEffectiveWidth() const final { return 1; }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class DistributionFunc : public SystemSubroutine {
public:
    DistributionFunc(KnownSystemName knownNameId, size_t numArgs) :
        SystemSubroutine(knownNameId, SubroutineKind::Function), numArgs(numArgs) {
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
        if (!checkArgCount(context, false, args, range, numArgs, numArgs))
            return comp.getErrorType();

        for (size_t i = 0; i < numArgs; i++) {
            if (!args[i]->type->isIntegral())
                return badArg(context, *args[i]);
        }

        return comp.getIntType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }

private:
    size_t numArgs;
};

class SampledFunc : public SystemSubroutine {
public:
    SampledFunc() : SystemSubroutine(KnownSystemName::Sampled, SubroutineKind::Function) {}

    const Expression& bindArgument(size_t, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        return Expression::bind(syntax, context, ASTFlags::AssertionExpr);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        AssertionExpr::checkSampledValueExpr(*args[0], context, false, diag::SampledValueLocalVar,
                                             diag::SampledValueMatched);

        return *args[0]->type;
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class ValueChangeFunc : public SystemSubroutine {
public:
    ValueChangeFunc(KnownSystemName knownNameId) :
        SystemSubroutine(knownNameId, SubroutineKind::Function) {}

    const Expression& bindArgument(size_t, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        return Expression::bind(syntax, context, ASTFlags::AssertionExpr);
    }

    bool allowClockingArgument(size_t argIndex) const final { return argIndex == 1; }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 2))
            return comp.getErrorType();

        AssertionExpr::checkSampledValueExpr(*args[0], context, false, diag::SampledValueLocalVar,
                                             diag::SampledValueMatched);

        if (args.size() == 2 && args[1]->kind != ExpressionKind::ClockingEvent)
            return badArg(context, *args[1]);

        return comp.getBitType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class PastFunc : public SystemSubroutine {
public:
    PastFunc() : SystemSubroutine(KnownSystemName::Past, SubroutineKind::Function) {}

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        bitmask<ASTFlags> extraFlags = ASTFlags::None;
        if (argIndex == 0 || argIndex == 2)
            extraFlags = ASTFlags::AssertionExpr;

        if (argIndex == 2)
            extraFlags |= ASTFlags::NonProcedural;

        return Expression::bind(syntax, context, extraFlags);
    }

    bool allowEmptyArgument(size_t argIndex) const final { return argIndex == 1 || argIndex == 2; }
    bool allowClockingArgument(size_t argIndex) const final { return argIndex == 3; }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 4))
            return comp.getErrorType();

        for (size_t i = 0; i < args.size() && i < 3; i++) {
            AssertionExpr::checkSampledValueExpr(*args[i], context, false,
                                                 diag::SampledValueLocalVar,
                                                 diag::SampledValueMatched);
        }

        if (args.size() > 1 && args[1]->kind != ExpressionKind::EmptyArgument) {
            auto numTicks = context.evalInteger(*args[1]);
            if (numTicks && *numTicks < 1)
                context.addDiag(diag::PastNumTicksInvalid, args[1]->sourceRange);
        }

        if (args.size() > 2 && args[2]->kind != ExpressionKind::EmptyArgument) {
            if (!context.requireBooleanConvertible(*args[2]))
                return comp.getErrorType();
        }

        if (args.size() > 3 && args[3]->kind != ExpressionKind::ClockingEvent)
            return badArg(context, *args[3]);

        return *args[0]->type;
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class GlobalValueChangeFunc : public SystemSubroutine {
public:
    GlobalValueChangeFunc(KnownSystemName knownNameId, bool isFuture) :
        SystemSubroutine(knownNameId, SubroutineKind::Function), isFuture(isFuture) {}

    const Expression& bindArgument(size_t, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        return Expression::bind(syntax, context, ASTFlags::AssertionExpr);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        if (!comp.getGlobalClockingAndNoteUse(*context.scope)) {
            if (!context.scope->isUninstantiated())
                context.addDiag(diag::NoGlobalClocking, range);
            return comp.getErrorType();
        }

        if (!context.flags.has(ASTFlags::AssertionExpr) && isFuture) {
            context.addDiag(diag::GlobalSampledValueAssertionExpr, range);
            return comp.getErrorType();
        }

        AssertionExpr::checkSampledValueExpr(*args[0], context, isFuture,
                                             diag::SampledValueLocalVar, diag::SampledValueMatched);

        return comp.getBitType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }

private:
    bool isFuture;
};

class TimeScaleFunc : public SystemSubroutine {
public:
    TimeScaleFunc(KnownSystemName knownNameId, bool isOptional) :
        SystemSubroutine(knownNameId, SubroutineKind::Function), isOptional(isOptional) {}

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        if (argIndex == 0) {
            auto& comp = context.getCompilation();
            if (!NameSyntax::isKind(syntax.kind)) {
                context.addDiag(diag::ExpectedModuleName, syntax.sourceRange());
                return *comp.emplace<InvalidExpression>(nullptr, comp.getErrorType());
            }

            bitmask<LookupFlags> extraFlags;
            if (isOptional)
                extraFlags = LookupFlags::AllowRoot | LookupFlags::AllowUnit;

            return ArbitrarySymbolExpression::fromSyntax(comp, syntax.as<NameSyntax>(), context,
                                                         extraFlags);
        }

        return SystemSubroutine::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, isOptional ? 0 : 1, 1))
            return comp.getErrorType();

        if (isOptional) {
            auto languageVersion = comp.languageVersion();
            if (languageVersion < LanguageVersion::v1800_2023)
                context.addDiag(diag::WrongLanguageVersion, range) << toString(languageVersion);
        }

        if (args.size() > 0) {
            auto& sym = *args[0]->as<ArbitrarySymbolExpression>().symbol;
            if (sym.kind != SymbolKind::Instance && sym.kind != SymbolKind::CompilationUnit &&
                sym.kind != SymbolKind::Root) {
                if (!context.scope->isUninstantiated())
                    context.addDiag(diag::ExpectedModuleName, args[0]->sourceRange);
                return comp.getErrorType();
            }
        }

        return comp.getIntType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }

private:
    bool isOptional;
};

class StacktraceFunc : public SystemSubroutine {
public:
    StacktraceFunc() : SystemSubroutine(KnownSystemName::Stacktrace, SubroutineKind::Function) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, 0))
            return comp.getErrorType();

        return context.flags.has(ASTFlags::TopLevelStatement) ? comp.getVoidType()
                                                              : comp.getStringType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class CountDriversFunc : public SystemSubroutine {
public:
    CountDriversFunc() : SystemSubroutine(KnownSystemName::CountDrivers, SubroutineKind::Function) {
        hasOutputArgs = true;
    }

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        if (argIndex > 0) {
            return Expression::bindArgument(context.getCompilation().getIntType(),
                                            ArgumentDirection::Out, {}, syntax, context);
        }
        return Expression::bind(syntax, context);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 6))
            return comp.getErrorType();

        auto sym = args[0]->getSymbolReference(/* allowPacked */ false);
        if (!sym || sym->kind != SymbolKind::Net)
            context.addDiag(diag::ExpectedNetRef, args[0]->sourceRange);

        return comp.getBitType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class GetPatternFunc : public SystemSubroutine {
public:
    GetPatternFunc() : SystemSubroutine(KnownSystemName::GetPattern, SubroutineKind::Function) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        if (!args[0]->type->isIntegral())
            return badArg(context, *args[0]);

        return comp.getType(args[0]->type->getBitWidth(), {});
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class TestPlusArgsFunction : public NonConstantFunction {
public:
    TestPlusArgsFunction(const Builtins& builtins) :
        NonConstantFunction(KnownSystemName::TestPlusArgs, builtins.intType, 1,
                            std::vector<const Type*>{&builtins.stringType}) {}

    // Return type is 'int' but the actual value is always either 0 or 1
    std::optional<bitwidth_t> getEffectiveWidth() const final { return 1; }
};

void Builtins::registerNonConstFuncs() {
    using parsing::KnownSystemName;

#define REGISTER(...) addSystemSubroutine(std::make_shared<NonConstantFunction>(__VA_ARGS__))

    std::vector<const Type*> intArg = {&intType};

    REGISTER(KnownSystemName::Time, timeType);
    REGISTER(KnownSystemName::STime, uintType);
    REGISTER(KnownSystemName::RealTime, realTimeType);
    REGISTER(KnownSystemName::Random, intType, 0, intArg);
    REGISTER(KnownSystemName::URandom, uintType, 0, intArg);
    REGISTER(KnownSystemName::URandomRange, uintType, 1,
             std::vector<const Type*>{&uintType, &uintType});

    REGISTER(KnownSystemName::FOpen, intType, 1,
             std::vector<const Type*>{&stringType, &stringType});
    REGISTER(KnownSystemName::FClose, voidType, 1, intArg);
    REGISTER(KnownSystemName::FGetC, intType, 1, intArg);
    REGISTER(KnownSystemName::UngetC, intType, 2, std::vector<const Type*>{&intType, &intType});
    REGISTER(KnownSystemName::FTell, intType, 1, intArg);
    REGISTER(KnownSystemName::FSeek, intType, 3,
             std::vector<const Type*>{&intType, &intType, &intType});
    REGISTER(KnownSystemName::Rewind, intType, 1, intArg);
    REGISTER(KnownSystemName::FFlush, voidType, 0, intArg);
    REGISTER(KnownSystemName::FEof, intType, 1, intArg);

    REGISTER(KnownSystemName::ResetCount, intType, 0);
    REGISTER(KnownSystemName::ResetValue, intType, 0);

#undef REGISTER

#define FUNC(name, numArgs) addSystemSubroutine(std::make_shared<DistributionFunc>(name, numArgs))
    FUNC(KnownSystemName::DistUniform, 3);
    FUNC(KnownSystemName::DistNormal, 3);
    FUNC(KnownSystemName::DistExponential, 2);
    FUNC(KnownSystemName::DistPoisson, 2);
    FUNC(KnownSystemName::DistChiSquare, 2);
    FUNC(KnownSystemName::DistT, 2);
    FUNC(KnownSystemName::DistErlang, 3);
#undef FUNC

#define FUNC(name) addSystemSubroutine(std::make_shared<ValueChangeFunc>(name))
    FUNC(KnownSystemName::Rose);
    FUNC(KnownSystemName::Fell);
    FUNC(KnownSystemName::Stable);
    FUNC(KnownSystemName::Changed);
#undef FUNC

#define FUNC(name, isFuture) \
    addSystemSubroutine(std::make_shared<GlobalValueChangeFunc>(name, isFuture))
    FUNC(KnownSystemName::PastGclk, false);
    FUNC(KnownSystemName::RoseGclk, false);
    FUNC(KnownSystemName::FellGclk, false);
    FUNC(KnownSystemName::StableGclk, false);
    FUNC(KnownSystemName::ChangedGclk, false);
    FUNC(KnownSystemName::FutureGclk, true);
    FUNC(KnownSystemName::RisingGclk, true);
    FUNC(KnownSystemName::FallingGclk, true);
    FUNC(KnownSystemName::SteadyGclk, true);
    FUNC(KnownSystemName::ChangingGclk, true);
#undef FUNC

    addSystemSubroutine(std::make_shared<FErrorFunc>());
    addSystemSubroutine(std::make_shared<FGetsFunc>());
    addSystemSubroutine(std::make_shared<ScanfFunc>(true));
    addSystemSubroutine(std::make_shared<ScanfFunc>(false));
    addSystemSubroutine(std::make_shared<FReadFunc>());
    addSystemSubroutine(std::make_shared<SampledFunc>());
    addSystemSubroutine(std::make_shared<PastFunc>());
    addSystemSubroutine(std::make_shared<TimeScaleFunc>(KnownSystemName::TimeUnit, true));
    addSystemSubroutine(std::make_shared<TimeScaleFunc>(KnownSystemName::TimePrecision, true));
    addSystemSubroutine(std::make_shared<TimeScaleFunc>(KnownSystemName::Scale, false));
    addSystemSubroutine(std::make_shared<StacktraceFunc>());
    addSystemSubroutine(std::make_shared<CountDriversFunc>());
    addSystemSubroutine(std::make_shared<GetPatternFunc>());
    addSystemSubroutine(std::make_shared<TestPlusArgsFunction>(*this));

    addSystemMethod(SymbolKind::EventType,
                    std::make_shared<NonConstantFunction>(KnownSystemName::Triggered, bitType, 0,
                                                          std::vector<const Type*>{},
                                                          /* isMethod */ true));

    addSystemMethod(SymbolKind::ClassProperty,
                    std::make_shared<RandModeFunc>(KnownSystemName::RandMode));
    addSystemMethod(SymbolKind::ConstraintBlock,
                    std::make_shared<RandModeFunc>(KnownSystemName::ConstraintMode));
}

} // namespace slang::ast::builtins
