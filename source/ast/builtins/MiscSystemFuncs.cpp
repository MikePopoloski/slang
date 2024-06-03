//------------------------------------------------------------------------------
// MiscSystemFuncs.cpp
// Built-in miscellaneous system functions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "../FmtHelpers.h"
#include "Builtins.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/expressions/AssertionExpr.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/SysFuncsDiags.h"

namespace slang::ast::builtins {

using namespace syntax;

class SFormatFunction : public SystemSubroutine {
public:
    SFormatFunction(const std::string& name, bool isNonStandard) :
        SystemSubroutine(name, SubroutineKind::Function), isNonStandard(isNonStandard) {}

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

        if (!FmtHelpers::checkSFormatArgs(context, args))
            return comp.getErrorType();

        if (isNonStandard)
            context.addDiag(diag::NonstandardSysFunc, range) << name;

        return comp.getStringType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo& callInfo) const final {
        ConstantValue formatStr = args[0]->eval(context).convertToStr();
        if (!formatStr)
            return nullptr;

        auto result = FmtHelpers::formatArgs(formatStr.str(), args[0]->sourceRange.start(),
                                             *callInfo.scope, context, args.subspan(1),
                                             args[0]->kind == ExpressionKind::StringLiteral);
        if (!result)
            return nullptr;

        return *result;
    }

private:
    bool isNonStandard;
};

class ValuePlusArgsFunction : public SystemSubroutine {
public:
    ValuePlusArgsFunction() : SystemSubroutine("$value$plusargs", SubroutineKind::Function) {
        hasOutputArgs = true;
    }

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        if (argIndex == 1)
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

        const Type& ft = *args[0]->type;
        if (!ft.canBeStringLike()) {
            context.addDiag(diag::InvalidStringArg, args[0]->sourceRange) << ft;
            return comp.getErrorType();
        }

        // TODO: if the first argument is known at compile time, do more specific
        // checking of the second argument.
        const Type& st = *args[1]->type;
        if (!st.canBeStringLike() && !st.isFloating())
            return badArg(context, *args[1]);

        return comp.getIntType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class ClassRandomizeFunction : public SystemSubroutine {
public:
    ClassRandomizeFunction() : SystemSubroutine("randomize", SubroutineKind::Function) {
        withClauseMode = WithClauseMode::Randomize;
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression* thisExpr) const final {
        bool isMethod = thisExpr != nullptr;
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, isMethod, args, range, 0, INT32_MAX))
            return comp.getErrorType();

        Args methodArgs = args;
        if (isMethod)
            methodArgs = methodArgs.subspan(1);

        // Special case: a single 'null' argument can be passed to indicate
        // that no variables should be randomized.
        if (methodArgs.size() == 1 && methodArgs[0]->type->isNull())
            return comp.getIntType();

        // This can only be called via a special lookup on a class handle or as a local
        // class member, so we know either the this expression gives us the class type
        // or we can look it up from our current scope.
        const Scope* ct;
        if (thisExpr)
            ct = &thisExpr->type->getCanonicalType().as<ClassType>();
        else
            ct = Lookup::getContainingClass(*context.scope).first;

        if (!ct)
            return comp.getErrorType();

        for (auto arg : methodArgs) {
            if (arg->kind != ExpressionKind::NamedValue) {
                context.addDiag(diag::ExpectedClassPropertyName, arg->sourceRange);
                return comp.getErrorType();
            }

            auto sym = arg->getSymbolReference();
            if (!sym || sym->kind != SymbolKind::ClassProperty || sym->getParentScope() != ct) {
                context.addDiag(diag::ExpectedClassPropertyName, arg->sourceRange);
                return comp.getErrorType();
            }
        }

        return comp.getIntType();
    }

    // Return type is 'int' but the actual value is always either 0 or 1
    std::optional<bitwidth_t> getEffectiveWidth() const final { return 1; }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class ScopeRandomizeFunction : public SystemSubroutine {
public:
    ScopeRandomizeFunction() : SystemSubroutine("randomize", SubroutineKind::Function) {
        withClauseMode = WithClauseMode::Randomize;
    }

    const Expression& bindArgument(size_t, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args&) const final {
        return Expression::bindLValue(syntax, context);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, INT32_MAX))
            return comp.getErrorType();

        for (auto arg : args) {
            auto sym = arg->getSymbolReference();
            if (!sym || arg->kind != ExpressionKind::NamedValue) {
                context.addDiag(diag::ExpectedVariableName, arg->sourceRange);
                return comp.getErrorType();
            }

            auto dt = sym->getDeclaredType();
            SLANG_ASSERT(dt);
            if (!dt->getType().isValidForRand(RandMode::Rand, comp.languageVersion())) {
                context.addDiag(diag::InvalidRandType, arg->sourceRange)
                    << dt->getType() << "rand"sv;
            }
        }

        return comp.getIntType();
    }

    // Return type is 'int' but the actual value is always either 0 or 1
    std::optional<bitwidth_t> getEffectiveWidth() const final { return 1; }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class GlobalClockFunction : public SystemSubroutine {
public:
    GlobalClockFunction() : SystemSubroutine("$global_clock", SubroutineKind::Function) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, 0))
            return comp.getErrorType();

        if (!context.flags.has(ASTFlags::AllowClockingBlock)) {
            context.addDiag(diag::GlobalClockEventExpr, range);
            return comp.getErrorType();
        }

        if (!comp.getGlobalClocking(*context.scope)) {
            if (!context.scope->isUninstantiated())
                context.addDiag(diag::NoGlobalClocking, range);
            return comp.getErrorType();
        }

        return comp.getType(SyntaxKind::EventType);
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class InferredValueFunction : public SystemSubroutine {
public:
    InferredValueFunction(const std::string& name, bool isClockFunc) :
        SystemSubroutine(name, SubroutineKind::Function), isClockFunc(isClockFunc) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, 0))
            return comp.getErrorType();

        if (!context.flags.has(ASTFlags::AssertionDefaultArg)) {
            context.addDiag(diag::InferredValDefArg, range) << name;
            return comp.getErrorType();
        }

        return isClockFunc ? comp.getType(SyntaxKind::EventType) : comp.getLogicType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }

private:
    bool isClockFunc;
};

struct SequenceMethodExprVisitor {
    const ASTContext& context;
    std::string name;

    SequenceMethodExprVisitor(const ASTContext& context, std::string name) :
        context(context), name(std::move(name)) {}

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_base_of_v<Expression, T>) {
            if (expr.kind == ExpressionKind::NamedValue) {
                if (auto sym = expr.getSymbolReference()) {
                    if (sym->kind == SymbolKind::LocalAssertionVar ||
                        (sym->kind == SymbolKind::AssertionPort &&
                         sym->template as<AssertionPortSymbol>().isLocalVar())) {
                        context.addDiag(diag::SequenceMethodLocalVar, expr.sourceRange) << name;
                    }
                }
            }
        }

        if constexpr (HasVisitExprs<T, SequenceMethodExprVisitor>)
            expr.visitExprs(*this);
    }
};

class SequenceMethod : public SystemSubroutine {
public:
    SequenceMethod(const std::string& name) : SystemSubroutine(name, SubroutineKind::Function) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        checkLocalVars(*args[0], context, range);

        return comp.getBitType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }

private:
    template<typename T>
    struct always_false : std::false_type {};

    void checkLocalVars(const Expression& expr, const ASTContext& context,
                        SourceRange range) const {
        if (expr.kind == ExpressionKind::AssertionInstance) {
            auto& aie = expr.as<AssertionInstanceExpression>();
            if (aie.symbol.kind == SymbolKind::AssertionPort) {
                if (aie.body.kind == AssertionExprKind::Simple)
                    checkLocalVars(aie.body.as<SimpleAssertionExpr>().expr, context, range);
                return;
            }

            auto& seq = aie.symbol.as<SequenceSymbol>();
            for (auto& arg : seq.membersOfType<AssertionPortSymbol>()) {
                if (arg.direction == ArgumentDirection::In ||
                    arg.direction == ArgumentDirection::InOut) {
                    auto& diag = context.addDiag(diag::SeqMethodInputLocalVar, range);
                    diag << name;
                    diag.addNote(diag::NoteDeclarationHere, arg.location);
                    return;
                }
            }

            // Arguments to sequence instances that have triggered invoked can only
            // reference local variables if that is the entire argument.
            SequenceMethodExprVisitor visitor(context, name);
            for (auto& [formal, actualArg] : aie.arguments) {
                std::visit(
                    [&visitor](auto&& arg) {
                        // Local vars are allowed at the top level, so we need to check if
                        // the entire argument is a named value and if so don't bother
                        // checking it.
                        using T = std::decay_t<decltype(arg)>;
                        if constexpr (std::is_same_v<T, const Expression*>) {
                            if (arg->kind != ExpressionKind::NamedValue)
                                arg->visit(visitor);
                        }
                        else if constexpr (std::is_same_v<T, const AssertionExpr*>) {
                            if (arg->kind == AssertionExprKind::Simple) {
                                auto& sae = arg->template as<SimpleAssertionExpr>();
                                if (sae.repetition || sae.expr.kind != ExpressionKind::NamedValue)
                                    arg->visit(visitor);
                            }
                            else {
                                arg->visit(visitor);
                            }
                        }
                        else if constexpr (std::is_same_v<T, const TimingControl*>) {
                            if (arg->kind == TimingControlKind::SignalEvent) {
                                auto& sec = arg->template as<SignalEventControl>();
                                if (sec.edge != EdgeKind::None || sec.iffCondition ||
                                    sec.expr.kind != ExpressionKind::NamedValue) {
                                    arg->visit(visitor);
                                }
                            }
                            else {
                                arg->visit(visitor);
                            }
                        }
                        else {
                            static_assert(always_false<T>::value, "Missing case");
                        }
                    },
                    actualArg);
            }
        }
    }
};

void Builtins::registerMiscSystemFuncs() {
#define REGISTER(name) addSystemSubroutine(std::make_shared<name##Function>())
    REGISTER(ValuePlusArgs);
    REGISTER(ScopeRandomize);
    REGISTER(GlobalClock);
#undef REGISTER

    addSystemSubroutine(std::make_shared<SFormatFunction>("$sformatf", false));
    addSystemSubroutine(std::make_shared<SFormatFunction>("$psprintf", true));

    addSystemSubroutine(std::make_shared<InferredValueFunction>("$inferred_clock", true));
    addSystemSubroutine(std::make_shared<InferredValueFunction>("$inferred_disable", false));

    addSystemMethod(SymbolKind::ClassType, std::make_shared<ClassRandomizeFunction>());
    addSystemMethod(SymbolKind::SequenceType, std::make_shared<SequenceMethod>("triggered"));
    addSystemMethod(SymbolKind::SequenceType, std::make_shared<SequenceMethod>("matched"));
}

} // namespace slang::ast::builtins
