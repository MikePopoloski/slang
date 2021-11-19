//------------------------------------------------------------------------------
// MiscSystemFuncs.cpp
// Built-in miscellaneous system functions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/AssertionExpr.h"
#include "slang/binding/FormatHelpers.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/symbols/ASTVisitor.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/MemberSymbols.h"

namespace slang::Builtins {

class SFormatFunction : public SystemSubroutine {
public:
    SFormatFunction(const std::string& name, bool isNonStandard) :
        SystemSubroutine(name, SubroutineKind::Function), isNonStandard(isNonStandard) {}

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
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

    ConstantValue eval(EvalContext& context, const Args& args,
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

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }

private:
    bool isNonStandard;
};

class ValuePlusArgsFunction : public SystemSubroutine {
public:
    ValuePlusArgsFunction() : SystemSubroutine("$value$plusargs", SubroutineKind::Function) {
        hasOutputArgs = true;
    }

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, 2))
            return comp.getErrorType();

        const Type& ft = *args[0]->type;
        if (!ft.canBeStringLike()) {
            context.addDiag(diag::InvalidStringArg, args[0]->sourceRange) << ft;
            return comp.getErrorType();
        }

        if (!args[1]->verifyAssignable(context))
            return comp.getErrorType();

        // TODO: if the first argument is known at compile time, do more specific
        // checking of the second argument.
        const Type& st = *args[1]->type;
        if (!st.canBeStringLike() && !st.isFloating())
            return badArg(context, *args[1]);

        return comp.getIntType();
    }

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }
};

class ClassRandomizeFunction : public SystemSubroutine {
public:
    ClassRandomizeFunction() : SystemSubroutine("randomize", SubroutineKind::Function) {
        withClauseMode = WithClauseMode::Randomize;
    }

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
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

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }
};

class ScopeRandomizeFunction : public SystemSubroutine {
public:
    ScopeRandomizeFunction() : SystemSubroutine("randomize", SubroutineKind::Function) {
        withClauseMode = WithClauseMode::Randomize;
    }

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
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
            ASSERT(dt);
            if (!dt->getType().isValidForRand(RandMode::Rand)) {
                context.addDiag(diag::InvalidRandType, arg->sourceRange)
                    << dt->getType() << "rand"sv;
            }
        }

        return comp.getIntType();
    }

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }
};

class GlobalClockFunction : public SystemSubroutine {
public:
    GlobalClockFunction() : SystemSubroutine("$global_clock", SubroutineKind::Function) {}

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, 0))
            return comp.getErrorType();

        if (!context.flags.has(BindFlags::AllowClockingBlock)) {
            context.addDiag(diag::GlobalClockEventExpr, range);
            return comp.getErrorType();
        }

        if (!comp.getGlobalClocking(*context.scope)) {
            context.addDiag(diag::NoGlobalClocking, range);
            return comp.getErrorType();
        }

        return comp.getType(SyntaxKind::EventType);
    }

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }
};

struct SequenceMethodExprVisitor {
    const BindContext& context;
    std::string name;

    SequenceMethodExprVisitor(const BindContext& context, std::string name) :
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

        if constexpr (is_detected_v<ASTDetectors::visitExprs_t, T, SequenceMethodExprVisitor>)
            expr.visitExprs(*this);
    }

    void visitInvalid(const Expression&) {}
    void visitInvalid(const AssertionExpr&) {}
};

class SequenceMethod : public SystemSubroutine {
public:
    SequenceMethod(const std::string& name) : SystemSubroutine(name, SubroutineKind::Function) {}

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        checkLocalVars(*args[0], context, range);

        return comp.getBitType();
    }

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }

private:
    template<typename T>
    struct always_false : std::false_type {};

    void checkLocalVars(const Expression& expr, const BindContext& context,
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
                if (arg.localVarDirection == ArgumentDirection::In ||
                    arg.localVarDirection == ArgumentDirection::InOut) {
                    auto& diag = context.addDiag(diag::SeqMethodInputLocalVar, range);
                    diag << name;
                    diag.addNote(diag::NoteDeclarationHere, arg.location);
                    return;
                }
            }

            // Arguments to sequence instances that have triggered invoked can only
            // reference local variables if that is the entire argument.
            SequenceMethodExprVisitor visitor(context, name);
            for (auto& [formal, arg_] : aie.arguments) {
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
                    arg_);
            }
        }
    }
};

void registerMiscSystemFuncs(Compilation& c) {
#define REGISTER(name) c.addSystemSubroutine(std::make_unique<name##Function>())
    REGISTER(ValuePlusArgs);
    REGISTER(ScopeRandomize);
    REGISTER(GlobalClock);
#undef REGISTER

    c.addSystemSubroutine(std::make_unique<SFormatFunction>("$sformatf", false));
    c.addSystemSubroutine(std::make_unique<SFormatFunction>("$psprintf", true));

    c.addSystemMethod(SymbolKind::ClassType, std::make_unique<ClassRandomizeFunction>());
    c.addSystemMethod(SymbolKind::SequenceType, std::make_unique<SequenceMethod>("triggered"));
    c.addSystemMethod(SymbolKind::SequenceType, std::make_unique<SequenceMethod>("matched"));
}

} // namespace slang::Builtins
