//------------------------------------------------------------------------------
// MiscSystemFuncs.cpp
// Built-in miscellaneous system functions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/FormatHelpers.h"
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/symbols/ClassSymbols.h"

namespace slang::Builtins {

class SFormatFunction : public SystemSubroutine {
public:
    SFormatFunction() : SystemSubroutine("$sformatf", SubroutineKind::Function) {}

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

        return comp.getStringType();
    }

    ConstantValue eval(EvalContext& context, const Args& args,
                       const CallExpression::SystemCallInfo& callInfo) const final {
        ConstantValue formatStr = args[0]->eval(context).convertToStr();
        if (!formatStr)
            return nullptr;

        auto result = FmtHelpers::formatArgs(formatStr.str(), args[0]->sourceRange.start(),
                                             *callInfo.scope, context, args.subspan(1));
        if (!result)
            return nullptr;

        return *result;
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }
};

class ValuePlusArgsFunction : public SystemSubroutine {
public:
    ValuePlusArgsFunction() : SystemSubroutine("$value$plusargs", SubroutineKind::Function) {}

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
            ct = Lookup::getContainingClass(context.scope).first;

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

void registerMiscSystemFuncs(Compilation& c) {
#define REGISTER(name) c.addSystemSubroutine(std::make_unique<name##Function>())
    REGISTER(SFormat);
    REGISTER(ValuePlusArgs);
    REGISTER(ScopeRandomize);
#undef REGISTER

    c.addSystemMethod(SymbolKind::ClassType, std::make_unique<ClassRandomizeFunction>());
}

} // namespace slang::Builtins
