//------------------------------------------------------------------------------
// NonConstFuncs.cpp
// Built-in non-constant system functions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"

namespace slang::Builtins {

class FErrorFunc : public SystemSubroutine {
public:
    FErrorFunc() : SystemSubroutine("$ferror", SubroutineKind::Function) {}

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, 2))
            return comp.getErrorType();

        if (!args[0]->type->isIntegral())
            return badArg(context, *args[0]);

        if (!args[1]->verifyAssignable(context))
            return comp.getErrorType();

        const Type& ft = *args[1]->type;
        if (!ft.canBeStringLike()) {
            context.addDiag(diag::InvalidStringArg, args[1]->sourceRange) << ft;
            return comp.getErrorType();
        }

        return comp.getIntegerType();
    }

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }
};

class FGetsFunc : public SystemSubroutine {
public:
    FGetsFunc() : SystemSubroutine("$fgets", SubroutineKind::Function) {}

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, 2))
            return comp.getErrorType();

        if (!args[0]->verifyAssignable(context))
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

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }
};

class ScanfFunc : public SystemSubroutine {
public:
    explicit ScanfFunc(bool isFscanf) :
        SystemSubroutine(isFscanf ? "$fscanf" : "$sscanf", SubroutineKind::Function),
        isFscanf(isFscanf) {}

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
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

        // Rest of the args can be anything. It would be nice to add some compile-time
        // checking of the format string here in the future.

        return comp.getIntegerType();
    }

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }

private:
    bool isFscanf;
};

class FReadFunc : public SystemSubroutine {
public:
    FReadFunc() : SystemSubroutine("$fread", SubroutineKind::Function) {}

    bool allowEmptyArgument(size_t argIndex) const final { return argIndex == 2; }

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 2, 4))
            return comp.getErrorType();

        if (!args[0]->verifyAssignable(context))
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

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }
};

class RandModeFunc : public SystemSubroutine {
public:
    RandModeFunc(const std::string& name) : SystemSubroutine(name, SubroutineKind::Task) {}

    const Type& checkArguments(const BindContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        // The number of arguments required is 1 if called as a task
        // and 0 if called as a function.
        auto& comp = context.getCompilation();
        size_t numArgs = context.flags.has(BindFlags::TopLevelStatement) ? 1 : 0;
        if (!checkArgCount(context, true, args, range, numArgs, numArgs))
            return comp.getErrorType();

        if (numArgs) {
            // First argument is integral.
            if (!args[1]->type->isIntegral())
                return badArg(context, *args[1]);
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

void registerNonConstFuncs(Compilation& c) {
#define REGISTER(...) c.addSystemSubroutine(std::make_unique<NonConstantFunction>(__VA_ARGS__))

    auto& intType = c.getIntType();
    auto& uintType = c.getUnsignedIntType();
    std::vector<const Type*> intArg = { &intType };

    REGISTER("$time", c.getTimeType());
    REGISTER("$stime", c.getUnsignedIntType());
    REGISTER("$realtime", c.getRealTimeType());
    REGISTER("$random", intType, 0, intArg);
    REGISTER("$urandom", uintType, 0, intArg);
    REGISTER("$urandom_range", uintType, 1, std::vector<const Type*>{ &uintType, &uintType });

    REGISTER("$fopen", intType, 1, std::vector{ &c.getStringType(), &c.getStringType() });
    REGISTER("$fclose", c.getVoidType(), 1, intArg);
    REGISTER("$fgetc", intType, 1, intArg);
    REGISTER("$ungetc", intType, 2, std::vector{ &intType, &intType });
    REGISTER("$ftell", intType, 1, intArg);
    REGISTER("$fseek", intType, 3, std::vector{ &intType, &intType, &intType });
    REGISTER("$rewind", intType, 1, intArg);
    REGISTER("$fflush", c.getVoidType(), 0, intArg);
    REGISTER("$feof", intType, 1, intArg);

    REGISTER("$test$plusargs", intType, 1, std::vector{ &c.getStringType() });

#undef REGISTER

    c.addSystemSubroutine(std::make_unique<FErrorFunc>());
    c.addSystemSubroutine(std::make_unique<FGetsFunc>());
    c.addSystemSubroutine(std::make_unique<ScanfFunc>(true));
    c.addSystemSubroutine(std::make_unique<ScanfFunc>(false));
    c.addSystemSubroutine(std::make_unique<FReadFunc>());

    c.addSystemMethod(SymbolKind::EventType,
                      std::make_unique<NonConstantFunction>("triggered", c.getBitType(), 0,
                                                            std::vector<const Type*>{},
                                                            /* isMethod */ true));

    c.addSystemMethod(SymbolKind::ClassProperty, std::make_unique<RandModeFunc>("rand_mode"));
    c.addSystemMethod(SymbolKind::ConstraintBlock,
                      std::make_unique<RandModeFunc>("constraint_mode"));
}

} // namespace slang::Builtins
