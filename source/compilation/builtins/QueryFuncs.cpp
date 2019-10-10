//------------------------------------------------------------------------------
// QueryFuncs.cpp
// Built-in system functions to query data about types and arrays.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"

namespace slang::Builtins {

class BitsFunction : public SystemSubroutine {
public:
    BitsFunction() : SystemSubroutine("$bits", SubroutineKind::Function) {}

    const Expression& bindArgument(size_t, const BindContext& context,
                                   const ExpressionSyntax& syntax) const final {
        BindContext nonConstCtx(context);
        nonConstCtx.flags &= ~BindFlags::Constant;
        nonConstCtx.flags |= BindFlags::NoHierarchicalNames;
        return Expression::bind(syntax, nonConstCtx, BindFlags::AllowDataType);
    }

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        if (!args[0]->type->isBitstreamType()) {
            context.addDiag(diag::BadSystemSubroutineArg, args[0]->sourceRange)
                << *args[0]->type << kindStr();
            return comp.getErrorType();
        }

        // TODO: not allowed on some dynamic types

        return comp.getIntegerType();
    }

    ConstantValue eval(EvalContext&, const Args& args) const final {
        // TODO: support for unpacked sizes
        return SVInt(32, args[0]->type->getBitWidth(), true);
    }

    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

class ArrayQueryFunction : public SystemSubroutine {
public:
    using SystemSubroutine::SystemSubroutine;

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        // TODO: support optional second argument
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        auto& type = *args[0]->type;
        if (!type.isIntegral() && !type.isUnpackedArray()) {
            context.addDiag(diag::BadSystemSubroutineArg, args[0]->sourceRange)
                << type << kindStr();
            return comp.getErrorType();
        }

        // TODO: not allowed on some dynamic types

        return comp.getIntegerType();
    }

    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

#define SUBROUTINE(className, base, ...)                                        \
    class className : public base {                                             \
    public:                                                                     \
        className() : base(__VA_ARGS__) {}                                      \
        ConstantValue eval(EvalContext& context, const Args& args) const final; \
    }

#define FUNC SubroutineKind::Function

SUBROUTINE(LowFunction, ArrayQueryFunction, "$low", FUNC);
SUBROUTINE(HighFunction, ArrayQueryFunction, "$high", FUNC);
SUBROUTINE(LeftFunction, ArrayQueryFunction, "$left", FUNC);
SUBROUTINE(RightFunction, ArrayQueryFunction, "$right", FUNC);
SUBROUTINE(SizeFunction, ArrayQueryFunction, "$size", FUNC);
SUBROUTINE(IncrementFunction, ArrayQueryFunction, "$increment", FUNC);

ConstantValue LowFunction::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)range.lower(), true);
}

ConstantValue HighFunction::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)range.upper(), true);
}

ConstantValue LeftFunction::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)range.left, true);
}

ConstantValue RightFunction::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)range.right, true);
}

ConstantValue SizeFunction::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, range.width(), true);
}

ConstantValue IncrementFunction::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)(range.isLittleEndian() ? 1 : -1), true);
}

void registerQueryFuncs(Compilation& c) {
#define REGISTER(name) c.addSystemSubroutine(std::make_unique<name##Function>())
    REGISTER(Bits);
    REGISTER(Low);
    REGISTER(High);
    REGISTER(Left);
    REGISTER(Right);
    REGISTER(Size);
    REGISTER(Increment);
#undef REGISTER
}

} // namespace slang::Builtins