//------------------------------------------------------------------------------
// SystemSubroutine.cpp
// System-defined subroutine handling
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"

#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

bool SystemSubroutine::allowEmptyArgument(size_t) const {
    return false;
}

const Expression& SystemSubroutine::bindArgument(size_t, const BindContext& context,
                                                 const ExpressionSyntax& syntax) const {
    return Expression::bind(syntax, context);
}

string_view SystemSubroutine::kindStr() const {
    return kind == SubroutineKind::Task ? "task"sv : "function"sv;
}

bool SystemSubroutine::checkArgCount(const BindContext& context, bool isMethod, const Args& args,
                                     SourceRange callRange, size_t min, size_t max) {
    size_t provided = args.size();
    if (isMethod) {
        ASSERT(provided);
        provided--;
    }

    if (provided < min) {
        context.addDiag(diag::TooFewArguments, callRange) << min << provided;
        return false;
    }

    if (provided > max) {
        context.addDiag(diag::TooManyArguments, args[max]->sourceRange) << max << provided;
        return false;
    }

    for (auto arg : args) {
        if (arg->bad())
            return false;
    }

    return true;
}

const Type& SystemSubroutine::badArg(const BindContext& context, const Expression& arg) const {
    context.addDiag(diag::BadSystemSubroutineArg, arg.sourceRange) << *arg.type << kindStr();
    return context.getCompilation().getErrorType();
}

bool SystemSubroutine::notConst(EvalContext& context, SourceRange range) const {
    context.addDiag(diag::SysFuncNotConst, range) << name;
    return false;
}

BindContext SystemSubroutine::makeNonConst(const BindContext& ctx) {
    BindContext nonConstCtx(ctx);
    if (nonConstCtx.flags & BindFlags::Constant) {
        nonConstCtx.flags &= ~BindFlags::Constant;
        nonConstCtx.flags |= BindFlags::NoHierarchicalNames;
    }
    return nonConstCtx;
}

const Expression& SimpleSystemSubroutine::bindArgument(size_t argIndex, const BindContext& context,
                                                       const ExpressionSyntax& syntax) const {
    optional<BindContext> nonConstCtx;
    const BindContext* ctx = &context;
    if (allowNonConst) {
        nonConstCtx.emplace(makeNonConst(context));
        ctx = &nonConstCtx.value();
    }

    if (argIndex >= argTypes.size())
        return SystemSubroutine::bindArgument(argIndex, *ctx, syntax);

    return Expression::bindRValue(*argTypes[argIndex], syntax, syntax.getFirstToken().location(),
                                  *ctx);
}

const Type& SimpleSystemSubroutine::checkArguments(const BindContext& context, const Args& args,
                                                   SourceRange range) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, isMethod, args, range, requiredArgs, argTypes.size()))
        return comp.getErrorType();

    return *returnType;
}

} // namespace slang