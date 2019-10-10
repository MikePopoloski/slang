//------------------------------------------------------------------------------
// SystemSubroutine.cpp
// System-defined subroutine handling.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"

#include "slang/binding/BindContext.h"
#include "slang/binding/Expressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/text/SFormat.h"

namespace slang {

const Expression& SystemSubroutine::bindArgument(size_t, const BindContext& context,
                                                 const ExpressionSyntax& syntax) const {
    return Expression::bind(syntax, context);
}

string_view SystemSubroutine::kindStr() const {
    return kind == SubroutineKind::Task ? "task"sv : "function"sv;
}

bool SystemSubroutine::checkArgCount(const BindContext& context, bool isMethod, const Args& args,
                                     SourceRange callRange, ptrdiff_t min, ptrdiff_t max) {
    ptrdiff_t provided = args.size();
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

bool SystemSubroutine::checkFormatArgs(const BindContext& context, const Args& args) {
    // TODO: empty args

    SmallVectorSized<SFormat::Arg, 8> specs;
    auto specIt = specs.begin();

    auto argIt = args.begin();
    while (argIt != args.end()) {
        auto arg = *argIt++;
        if (arg->bad())
            return false;

        const Type& type = *arg->type;
        if (specIt == specs.end()) {
            if (arg->kind == ExpressionKind::StringLiteral) {
                specs.clear();
                auto& lit = arg->as<StringLiteral>();

                Diagnostics diags;
                if (!SFormat::parseArgs(lit.getRawValue(), arg->sourceRange.start(), specs,
                                        diags)) {
                    context.scope.addDiags(diags);
                    return false;
                }

                specIt = specs.begin();
            }
            else if (type.isAggregate() && !type.isByteArray()) {
                context.addDiag(diag::FormatUnspecifiedType, arg->sourceRange) << type;
                return false;
            }
        }
        else {
            SFormat::Arg fmtArg = *specIt++;
            if (!SFormat::isArgTypeValid(fmtArg.type, type)) {
                context.addDiag(diag::FormatMismatchedType, arg->sourceRange)
                    << type << fmtArg.spec;
                return false;
            }
        }
    }

    // TODO: check for left over specifiers

    return true;
}

const Expression& SimpleSystemSubroutine::bindArgument(size_t argIndex, const BindContext& context,
                                                       const ExpressionSyntax& syntax) const {
    if (argIndex >= argTypes.size())
        return SystemSubroutine::bindArgument(argIndex, context, syntax);

    return Expression::bind(*argTypes[argIndex], syntax, syntax.getFirstToken().location(),
                            context);
}

const Type& SimpleSystemSubroutine::checkArguments(const BindContext& context, const Args& args,
                                                   SourceRange range) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, isMethod, args, range, ptrdiff_t(requiredArgs),
                       ptrdiff_t(argTypes.size()))) {
        return comp.getErrorType();
    }

    return *returnType;
}

} // namespace slang