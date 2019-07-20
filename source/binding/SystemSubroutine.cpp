//------------------------------------------------------------------------------
// SystemSubroutine.cpp
// System-defined subroutine handling.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"

#include "slang/binding/BindContext.h"
#include "slang/binding/Expressions.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/text/SFormat.h"

namespace slang {

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

    optional<SFormat> formatStr;
    span<const SFormat::Arg> specs;
    auto specIt = specs.begin();

    auto argIt = args.begin();
    while (argIt != args.end()) {
        auto arg = *argIt++;
        if (arg->bad())
            return false;

        const Type& type = *arg->type;
        if (specIt == specs.end()) {
            if (arg->kind == ExpressionKind::StringLiteral) {
                auto& lit = arg->as<StringLiteral>();
                formatStr.emplace(lit.getRawValue(), arg->sourceRange.start());

                if (!formatStr->valid()) {
                    context.scope.addDiags(formatStr->getDiagnostics());
                    return false;
                }

                specs = formatStr->specifiers();
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

} // namespace slang