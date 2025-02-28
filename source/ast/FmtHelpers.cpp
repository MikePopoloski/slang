//------------------------------------------------------------------------------
// FmtHelpers.cpp
// Helpers for implementing the string formatting system functions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "FmtHelpers.h"

#include "slang/ast/EvalContext.h"
#include "slang/ast/Expression.h"
#include "slang/ast/SFormat.h"
#include "slang/ast/expressions/LiteralExpressions.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/util/String.h"

namespace slang::ast {

using Args = std::span<const Expression* const>;

static bool isValidForRaw(const Type& type) {
    if (type.isIntegral())
        return true;

    if (type.isUnpackedUnion()) {
        auto& uut = type.getCanonicalType().as<UnpackedUnionType>();
        for (auto& member : uut.members()) {
            if (!isValidForRaw(member.as<FieldSymbol>().getType()))
                return false;
        }
        return true;
    }
    else if (type.isUnpackedStruct()) {
        auto& ust = type.getCanonicalType().as<UnpackedStructType>();
        for (auto& member : ust.members()) {
            if (!isValidForRaw(member.as<FieldSymbol>().getType()))
                return false;
        }
        return true;
    }

    return false;
}

template<typename TContext>
static bool checkArgType(TContext& context, const Expression& arg, char spec, SourceRange range) {
    if (arg.bad())
        return false;

    auto& type = *arg.type;
    switch (charToLower(spec)) {
        case 'h':
        case 'x':
        case 'd':
        case 'o':
        case 'b':
        case 'c':
            if (type.isIntegral() || type.isString())
                return true;
            if (type.isFloating()) {
                // Just a warning, we will implicitly convert.
                context.addDiag(diag::FormatRealInt, arg.sourceRange) << spec << range;
                return true;
            }
            break;
        case 'e':
        case 'f':
        case 'g':
        case 't':
            if (type.isNumeric())
                return true;
            break;
        case 'v':
            if (type.isIntegral()) {
                if (type.getBitWidth() > 1)
                    context.addDiag(diag::FormatMultibitStrength, arg.sourceRange) << range;
                return true;
            }
            break;
        case 'u':
        case 'z':
            if (isValidForRaw(type))
                return true;
            break;
        case 'p':
            if (!type.isVoid())
                return true;
            break;
        case 's':
            if (type.canBeStringLike())
                return true;
            break;
        default:
            break;
    }

    context.addDiag(diag::FormatMismatchedType, arg.sourceRange) << type << spec << range;
    return false;
}

static bool checkFormatString(const ASTContext& context, const StringLiteral& arg,
                              Args::iterator& argIt, Args::iterator argEnd) {
    // Strip quotes from the raw string.
    std::string_view fmt = arg.getRawValue();
    if (fmt.length() >= 2)
        fmt = fmt.substr(1, fmt.length() - 2);

    SourceLocation loc = arg.sourceRange.start() + 1;
    auto getRange = [&](size_t offset, size_t len) {
        SourceLocation sl = loc + offset;
        return SourceRange{sl, sl + len};
    };

    bool ok = true;
    bool parseOk = SFormat::parse(
        fmt, [](std::string_view) {},
        [&](char spec, size_t offset, size_t len, const SFormat::FormatOptions&) {
            // Filter out non-consuming arguments.
            switch (charToLower(spec)) {
                case 'l':
                case 'm':
                    return;
                default:
                    break;
            }

            SourceRange range = getRange(offset, len);
            if (argIt == argEnd) {
                // If we've run out of arguments, this is an error.
                context.addDiag(diag::FormatNoArgument, range) << spec;
                ok = false;
                return;
            }

            auto arg = *argIt++;
            if (arg->kind == ExpressionKind::EmptyArgument) {
                // Empty arguments aren't allowed for format args.
                context.addDiag(diag::FormatEmptyArg, arg->sourceRange) << spec << range;
                ok = false;
                return;
            }

            ok &= checkArgType(context, *arg, spec, range);
        },
        [&](DiagCode code, size_t offset, size_t len, std::optional<char> specifier) {
            auto& diag = context.addDiag(code, getRange(offset, len));
            if (specifier)
                diag << *specifier;
        });

    return ok && parseOk;
}

bool FmtHelpers::checkDisplayArgs(const ASTContext& context, const Args& args) {
    auto argIt = args.begin();
    while (argIt != args.end()) {
        auto arg = *argIt++;
        if (arg->bad())
            return false;

        // Handle string literals as format strings.
        if (arg->kind == ExpressionKind::StringLiteral) {
            if (!checkFormatString(context, arg->as<StringLiteral>(), argIt, args.end()))
                return false;
        }
        else {
            const Type& type = *arg->type;
            if (type.isAggregate() && !type.isByteArray()) {
                context.addDiag(diag::FormatUnspecifiedType, arg->sourceRange) << type;
                return false;
            }
        }
    }

    return true;
}

bool FmtHelpers::checkSFormatArgs(const ASTContext& context, const Args& args) {
    // If the format string is known at compile time, check it for correctness now.
    // Otherwise this will wait until runtime.
    auto argIt = args.begin();
    auto arg = *argIt++;
    if (arg->kind != ExpressionKind::StringLiteral)
        return true;

    if (!checkFormatString(context, arg->as<StringLiteral>(), argIt, args.end()))
        return false;

    // Leftover arguments are invalid (all must be consumed by the format string).
    if (argIt != args.end()) {
        context.addDiag(diag::FormatTooManyArgs, (*argIt)->sourceRange);
        return false;
    }

    return true;
}

static bool formatSpecialArg(char spec, const Scope& scope, std::string& result) {
    switch (charToLower(spec)) {
        case 'l': {
            auto& sym = scope.asSymbol();
            if (auto lib = sym.getSourceLibrary()) {
                result += lib->name;
                result.push_back('.');
            }
            if (auto def = sym.getDeclaringDefinition())
                result += def->name;
            else
                result += "$unit";
            return true;
        }
        case 'm':
            scope.asSymbol().getHierarchicalPath(result);
            return true;
        default:
            return false;
    }
}

std::optional<std::string> FmtHelpers::formatArgs(std::string_view formatString, SourceLocation loc,
                                                  const Scope& scope, EvalContext& context,
                                                  const std::span<const Expression* const>& args,
                                                  bool isStringLiteral) {
    auto getRange = [&](size_t offset, size_t len) {
        // If this is not a string literal, we can't meaningfully get an offset.
        if (!isStringLiteral)
            return SourceRange{loc, loc};

        SourceLocation sl = loc + offset;
        return SourceRange{sl, sl + len};
    };

    std::string result;
    auto argIt = args.begin();

    bool ok = true;
    bool parseOk = SFormat::parse(
        formatString, [&](std::string_view text) { result += text; },
        [&](char spec, size_t offset, size_t len, const SFormat::FormatOptions& options) {
            if (formatSpecialArg(spec, scope, result))
                return;

            SourceRange range = getRange(offset, len);
            if (argIt == args.end()) {
                // If we've run out of arguments, this is an error.
                context.addDiag(diag::FormatNoArgument, range) << spec;
                ok = false;
                return;
            }

            auto arg = *argIt++;
            if (arg->kind == ExpressionKind::EmptyArgument) {
                // Empty arguments aren't allowed for format args.
                context.addDiag(diag::FormatEmptyArg, arg->sourceRange) << spec << range;
                ok = false;
                return;
            }

            if (!checkArgType(context, *arg, spec, range)) {
                ok = false;
                return;
            }

            auto&& value = arg->eval(context);
            if (!value) {
                ok = false;
                return;
            }

            SFormat::formatArg(result, value, *arg->type, spec, options, arg->isImplicitString());
        },
        [&](DiagCode code, size_t offset, size_t len, std::optional<char> specifier) {
            // If this is from a string literal format string, we already checked
            // the string at expression creation time, so don't re-issue diagnostics.
            if (isStringLiteral)
                return;

            auto& diag = context.addDiag(code, getRange(offset, len));
            if (specifier)
                diag << *specifier;
        });

    // Leftover arguments are invalid (all must be consumed by the format string).
    if (argIt != args.end())
        context.addDiag(diag::FormatTooManyArgs, (*argIt)->sourceRange);

    ok &= parseOk;
    if (!ok)
        return std::nullopt;

    return result;
}

static char getDefaultSpecifier(const Expression& expr, LiteralBase defaultBase) {
    auto& type = *expr.type;
    if (type.isIntegral()) {
        switch (defaultBase) {
            case LiteralBase::Decimal:
                return 'd';
            case LiteralBase::Octal:
                return 'o';
            case LiteralBase::Hex:
                return 'h';
            case LiteralBase::Binary:
                return 'b';
            default:
                SLANG_UNREACHABLE;
        }
    }

    if (type.isFloating())
        return 'f';

    if (type.isString())
        return 's';

    return 'p';
}

std::optional<std::string> FmtHelpers::formatDisplay(
    const Scope& scope, EvalContext& context, const std::span<const Expression* const>& args) {
    std::string result;
    auto argIt = args.begin();
    while (argIt != args.end()) {
        // Empty arguments always print a space.
        auto arg = *argIt++;
        if (arg->kind == ExpressionKind::EmptyArgument) {
            result.push_back(' ');
            continue;
        }

        // Handle string literals as format strings.
        if (arg->kind == ExpressionKind::StringLiteral) {
            // Strip quotes from the raw string.
            auto& lit = arg->as<StringLiteral>();
            std::string_view fmt = lit.getRawValue();
            if (fmt.length() >= 2)
                fmt = fmt.substr(1, fmt.length() - 2);

            bool ok = true;
            bool parseOk = SFormat::parse(
                fmt, [&](std::string_view text) { result += text; },
                [&](char specifier, size_t, size_t, const SFormat::FormatOptions& options) {
                    if (formatSpecialArg(specifier, scope, result))
                        return;

                    if (argIt != args.end()) {
                        auto currentArg = *argIt++;
                        auto&& value = currentArg->eval(context);
                        if (!value) {
                            ok = false;
                            return;
                        }

                        SFormat::formatArg(result, value, *currentArg->type, specifier, options,
                                           currentArg->isImplicitString());
                    }
                },
                [](DiagCode, size_t, size_t, std::optional<char>) {});

            ok &= parseOk;
            if (!ok)
                return std::nullopt;
        }
        else {
            // Otherwise, print the value with default options.
            auto&& value = arg->eval(context);
            if (!value)
                return std::nullopt;

            SFormat::formatArg(result, value, *arg->type,
                               getDefaultSpecifier(*arg, LiteralBase::Decimal), {},
                               arg->isImplicitString());
        }
    }

    return result;
}

bool FmtHelpers::checkFinishNum(const ASTContext& context, const Expression& arg) {
    ConstantValue cv = context.tryEval(arg);
    if (cv.isInteger()) {
        auto& val = cv.integer();
        if (val == 0 || val == 1 || val == 2)
            return true;
    }

    context.addDiag(diag::BadFinishNum, arg.sourceRange);
    return false;
}

} // namespace slang::ast
