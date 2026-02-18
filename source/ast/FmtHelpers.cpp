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
#include "slang/parsing/Lexer.h"
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

template<typename TContext, typename TRangeGetter>
static bool checkArgType(TContext& context, const Expression& arg, char spec,
                         TRangeGetter&& rangeGetter) {
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
            if (type.isIntegral() || type.isString() || type.isClass() || type.isNull() ||
                type.isCHandle())
                return true;
            if (type.isFloating()) {
                // Just a warning, we will implicitly convert.
                context.addDiag(diag::FormatRealInt, arg.sourceRange) << spec << rangeGetter();
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
                    context.addDiag(diag::FormatMultibitStrength, arg.sourceRange) << rangeGetter();
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

    context.addDiag(diag::FormatMismatchedType, arg.sourceRange) << type << spec << rangeGetter();
    return false;
}

static bool checkFormatString(const ASTContext& context, const StringLiteral& arg,
                              Args::iterator& argIt, Args::iterator argEnd) {
    auto getRange = [&arg](size_t offset, size_t len) {
        size_t charLen = 1;
        auto sl = arg.sourceRange.start() +
                  parsing::Lexer::getLocForStringChar(arg.getRawValue(), offset, charLen);
        sl -= charLen;
        return SourceRange{sl, sl + len + charLen - 1};
    };

    bool ok = true;
    bool parseOk = SFormat::parse(
        arg.getValue(), [](std::string_view) {},
        [&](char spec, size_t offset, size_t len, const SFormat::FormatOptions&) {
            // Filter out non-consuming arguments.
            switch (charToLower(spec)) {
                case 'l':
                case 'm':
                    return;
                default:
                    break;
            }

            if (argIt == argEnd) {
                // If we've run out of arguments, this is an error.
                context.addDiag(diag::FormatNoArgument, getRange(offset, len)) << spec;
                ok = false;
                return;
            }

            auto arg = *argIt++;
            if (arg->kind == ExpressionKind::EmptyArgument) {
                // Empty arguments aren't allowed for format args.
                context.addDiag(diag::FormatEmptyArg, arg->sourceRange)
                    << spec << getRange(offset, len);
                ok = false;
                return;
            }

            ok &= checkArgType(context, *arg, spec, [&]() { return getRange(offset, len); });
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
            scope.asSymbol().appendHierarchicalPath(result);
            return true;
        default:
            return false;
    }
}

std::optional<std::string> FmtHelpers::formatArgs(std::string_view formatString,
                                                  const Expression& formatExpr, const Scope& scope,
                                                  EvalContext& context,
                                                  const std::span<const Expression* const>& args) {
    std::string result;
    auto argIt = args.begin();

    bool ok = true;
    bool parseOk = SFormat::parse(
        formatString, [&](std::string_view text) { result += text; },
        [&](char spec, size_t, size_t, const SFormat::FormatOptions& options) {
            if (formatSpecialArg(spec, scope, result))
                return;

            if (argIt == args.end()) {
                // If we've run out of arguments, this is an error.
                context.addDiag(diag::FormatNoArgument, formatExpr.sourceRange) << spec;
                ok = false;
                return;
            }

            auto arg = *argIt++;
            if (arg->kind == ExpressionKind::EmptyArgument) {
                // Empty arguments aren't allowed for format args.
                context.addDiag(diag::FormatEmptyArg, formatExpr.sourceRange)
                    << spec << formatExpr.sourceRange;
                ok = false;
                return;
            }

            if (!checkArgType(context, *arg, spec, [&]() { return formatExpr.sourceRange; })) {
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
        [&](DiagCode code, size_t, size_t, std::optional<char> specifier) {
            // If this is from a string literal format string we already checked
            // the string at expression creation time, so don't re-issue diagnostics.
            if (formatExpr.kind == ExpressionKind::StringLiteral)
                return;

            auto& diag = context.addDiag(code, formatExpr.sourceRange);
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
            bool ok = true;
            bool parseOk = SFormat::parse(
                arg->as<StringLiteral>().getValue(), [&](std::string_view text) { result += text; },
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

void FmtHelpers::checkFinishNum(const ASTContext& context, const Expression& arg) {
    ConstantValue cv = context.tryEval(arg);
    if (cv.isInteger()) {
        auto& val = cv.integer();
        if (val == 0 || val == 1 || val == 2)
            return;
    }

    context.addDiag(diag::BadFinishNum, arg.sourceRange);
}

} // namespace slang::ast
