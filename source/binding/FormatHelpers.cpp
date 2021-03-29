//------------------------------------------------------------------------------
// FormatHelpers.cpp
// Helpers for implementing the string formatting system functions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/FormatHelpers.h"

#include "slang/binding/Expression.h"
#include "slang/binding/LiteralExpressions.h"
#include "slang/compilation/Definition.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/mir/Procedure.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/text/SFormat.h"
#include "slang/types/AllTypes.h"

namespace slang {

using Args = span<const Expression* const>;

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
    switch (::tolower(spec)) {
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
            // Always valid.
            return true;
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

static bool checkFormatString(const BindContext& context, const StringLiteral& arg,
                              Args::iterator& argIt, Args::iterator argEnd) {
    // Strip quotes from the raw string.
    string_view fmt = arg.getRawValue();
    if (fmt.length() >= 2)
        fmt = fmt.substr(1, fmt.length() - 2);

    SourceLocation loc = arg.sourceRange.start() + 1;
    auto getRange = [&](size_t offset, size_t len) {
        SourceLocation sl = loc + offset;
        return SourceRange{ sl, sl + len };
    };

    bool ok = true;
    ok &= SFormat::parse(
        fmt, [](string_view) {},
        [&](char spec, size_t offset, size_t len, const SFormat::FormatOptions&) {
            // Filter out non-consuming arguments.
            switch (::tolower(spec)) {
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
        [&](DiagCode code, size_t offset, size_t len, optional<char> specifier) {
            auto& diag = context.addDiag(code, getRange(offset, len));
            if (specifier)
                diag << *specifier;
        });

    return ok;
}

bool FmtHelpers::checkDisplayArgs(const BindContext& context, const Args& args) {
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

bool FmtHelpers::checkSFormatArgs(const BindContext& context, const Args& args) {
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
    switch (::tolower(spec)) {
        case 'l':
            if (auto def = scope.asSymbol().getDeclaringDefinition())
                result += def->name;
            else
                result += "$unit";
            return true;
        case 'm':
            scope.asSymbol().getHierarchicalPath(result);
            return true;
        default:
            return false;
    }
}

optional<std::string> FmtHelpers::formatArgs(string_view formatString, SourceLocation loc,
                                             const Scope& scope, EvalContext& context,
                                             const span<const Expression* const>& args,
                                             bool isStringLiteral) {
    auto getRange = [&](size_t offset, size_t len) {
        // If this is not a string literal, we can't meaningfully get an offset.
        if (!isStringLiteral)
            return SourceRange{ loc, loc };

        SourceLocation sl = loc + offset;
        return SourceRange{ sl, sl + len };
    };

    std::string result;
    auto argIt = args.begin();

    bool ok = true;
    ok &= SFormat::parse(
        formatString, [&](string_view text) { result += text; },
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

            SFormat::formatArg(result, value, spec, options);
        },
        [&](DiagCode code, size_t offset, size_t len, optional<char> specifier) {
            // If this is from a string literal format string, we already checked
            // the string as expression binding time, so don't re-issue diagnostics.
            if (isStringLiteral)
                return;

            auto& diag = context.addDiag(code, getRange(offset, len));
            if (specifier)
                diag << *specifier;
        });

    // Leftover arguments are invalid (all must be consumed by the format string).
    if (argIt != args.end())
        context.addDiag(diag::FormatTooManyArgs, (*argIt)->sourceRange);

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
                THROW_UNREACHABLE;
        }
    }

    if (type.isFloating())
        return 'f';

    if (type.isString())
        return 's';

    return 'p';
}

optional<std::string> FmtHelpers::formatDisplay(const Scope& scope, EvalContext& context,
                                                const span<const Expression* const>& args) {
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
            string_view fmt = lit.getRawValue();
            if (fmt.length() >= 2)
                fmt = fmt.substr(1, fmt.length() - 2);

            bool ok = true;
            ok &= SFormat::parse(
                fmt, [&](string_view text) { result += text; },
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

                        SFormat::formatArg(result, value, specifier, options);
                    }
                },
                [](DiagCode, size_t, size_t, optional<char>) {});

            if (!ok)
                return std::nullopt;
        }
        else {
            // Otherwise, print the value with default options.
            auto&& value = arg->eval(context);
            if (!value)
                return std::nullopt;

            SFormat::formatArg(result, value, getDefaultSpecifier(*arg, LiteralBase::Decimal), {});
        }
    }

    return result;
}

static void lowerFormatArg(mir::Procedure& proc, const Expression& arg, char,
                           const SFormat::FormatOptions& options, LiteralBase defaultBase) {
    // TODO: actually use the options
    mir::MIRValue argVal = proc.emitExpr(arg);
    const Type& type = arg.type->getCanonicalType();
    if (type.isIntegral()) {
        auto args = { argVal, proc.emitInt(8, uint64_t(defaultBase), false),
                      proc.emitInt(32, options.width.value_or(0), false),
                      proc.emitInt(1, options.width.has_value(), false) };
        proc.emitCall(mir::SysCallKind::printInt, args);
        return;
    }

    switch (type.kind) {
        case SymbolKind::FloatingType:
        case SymbolKind::StringType:
        case SymbolKind::EventType:
        case SymbolKind::CHandleType:
        case SymbolKind::ClassType:
        case SymbolKind::NullType:
            THROW_UNREACHABLE;
        default:
            // Should only be reachable by invalid display calls,
            // in which case an error will already have been reported.
            break;
    }
}

void FmtHelpers::lowerFormatArgs(mir::Procedure& proc, const Args& args, LiteralBase defaultBase,
                                 bool newline) {
    auto argIt = args.begin();
    while (argIt != args.end()) {
        auto arg = *argIt++;
        if (arg->bad())
            return;

        // Empty arguments always print a space.
        if (arg->kind == ExpressionKind::EmptyArgument) {
            proc.emitCall(mir::SysCallKind::printStr, proc.emitString(" "));
            continue;
        }

        // Handle string literals as format strings.
        if (arg->kind == ExpressionKind::StringLiteral) {
            // Strip quotes from the raw string.
            auto& lit = arg->as<StringLiteral>();
            string_view fmt = lit.getRawValue();
            if (fmt.length() >= 2)
                fmt = fmt.substr(1, fmt.length() - 2);

            bool result = SFormat::parse(
                fmt,
                [&](string_view text) {
                    proc.emitCall(mir::SysCallKind::printStr, proc.emitString(std::string(text)));
                },
                [&](char specifier, size_t, size_t, const SFormat::FormatOptions& options) {
                    if (argIt != args.end()) {
                        auto currentArg = *argIt++;
                        lowerFormatArg(proc, *currentArg, specifier, options, defaultBase);
                    }
                },
                [](DiagCode, size_t, size_t, optional<char>) {});

            if (!result)
                return;
        }
        else {
            // Otherwise, print the value with default options.
            // TODO: set correct specifier
            lowerFormatArg(proc, *arg, ' ', {}, defaultBase);
        }
    }

    proc.emitCall(mir::SysCallKind::flush, proc.emitBool(newline));
}

bool FmtHelpers::checkFinishNum(const BindContext& context, const Expression& arg) {
    ConstantValue cv = context.tryEval(arg);
    if (cv.isInteger()) {
        auto& val = cv.integer();
        if (val == 0 || val == 1 || val == 2)
            return true;
    }

    context.addDiag(diag::BadFinishNum, arg.sourceRange);
    return false;
}

} // namespace slang
