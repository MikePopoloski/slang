//------------------------------------------------------------------------------
// SystemSubroutine.cpp
// System-defined subroutine handling.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"

#include "../text/CharInfo.h"

#include "slang/binding/BindContext.h"
#include "slang/binding/Expressions.h"

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
        context.addDiag(DiagCode::TooFewArguments, callRange) << min << provided;
        return false;
    }

    if (provided > max) {
        context.addDiag(DiagCode::TooManyArguments, args[max]->sourceRange) << max << provided;
        return false;
    }

    for (auto arg : args) {
        if (arg->bad())
            return false;
    }

    return true;
}

struct FormatArg {
    enum { Integral, Raw, Float, Net, Pattern, Character, String } kind;
    char spec;
};

static bool parseFormatString(const BindContext& context, string_view str, SourceLocation loc,
                              SmallVector<FormatArg>& args) {
    const char* ptr = str.data();
    const char* end = str.data() + str.length();

    auto error = [&](DiagCode code, const char* start) -> decltype(auto) {
        SourceLocation sl = loc + (start - str.data());
        return context.addDiag(code, SourceRange{ sl, sl + (ptr - start) });
    };

    while (ptr != end) {
        const char* start = ptr;
        if (*ptr++ != '%')
            continue;

        bool hasNeg = false;
        if (ptr != end && *ptr == '-') {
            hasNeg = true;
            ptr++;
            if (ptr != end && !isDecimalDigit(*ptr)) {
                error(DiagCode::UnknownFormatSpecifier, start) << '-';
                return false;
            }
        }

        bool hasSize = false;
        bool hasDecimal = false;
        uint32_t width = 0;

        if (ptr != end && isDecimalDigit(*ptr)) {
            hasSize = true;
            do {
                width = width * 10 + *ptr;
                if (width > INT32_MAX)
                    break;
                ptr++;
            } while (ptr != end && isDecimalDigit(*ptr));

            if (width > INT32_MAX || (width == 0 && (ptr - start) > 2)) {
                error(DiagCode::FormatSpecifierInvalidWidth, start);
                return false;
            }

            if (ptr != end && *ptr == '.') {
                hasDecimal = true;
                ptr++;
                while (ptr != end && isDecimalDigit(*ptr))
                    ptr++;
            }
        }

        if (ptr == end) {
            error(DiagCode::MissingFormatSpecifier, start);
            return false;
        }

        bool sizeAllowed = false;
        bool floatAllowed = false;
        char c = *ptr++;
        switch (::tolower(c)) {
            case 'l':
            case 'm':
            case '%':
                // Nothing to do for these.
                break;
            case 'h':
            case 'x':
            case 'd':
            case 'o':
            case 'b':
                sizeAllowed = true;
                args.append({ FormatArg::Integral, c });
                break;
            case 'u':
            case 'z':
                args.append({ FormatArg::Raw, c });
                break;
            case 'e':
            case 'f':
            case 'g':
                sizeAllowed = true;
                floatAllowed = true;
                args.append({ FormatArg::Float, c });
                break;
            case 't':
                args.append({ FormatArg::Float, c });
                break;
            case 'c':
                args.append({ FormatArg::Character, c });
                break;
            case 'v':
                args.append({ FormatArg::Net, c });
                break;
            case 'p':
                sizeAllowed = width == 0;
                args.append({ FormatArg::Pattern, c });
                break;
            case 's':
                sizeAllowed = true;
                args.append({ FormatArg::String, c });
                break;
            default:
                error(DiagCode::UnknownFormatSpecifier, start) << c;
                return false;
        }

        if (hasSize) {
            if (!sizeAllowed) {
                error(DiagCode::FormatSpecifierWidthNotAllowed, start) << c;
                return false;
            }

            if (!floatAllowed && (hasNeg || hasDecimal)) {
                error(DiagCode::FormatSpecifierNotFloat, start);
                return false;
            }
        }
    }

    return true;
}

static bool isByteArray(const Type& type) {
    if (!type.isUnpackedArray())
        return false;

    auto& elem = type.getCanonicalType().as<UnpackedArrayType>().elementType.getCanonicalType();
    return elem.isPredefinedInteger() &&
           elem.as<PredefinedIntegerType>().integerKind == PredefinedIntegerType::Byte;
}

static bool isValidForRaw(const Type& type) {
    if (type.isIntegral())
        return true;

    if (!type.isUnpackedStruct())
        return false;

    auto& ust = type.getCanonicalType().as<UnpackedStructType>();
    for (auto& member : ust.members()) {
        if (!isValidForRaw(member.as<FieldSymbol>().getType()))
            return false;
    }

    return true;
}

bool SystemSubroutine::checkFormatArgs(const BindContext& context, const Args& args) {
    // TODO: empty args

    SmallVectorSized<FormatArg, 8> specs;
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
                if (!parseFormatString(context, lit.getRawValue(), arg->sourceRange.start(), specs))
                    return false;

                specIt = specs.begin();
            }
            else if (type.isAggregate() && !isByteArray(type)) {
                context.addDiag(DiagCode::FormatUnspecifiedType, arg->sourceRange) << type;
                return false;
            }
        }
        else {
            FormatArg fmtArg = *specIt++;
            bool ok = false;
            switch (fmtArg.kind) {
                case FormatArg::Integral:
                case FormatArg::Character:
                    ok = type.isIntegral();
                    break;
                case FormatArg::Float:
                    ok = type.isNumeric();
                    break;
                case FormatArg::Net:
                    // TODO: support this
                    ok = false;
                    break;
                case FormatArg::Raw:
                    ok = isValidForRaw(type);
                    break;
                case FormatArg::Pattern:
                    ok = true;
                    break;
                case FormatArg::String:
                    ok = type.isIntegral() || type.isString() || isByteArray(type);
                    break;
            }

            if (!ok) {
                context.addDiag(DiagCode::FormatMismatchedType, arg->sourceRange)
                    << type << fmtArg.spec;
                return false;
            }
        }
    }

    return true;
}

} // namespace slang