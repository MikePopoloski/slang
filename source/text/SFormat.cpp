//------------------------------------------------------------------------------
// SFormat.cpp
// SystemVerilog string formatting routines.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/text/SFormat.h"

#include "../text/CharInfo.h"

#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/symbols/TypeSymbols.h"

namespace slang {

namespace SFormat {

template<typename OnChar, typename OnArg>
static bool parseFormatString(string_view str, SourceLocation loc, OnChar&& onChar, OnArg&& onArg,
                              Diagnostics& diags) {
    const char* ptr = str.data();
    const char* end = str.data() + str.length();

    auto onError = [&](DiagCode code, const char* curr) -> decltype(auto) {
        SourceLocation sl = loc + (curr - str.data());
        return diags.add(code, SourceRange{ sl, sl + (ptr - curr) });
    };

    while (ptr != end) {
        const char* start = ptr;
        if (char c = *ptr++; c != '%') {
            onChar(c);
            continue;
        }

        // %% collapsed to a single %
        if (ptr != end && *ptr == '%') {
            ptr++;
            onChar('%');
            continue;
        }

        bool hasNeg = false;
        if (ptr != end && *ptr == '-') {
            hasNeg = true;
            ptr++;
            if (ptr != end && !isDecimalDigit(*ptr)) {
                onError(diag::UnknownFormatSpecifier, start) << '-';
                return false;
            }
        }

        bool hasSize = false;
        bool hasDecimal = false;
        uint32_t width = 0;

        if (ptr != end && isDecimalDigit(*ptr)) {
            hasSize = true;
            do {
                width = width * 10 + uint8_t(*ptr - '0');
                if (width > INT32_MAX)
                    break;
                ptr++;
            } while (ptr != end && isDecimalDigit(*ptr));

            if (width > INT32_MAX || (width == 0 && (ptr - start) > 2)) {
                onError(diag::FormatSpecifierInvalidWidth, start);
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
            onError(diag::MissingFormatSpecifier, start);
            return false;
        }

        Arg::Type type;
        bool sizeAllowed = false;
        bool floatAllowed = false;
        char c = *ptr++;
        switch (::tolower(c)) {
            case 'l':
            case 'm':
                type = Arg::None;
                break;
            case 'h':
            case 'x':
            case 'd':
            case 'o':
            case 'b':
                sizeAllowed = true;
                type = Arg::Integral;
                break;
            case 'u':
            case 'z':
                type = Arg::Raw;
                break;
            case 'e':
            case 'f':
            case 'g':
                sizeAllowed = true;
                floatAllowed = true;
                type = Arg::Float;
                break;
            case 't':
                type = Arg::Float;
                break;
            case 'c':
                type = Arg::Character;
                break;
            case 'v':
                type = Arg::Net;
                break;
            case 'p':
                sizeAllowed = width == 0;
                type = Arg::Pattern;
                break;
            case 's':
                sizeAllowed = true;
                type = Arg::String;
                break;
            default:
                onError(diag::UnknownFormatSpecifier, start) << c;
                return false;
        }

        optional<int> argWidth;
        if (hasSize) {
            if (!sizeAllowed) {
                onError(diag::FormatSpecifierWidthNotAllowed, start) << c;
                return false;
            }

            if (!floatAllowed && (hasNeg || hasDecimal)) {
                onError(diag::FormatSpecifierNotFloat, start);
                return false;
            }

            int w = int(width);
            if (hasNeg)
                w = -w;
            argWidth = w;
        }

        onArg(type, c, argWidth);
    }

    return true;
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

static void formatInt(std::string& result, const SVInt& value, LiteralBase base,
                      optional<int> width) {
    auto str = value.toString(base, /* includeBase */ false);

    // If no width is specified we need to calculate it ourselves based on the bitwidth
    // of the provided integer.
    if (!width.has_value()) {
        constexpr double log2_10 = 3.32192809489; // TODO: log2(10)
        bitwidth_t bw = value.getBitWidth();
        switch (base) {
            case LiteralBase::Binary:
                width = int(bw);
                break;
            case LiteralBase::Octal:
                width = int(ceil(bw / 3.0));
                break;
            case LiteralBase::Hex:
                width = int(ceil(bw / 4.0));
                break;
            case LiteralBase::Decimal:
                width = int(ceil(bw / log2_10));
                break;
        }

        if (value.isSigned())
            width = *width + 1;
    }

    size_t w = *width;
    if (str.size() < w) {
        char pad = '0';
        if (base == LiteralBase::Decimal)
            pad = ' ';

        result.append(w - str.size(), pad);
    }

    result.append(str);
}

static void formatArg(std::string& result, const ConstantValue& arg, const Type&, char specifier,
                      optional<int> width, Diagnostics&) {
    switch (::tolower(specifier)) {
        case 'l':
            // TODO:
            return;
        case 'm':
            // TODO:
            return;
        case 'h':
        case 'x':
            formatInt(result, arg.integer(), LiteralBase::Hex, width);
            return;
        case 'd':
            formatInt(result, arg.integer(), LiteralBase::Decimal, width);
            return;
        case 'o':
            formatInt(result, arg.integer(), LiteralBase::Octal, width);
            return;
        case 'b':
            formatInt(result, arg.integer(), LiteralBase::Binary, width);
            return;
        case 'u':
        case 'z':
            return;
        case 'e':
        case 'f':
        case 'g':
            return;
        case 't':
            return;
        case 'c':
            return;
        case 'v':
            // TODO:
            return;
        case 'p':
            return;
        case 's':
            return;
        default:
            THROW_UNREACHABLE;
    }
}

bool parseArgs(string_view formatString, SourceLocation loc, SmallVector<Arg>& args,
               Diagnostics& diags) {
    auto onArg = [&](Arg::Type type, char c, optional<int>) { args.append({ type, c }); };
    return parseFormatString(formatString, loc, [](char) {}, onArg, diags);
}

optional<std::string> format(string_view formatString, SourceLocation loc,
                             span<const TypedValue> args, Diagnostics& diags) {
    std::string result;
    auto argIt = args.begin();

    auto onChar = [&](char c) { result += c; };

    auto onArg = [&](Arg::Type requiredType, char c, optional<int> width) {
        if (argIt == args.end()) {
            // TODO: error for not enough args
            return;
        }

        auto& [value, type, range] = *argIt;
        if (!isArgTypeValid(requiredType, *type))
            diags.add(diag::FormatMismatchedType, range) << *type << c;
        else
            formatArg(result, value, *type, c, width, diags);
    };

    if (!parseFormatString(formatString, loc, onChar, onArg, diags))
        return std::nullopt;

    // TODO: check for too many args

    return result;
}

bool isArgTypeValid(Arg::Type required, const Type& type) {
    switch (required) {
        case Arg::Integral:
        case Arg::Character:
            return type.isIntegral();
        case Arg::Float:
            return type.isNumeric();
        case Arg::Net:
            // TODO: support this
            return false;
        case Arg::Raw:
            return isValidForRaw(type);
        case Arg::Pattern:
            return true;
        case Arg::String:
            return type.isIntegral() || type.isString() || type.isByteArray();
    }
    return false;
}

} // namespace SFormat

} // namespace slang
