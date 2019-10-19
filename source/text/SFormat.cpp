//------------------------------------------------------------------------------
// SFormat.cpp
// SystemVerilog string formatting routines.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/text/SFormat.h"

#include "../text/CharInfo.h"
#include <ieee1800/vpi_user.h>

#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/symbols/AllTypes.h"
#include "slang/symbols/VariableSymbols.h"

namespace slang::SFormat {

static optional<uint32_t> parseUInt(const char*& ptr) {
    // TODO: use std::from_chars and disallow prefix
    char* end;
    errno = 0;
    unsigned long val = strtoul(ptr, &end, 10);

    if (ptr == end || errno == ERANGE || val > UINT32_MAX)
        return std::nullopt;

    ptr = end;
    return uint32_t(val);
}

struct FormatOptions {
    optional<uint32_t> width;
    optional<uint32_t> precision;
    bool leftJustify = false;
    bool zeroPad = false;
};

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

        // %% collapses to a single %
        if (ptr != end && *ptr == '%') {
            ptr++;
            onChar('%');
            continue;
        }

        FormatOptions options;
        while (ptr != end) {
            if (*ptr == '-' && !options.leftJustify) {
                options.leftJustify = true;
                ptr++;
            }
            else if (*ptr == '0' && !options.zeroPad) {
                options.zeroPad = true;
                ptr++;
            }
            else {
                break;
            }
        }

        if (ptr != end && isDecimalDigit(*ptr)) {
            options.width = parseUInt(ptr);
            if (!options.width) {
                onError(diag::FormatSpecifierInvalidWidth, start);
                return false;
            }
        }

        if (ptr != end && *ptr == '.') {
            ptr++;
            if (ptr != end && isDecimalDigit(*ptr)) {
                options.precision = parseUInt(ptr);
                if (!options.precision) {
                    onError(diag::FormatSpecifierInvalidWidth, start);
                    return false;
                }
            }
            else {
                // Precision defaults to zero if we just have a decimal point.
                options.precision = 0;
            }
        }

        if (ptr == end) {
            onError(diag::MissingFormatSpecifier, start);
            return false;
        }

        Arg::Type type;
        bool widthAllowed = false;
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
                widthAllowed = true;
                type = Arg::Integral;
                if (options.zeroPad) {
                    options.zeroPad = false;
                    if (!options.width)
                        options.width = 0;
                }
                break;
            case 'u':
            case 'z':
                type = Arg::Raw;
                break;
            case 'e':
            case 'f':
            case 'g':
                widthAllowed = true;
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
                type = Arg::Pattern;
                break;
            case 's':
                widthAllowed = true;
                type = Arg::String;
                break;
            default:
                onError(diag::UnknownFormatSpecifier, start) << c;
                return false;
        }

        if (options.width && !widthAllowed) {
            onError(diag::FormatSpecifierWidthNotAllowed, start) << c;
            return false;
        }

        if ((options.precision || options.leftJustify) && !floatAllowed) {
            onError(diag::FormatSpecifierNotFloat, start);
            return false;
        }

        if (options.zeroPad && !widthAllowed && type != Arg::Pattern) {
            onError(diag::FormatSpecifierWidthNotAllowed, start) << c;
            return false;
        }

        onArg(type, c, options);
    }

    return true;
}

static bool isValidForRaw(const Type& type) {
    if (type.isIntegral())
        return true;

    if (type.isUnpackedUnion()) {
        auto members = type.as<UnpackedUnionType>().members();
        if (members.begin() == members.end())
            return false;

        return isValidForRaw(members.begin()->as<FieldSymbol>().getType());
    }

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
                      const FormatOptions& options) {
    std::string str;
    if (base != LiteralBase::Decimal && value.isSigned()) {
        // Non-decimal bases don't print as signed ever.
        SVInt copy = value;
        copy.setSigned(false);
        str = copy.toString(base, /* includeBase */ false);
    }
    else {
        str = value.toString(base, /* includeBase */ false);
    }

    // If no width is specified we need to calculate it ourselves based on the bitwidth
    // of the provided integer.
    uint32_t width = 0;
    if (options.width)
        width = *options.width;
    else {
        static const double log2_10 = log2(10.0);
        bitwidth_t bw = value.getBitWidth();
        switch (base) {
            case LiteralBase::Binary:
                width = bw;
                break;
            case LiteralBase::Octal:
                width = uint32_t(ceil(bw / 3.0));
                break;
            case LiteralBase::Hex:
                width = uint32_t(ceil(bw / 4.0));
                break;
            case LiteralBase::Decimal:
                width = uint32_t(ceil(bw / log2_10));
                if (value.isSigned())
                    width++;
                break;
        }
    }

    if (str.size() < width) {
        char pad = '0';
        if (base == LiteralBase::Decimal)
            pad = ' ';

        result.append(width - str.size(), pad);
    }

    result.append(str);
}

static void formatFloat(std::string& result, double value, char specifier,
                        const FormatOptions& options) {
    // TODO: use std::to_chars
    std::string fmt = "%";
    if (options.leftJustify)
        fmt.push_back('-');
    if (options.zeroPad)
        fmt.push_back('0');
    if (options.width)
        fmt.append(std::to_string(*options.width));
    if (options.precision) {
        fmt.push_back('.');
        fmt.append(std::to_string(*options.precision));
    }
    fmt.push_back(specifier);

    size_t cur = result.size();
    size_t sz = (size_t)snprintf(nullptr, 0, fmt.c_str(), value);
    result.resize(cur + sz + 1);
    snprintf(result.data() + cur, sz + 1, fmt.c_str(), value);
    result.pop_back();
}

static void formatChar(std::string& result, const SVInt& value) {
    char c = char(value.getRawPtr()[0] & 0xff);
    result.push_back(c);
}

static void formatString(std::string& result, const std::string& value,
                         const FormatOptions& options) {
    if (options.width) {
        uint32_t width = *options.width;
        if (value.size() < width)
            result.append(width - value.size(), ' ');
    }

    result.append(value);
}

static void formatRaw2(std::string& result, const ConstantValue& value) {
    if (value.isUnpacked()) {
        for (auto& elem : value.elements())
            formatRaw2(result, elem);
        return;
    }

    SVInt sv = value.integer();
    sv.flattenUnknowns();

    uint32_t words = sv.getNumWords();
    uint32_t lastBits = sv.getBitWidth() % 64;
    if (lastBits == 0)
        lastBits = 64;

    const uint64_t* ptr = sv.getRawPtr();
    for (uint32_t i = 0; i < words; i++) {
        // Don't write the upper half of the last word if we don't actually have those bits.
        size_t bytes = (i == words - 1 && lastBits <= 32) ? sizeof(uint32_t) : sizeof(uint64_t);
        result.append(reinterpret_cast<const char*>(ptr + i), bytes);
    }
}

static void formatRaw4(std::string& result, const ConstantValue& value) {
    if (value.isUnpacked()) {
        for (auto& elem : value.elements())
            formatRaw4(result, elem);
        return;
    }

    const SVInt& sv = value.integer();
    uint32_t words = sv.getNumWords();
    const uint64_t* ptr = sv.getRawPtr();
    const uint64_t* unknownPtr = nullptr;
    if (sv.hasUnknown()) {
        words /= 2;
        unknownPtr = ptr + words;
    }

    uint32_t lastBits = sv.getBitWidth() % 64;
    if (lastBits == 0)
        lastBits = 64;

    auto writeEntry = [&result](uint32_t bits, uint32_t unknowns) {
        // The encoding for X and Z are reversed from how SVInt stores them.
        s_vpi_vecval entry;
        entry.aval = bits ^ unknowns;
        entry.bval = unknowns;
        result.append(reinterpret_cast<const char*>(&entry), sizeof(s_vpi_vecval));
    };

    for (uint32_t i = 0; i < words; i++) {
        uint64_t bits = ptr[i];
        uint64_t unknowns = unknownPtr ? unknownPtr[i] : 0;

        writeEntry(uint32_t(bits), uint32_t(unknowns));

        // Don't write the upper half of the last word if we don't actually have those bits.
        if (i != words - 1 || lastBits > 32)
            writeEntry(uint32_t(bits >> 32), uint32_t(unknowns >> 32));
    }
}

static void formatArg(std::string& result, const ConstantValue& arg, const Type&, char specifier,
                      const FormatOptions& options, Diagnostics&) {
    switch (::tolower(specifier)) {
        case 'h':
        case 'x':
            formatInt(result, arg.integer(), LiteralBase::Hex, options);
            return;
        case 'd':
            formatInt(result, arg.integer(), LiteralBase::Decimal, options);
            return;
        case 'o':
            formatInt(result, arg.integer(), LiteralBase::Octal, options);
            return;
        case 'b':
            formatInt(result, arg.integer(), LiteralBase::Binary, options);
            return;
        case 'u':
            formatRaw2(result, arg);
            return;
        case 'z':
            formatRaw4(result, arg);
            return;
        case 'e':
        case 'f':
        case 'g':
            formatFloat(result, arg.convertToReal().real(), specifier, options);
            return;
        case 't':
            // TODO:
            return;
        case 'c':
            formatChar(result, arg.integer());
            return;
        case 'v':
            // TODO:
            return;
        case 'p':
            return;
        case 's':
            formatString(result, arg.convertToStr().str(), options);
            return;
        default:
            THROW_UNREACHABLE;
    }
}

static void formatNonArg(std::string& result, char specifier, const Scope& scope) {
    specifier = char(::tolower(specifier));
    if (specifier == 'l') {
        // TODO: support libraries
        return;
    }

    if (specifier == 'm') {
        scope.asSymbol().getHierarchicalPath(result);
        return;
    }

    THROW_UNREACHABLE;
}

bool parseArgs(string_view formatString, SourceLocation loc, SmallVector<Arg>& args,
               Diagnostics& diags) {
    auto onArg = [&](Arg::Type type, char c, const FormatOptions&) {
        if (type == Arg::None)
            return;
        args.append({ type, c });
    };
    return parseFormatString(
        formatString, loc, [](char) {}, onArg, diags);
}

optional<std::string> format(string_view formatString, SourceLocation loc,
                             span<const TypedValue> args, const Scope& scope, Diagnostics& diags) {
    std::string result;
    auto argIt = args.begin();

    auto onChar = [&](char c) { result += c; };

    auto onArg = [&](Arg::Type requiredType, char c, const FormatOptions& options) {
        if (requiredType == Arg::None) {
            formatNonArg(result, c, scope);
            return;
        }

        if (argIt == args.end()) {
            // TODO: error for not enough args
            return;
        }

        auto& [value, type, range] = *argIt;
        if (!isArgTypeValid(requiredType, *type))
            diags.add(diag::FormatMismatchedType, range) << *type << c;
        else
            formatArg(result, value, *type, c, options, diags);
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
        case Arg::None:
            return false;
    }
    return false;
}

} // namespace slang::SFormat
