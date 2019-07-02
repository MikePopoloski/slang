//------------------------------------------------------------------------------
// SFormat.cpp
// SystemVerilog string formatting routines.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/text/SFormat.h"

#include "../text/CharInfo.h"

#include "slang/diagnostics/SysFuncsDiags.h"

namespace slang {

SFormat::SFormat(string_view str, SourceLocation loc) {
    const char* ptr = str.data();
    const char* end = str.data() + str.length();

    auto error = [&](DiagCode code, const char* start) -> decltype(auto) {
        SourceLocation sl = loc + (start - str.data());
        return diags.add(code, SourceRange{ sl, sl + (ptr - start) });
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
                error(diag::UnknownFormatSpecifier, start) << '-';
                return;
            }
        }

        bool hasSize = false;
        bool hasDecimal = false;
        uint32_t width = 0;

        if (ptr != end && isDecimalDigit(*ptr)) {
            hasSize = true;
            do {
                width = width * 10 + uint8_t(*ptr);
                if (width > INT32_MAX)
                    break;
                ptr++;
            } while (ptr != end && isDecimalDigit(*ptr));

            if (width > INT32_MAX || (width == 0 && (ptr - start) > 2)) {
                error(diag::FormatSpecifierInvalidWidth, start);
                return;
            }

            if (ptr != end && *ptr == '.') {
                hasDecimal = true;
                ptr++;
                while (ptr != end && isDecimalDigit(*ptr))
                    ptr++;
            }
        }

        if (ptr == end) {
            error(diag::MissingFormatSpecifier, start);
            return;
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
                specs.append({ Arg::Integral, c });
                break;
            case 'u':
            case 'z':
                specs.append({ Arg::Raw, c });
                break;
            case 'e':
            case 'f':
            case 'g':
                sizeAllowed = true;
                floatAllowed = true;
                specs.append({ Arg::Float, c });
                break;
            case 't':
                specs.append({ Arg::Float, c });
                break;
            case 'c':
                specs.append({ Arg::Character, c });
                break;
            case 'v':
                specs.append({ Arg::Net, c });
                break;
            case 'p':
                sizeAllowed = width == 0;
                specs.append({ Arg::Pattern, c });
                break;
            case 's':
                sizeAllowed = true;
                specs.append({ Arg::String, c });
                break;
            default:
                error(diag::UnknownFormatSpecifier, start) << c;
                return;
        }

        if (hasSize) {
            if (!sizeAllowed) {
                error(diag::FormatSpecifierWidthNotAllowed, start) << c;
                return;
            }

            if (!floatAllowed && (hasNeg || hasDecimal)) {
                error(diag::FormatSpecifierNotFloat, start);
                return;
            }
        }
    }
}

optional<std::string> SFormat::format(span<const ConstantValue>, Diagnostics&) const {
    return std::nullopt;
}

} // namespace slang
