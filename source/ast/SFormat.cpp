//------------------------------------------------------------------------------
// SFormat.cpp
// SystemVerilog string formatting routines
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/SFormat.h"

#include <cmath>
#include <ieee1800/vpi_user.h>

#include "slang/ast/ASTVisitor.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/text/CharInfo.h"
#include "slang/text/FormatBuffer.h"
#include "slang/util/String.h"

static const double log2_10 = std::log2(10.0);

namespace slang::ast::SFormat {

static std::optional<uint32_t> parseUInt(const char*& ptr, const char* end) {
    size_t pos;
    auto result = strToUInt(std::string_view(ptr, size_t(end - ptr)), &pos);
    if (result)
        ptr += pos;

    return result;
}

bool parse(std::string_view str, function_ref<void(std::string_view)> onText,
           function_ref<void(char, size_t, size_t, const FormatOptions&)> onArg,
           function_ref<void(DiagCode, size_t, size_t, std::optional<char>)> onError) {
    SmallVector<char> text;
    const char* ptr = str.data();
    const char* end = str.data() + str.length();

    auto err = [&](DiagCode code, const char* curr, std::optional<char> spec = {}) {
        onError(code, size_t(curr - str.data()), size_t(ptr - curr), spec);
    };

    while (ptr != end) {
        const char* start = ptr;
        if (char c = *ptr++; c != '%') {
            text.push_back(c);
            continue;
        }

        // %% collapses to a single %
        if (ptr != end && *ptr == '%') {
            ptr++;
            text.push_back('%');
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
            options.width = parseUInt(ptr, end);
            if (!options.width) {
                err(diag::FormatSpecifierInvalidWidth, ptr);
                return false;
            }
        }

        if (ptr != end && *ptr == '.') {
            ptr++;
            if (ptr != end && isDecimalDigit(*ptr)) {
                options.precision = parseUInt(ptr, end);
                if (!options.precision) {
                    err(diag::FormatSpecifierInvalidWidth, ptr);
                    return false;
                }
            }
            else {
                // Precision defaults to zero if we just have a decimal point.
                options.precision = 0;
            }
        }

        if (ptr == end) {
            err(diag::MissingFormatSpecifier, start);
            text.push_back('%');
            break;
        }

        bool widthAllowed = false;
        bool floatAllowed = false;
        char c = *ptr++;
        char spec = charToLower(c);
        switch (spec) {
            case 'h':
            case 'x':
            case 'd':
            case 'o':
            case 'b':
                widthAllowed = true;
                if (options.zeroPad) {
                    options.zeroPad = false;
                    if (!options.width)
                        options.width = 0;
                }
                break;
            case 'e':
            case 'f':
            case 'g':
                widthAllowed = true;
                floatAllowed = true;
                break;
            case 's':
            case 't':
                widthAllowed = true;
                break;
            case 'c':
            case 'u':
            case 'z':
            case 'v':
            case 'p':
            case 'l':
            case 'm':
                break;
            default:
                err(diag::UnknownFormatSpecifier, start, c);
                return false;
        }

        if ((options.width || options.leftJustify) && !widthAllowed) {
            err(diag::FormatSpecifierWidthNotAllowed, start, c);
            return false;
        }

        if (options.precision && !floatAllowed) {
            err(diag::FormatSpecifierNotFloat, start);
            return false;
        }

        // Pattern args allow the zero-pad specifier.
        if (options.zeroPad && !widthAllowed && spec != 'p') {
            err(diag::FormatSpecifierWidthNotAllowed, start, c);
            return false;
        }

        if (!text.empty()) {
            onText(toStringView(text));
            text.clear();
        }

        onArg(c, size_t(start - str.data()), size_t(ptr - start), options);
    }

    if (!text.empty())
        onText(toStringView(text));

    return true;
}

void formatInt(std::string& result, const SVInt& value, LiteralBase base,
               const FormatOptions& options) {
    SmallVector<char> buffer;
    if (base != LiteralBase::Decimal && value.isSigned()) {
        // Non-decimal bases don't print as signed ever.
        SVInt copy = value;
        copy.setSigned(false);
        copy.writeTo(buffer, base, /* includeBase */ false);
    }
    else {
        value.writeTo(buffer, base, /* includeBase */ false);
    }

    // If no width is specified we need to calculate it ourselves based on the bitwidth
    // of the provided integer.
    uint32_t width = 0;
    if (options.width)
        width = *options.width;
    else {
        bitwidth_t bw = value.getBitWidth();
        switch (base) {
            case LiteralBase::Binary:
                width = bw;
                break;
            case LiteralBase::Octal:
                width = uint32_t(std::ceil(bw / 3.0));
                break;
            case LiteralBase::Hex:
                width = uint32_t(std::ceil(bw / 4.0));
                break;
            case LiteralBase::Decimal:
                width = uint32_t(std::ceil(bw / log2_10));
                if (value.isSigned())
                    width++;
                break;
        }
    }

    auto doPad = [&] {
        char pad = '0';
        if (base == LiteralBase::Decimal)
            pad = ' ';

        result.append(width - buffer.size(), pad);
    };

    if (buffer.size() < width && !options.leftJustify)
        doPad();

    result.append(buffer.begin(), buffer.end());

    if (buffer.size() < width && options.leftJustify)
        doPad();
}

static void formatFloat(std::string& result, double value, char specifier,
                        const FormatOptions& options) {
    SmallVector<char, 8> fmt;
    fmt.push_back('%');
    if (options.leftJustify)
        fmt.push_back('-');
    if (options.zeroPad)
        fmt.push_back('0');
    if (options.width)
        uintToStr(fmt, *options.width);
    if (options.precision) {
        fmt.push_back('.');
        uintToStr(fmt, *options.precision);
    }
    fmt.push_back(specifier);
    fmt.push_back('\0');

    size_t cur = result.size();
    size_t sz = (size_t)snprintf(nullptr, 0, fmt.data(), value);
    result.resize(cur + sz + 1);
    snprintf(result.data() + cur, sz + 1, fmt.data(), value);
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

void formatStrength(std::string& result, const SVInt& value) {
    for (bitwidth_t i = value.getBitWidth(); i > 0; i--) {
        // At compile time it's impossible to know strength values so
        // we will always put "Strong" here, or "Hi" if it's high impedance.
        logic_t l = value[int32_t(i) - 1];
        switch (l.value) {
            case 0:
                result += "St0";
                break;
            case 1:
                result += "St1";
                break;
            case logic_t::X_VALUE:
                result += "StX";
                break;
            case logic_t::Z_VALUE:
                result += "HiZ";
                break;
            default:
                SLANG_UNREACHABLE;
        }

        if (i != 1)
            result += " ";
    }
}

struct TypeVisitor {
    bool abbreviated;
    bool isStringLiteral;

    TypeVisitor(bool abbreviated, bool isStringLiteral) :
        abbreviated(abbreviated), isStringLiteral(isStringLiteral) {}

    void visit(const EnumType& type, const ConstantValue& arg) {
        for (auto& member : type.values()) {
            if (member.getValue() == arg) {
                buffer.append(member.name);
                return;
            }
        }
        buffer.append(arg.toString());
    }

    void visit(const PackedStructType& type, const ConstantValue& arg) {
        if (arg) {
            auto& value = arg.integer();
            auto currOffset = int32_t(value.getBitWidth());

            buffer.append("'{");
            for (auto& field : type.membersOfType<FieldSymbol>()) {
                auto& fieldType = field.getType();
                auto fieldWidth = int32_t(fieldType.getBitWidth());
                auto elem = value.slice(currOffset - 1, currOffset - fieldWidth);
                currOffset -= fieldWidth;

                if (!abbreviated) {
                    buffer.append(field.name);
                    buffer.append(":");
                }

                fieldType.visit(*this, elem);

                buffer.append(",");
                if (!abbreviated)
                    buffer.append(" ");
            }

            buffer.pop_back();
            if (!abbreviated)
                buffer.pop_back();
            buffer.append("}");
        }
    }

    void visit(const UnpackedStructType& type, const ConstantValue& arg) {
        if (arg) {
            auto elements = arg.elements();
            auto elemIt = elements.begin();

            buffer.append("'{");
            for (auto field : type.fields) {
                SLANG_ASSERT(elemIt != elements.end());

                if (!abbreviated) {
                    buffer.append(field->name);
                    buffer.append(":");
                }

                field->getType().visit(*this, *elemIt++);

                buffer.append(",");
                if (!abbreviated)
                    buffer.append(" ");
            }

            buffer.pop_back();
            if (!abbreviated)
                buffer.pop_back();
            buffer.append("}");
        }
    }

    void visit(const PackedUnionType& type, const ConstantValue& arg) {
        // LRM says the value is printed with the type of the first member.
        auto fields = type.membersOfType<FieldSymbol>();
        if (!fields.empty())
            fields.front().getType().visit(*this, arg);
    }

    void visit(const UnpackedUnionType& type, const ConstantValue& arg) {
        if (arg.isUnion()) {
            auto& u = *arg.unionVal();
            if (!u.activeMember) {
                buffer.append("(unset)");
            }
            else {
                auto& field = *type.fields[*u.activeMember];
                buffer.format("{}", field.name);
                if (!field.getType().isVoid()) {
                    buffer.append(":");
                    field.getType().visit(*this, u.value);
                }
            }
        }
    }

    void visit(const FixedSizeUnpackedArrayType& type, const ConstantValue& arg) {
        if (arg)
            formatArray(type, arg.elements());
    }

    void visit(const DynamicArrayType& type, const ConstantValue& arg) {
        if (arg)
            formatArray(type, arg.elements());
    }

    void visit(const QueueType& type, const ConstantValue& arg) {
        if (arg)
            formatArray(type, *arg.queue());
    }

    void visit(const AssociativeArrayType& type, const ConstantValue& arg) {
        if (arg) {
            buffer.append("'{");
            for (auto& [key, val] : *arg.map()) {
                if (type.indexType)
                    type.indexType->visit(*this, key);
                else
                    buffer.append(key.toString());

                buffer.append(":");
                type.elementType.visit(*this, val);

                buffer.append(",");
                if (!abbreviated)
                    buffer.append(" ");
            }

            buffer.pop_back();
            if (!abbreviated)
                buffer.pop_back();
            buffer.append("}");
        }
    }

    void visit(const TypeAliasType& type, const ConstantValue& arg) {
        type.targetType.getType().visit(*this, arg);
    }

    template<typename T>
    void visit(const T&, const ConstantValue& arg) {
        if (isStringLiteral)
            buffer.append(arg.convertToStr().toString());
        else
            buffer.append(arg.toString());
    }

    template<typename T>
    void formatArray(const Type& type, const T& arr) {
        auto elemType = type.getArrayElementType();
        SLANG_ASSERT(elemType);

        buffer.append("'{");
        for (size_t i = 0; i < arr.size(); i++) {
            if (i != 0) {
                buffer.append(",");
                if (!abbreviated)
                    buffer.append(" ");
            }
            elemType->visit(*this, arr[i]);
        }
        buffer.append("}");
    }

    FormatBuffer buffer;
};

void formatPattern(std::string& result, const ConstantValue& arg, const Type& type,
                   const FormatOptions& options, bool isStringLiteral) {
    TypeVisitor visitor(options.zeroPad, isStringLiteral);
    type.visit(visitor, arg);
    result += visitor.buffer.str();
}

void formatArg(std::string& result, const ConstantValue& arg, const Type& type, char specifier,
               const FormatOptions& options, bool isStringLiteral) {
    switch (charToLower(specifier)) {
        case 'h':
        case 'x':
            formatInt(result, arg.convertToInt().integer(), LiteralBase::Hex, options);
            return;
        case 'd':
            formatInt(result, arg.convertToInt().integer(), LiteralBase::Decimal, options);
            return;
        case 'o':
            formatInt(result, arg.convertToInt().integer(), LiteralBase::Octal, options);
            return;
        case 'b':
            formatInt(result, arg.convertToInt().integer(), LiteralBase::Binary, options);
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
        case 't': {
            auto timeOptions = options;
            if (!timeOptions.width)
                timeOptions.width = 20;
            formatInt(result, arg.convertToInt().integer(), LiteralBase::Decimal, timeOptions);
            return;
        }
        case 'c':
            formatChar(result, arg.convertToInt().integer());
            return;
        case 'v':
            formatStrength(result, arg.integer());
            return;
        case 'p':
            formatPattern(result, arg, type, options, isStringLiteral);
            return;
        case 's':
            formatString(result, arg.convertToStr().str(), options);
            return;
        default:
            SLANG_UNREACHABLE;
    }
}

} // namespace slang::ast::SFormat
