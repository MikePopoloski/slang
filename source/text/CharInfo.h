//------------------------------------------------------------------------------
// CharInfo.h
// Various character-related utilities.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

namespace slang {

/// Returns whether the given character is a valid ASCII character.
inline bool isASCII(char c) {
    return static_cast<unsigned char>(c) < 128;
}

/// Returns whether the given character is considered "printable".
inline bool isPrintable(char c) {
    return c >= 33 && c <= 126;
}

/// Returns whether the given character is considered whitespace.
inline bool isWhitespace(char c) {
    switch (c) {
        case ' ':
        case '\t':
        case '\v':
        case '\f':
        case '\r':
        case '\n':
            return true;
    }
    return false;
}

/// Returns whether the given character is considered horizontal whitespace
/// (as opposed to vertical like line feeds or vertical tabs).
inline bool isHorizontalWhitespace(char c) {
    switch (c) {
        case ' ':
        case '\t':
        case '\v':
        case '\f':
            return true;
    }
    return false;
}

/// Returns whether the given character is considered a new line.
inline bool isNewline(char c) {
    return c == '\r' || c == '\n';
}

/// Returns whether the given character is considered a decimal digit.
inline bool isDecimalDigit(char c) {
    return c >= '0' && c <= '9';
}

/// Returns whether the given character is considered an octal digit.
inline bool isOctalDigit(char c) {
    return c >= '0' && c <= '7';
}

/// Returns whether the given character is considered a hexadecimal digit.
inline bool isHexDigit(char c) {
    return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
}

/// Returns whether the given character is considered a binary digit.
inline bool isBinaryDigit(char c) {
    return c == '0' || c == '1';
}

/// Returns whether the given character is considered an alphanumeric character.
inline bool isAlphaNumeric(char c) {
    return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
}

/// Returns whether the given character is considered a special logic digit,
/// which encompasses various ways to say Unknown (X) or High Impedance (Z).
inline bool isLogicDigit(char c) {
    switch (c) {
        case 'z':
        case 'Z':
        case '?':
        case 'x':
        case 'X':
            return true;
        default:
            return false;
    }
}

/// Gets the numeric value of the given decimal digit. If the given character
/// is not a valid decimal digit, the result is undefined.
inline uint8_t getDigitValue(char c) {
    return uint8_t(c - '0');
}

/// Gets the numeric value of the given hexadecimal digit. If the given character
/// is not a valid hexadecimal digit, the result is undefined.
inline uint8_t getHexDigitValue(char c) {
    if (c <= '9')
        return uint8_t(c - '0');
    if (c <= 'F')
        return uint8_t(10 + c - 'A');
    return uint8_t(10 + c - 'a');
}

/// Gets the logic_t value of the given logic digit,
/// which encompasses various ways to say Unknown (X) or High Impedance (Z).
inline logic_t getLogicCharValue(char c) {
    switch (c) {
        case 'z':
        case 'Z':
        case '?':
            return logic_t::z;
        case 'x':
        case 'X':
            return logic_t::x;
        default:
            return logic_t(0);
    }
}

/// Returns the number of bytes to skip after reading a UTF-8 character.
inline int utf8SeqBytes(char c) {
    unsigned char uc = static_cast<unsigned char>(c);
    if ((uc & (3 << 6)) == 0)
        return 0;
    if ((uc & (1 << 5)) == 0)
        return 1;
    if ((uc & (1 << 4)) == 0)
        return 2;
    if ((uc & (1 << 3)) == 0)
        return 3;

    // 5 and 6 byte sequences are disallowed by the UTF-8 spec
    return 0;
}

}