//------------------------------------------------------------------------------
//! @file String.h
//! @brief Various string utilities
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <filesystem>
#include <optional>

#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang {

/// Converts a span of characters into a std::string_view.
inline std::string_view toStringView(std::span<char> text) {
    return std::string_view(text.data(), text.size());
}

/// Converts the provided @a value into a string, storing it into @a buffer.
void uintToStr(SmallVectorBase<char>& buffer, uint32_t value);

/// Converts the provided @a value into a string, storing it into @a buffer.
void uintToStr(SmallVectorBase<char>& buffer, uint64_t value);

/// Parses the provided @a str in the specified @a base into a signed integer.
/// If @a pos is non-null, it will be set to point to the first character in the
/// source string that was not part of the conversion.
///
/// @return the converted value, or nullopt if conversion fails (invalid string, overflow, etc).
std::optional<int32_t> strToInt(std::string_view str, size_t* pos = nullptr, int base = 10);

/// Parses the provided @a str in the specified @a base into an unsigned integer.
/// If @a pos is non-null, it will be set to point to the first character in the
/// source string that was not part of the conversion.
///
/// @return the converted value, or nullopt if conversion fails (invalid string, overflow, etc).
std::optional<uint32_t> strToUInt(std::string_view str, size_t* pos = nullptr, int base = 10);

/// Parses the provided @a str into a floating point value.
/// If @a pos is non-null, it will be set to point to the first character in the
/// source string that was not part of the conversion.
///
/// @return the converted value, or nullopt if conversion fails (invalid string, overflow, etc).
std::optional<double> strToDouble(std::string_view str, size_t* pos = nullptr);

/// Converts the provided string to all uppercase characters (assuming ASCII contents).
/// The string is converted in place.
void strToUpper(std::string& str);

/// Converts the provided string to all lowercase characters (assuming ASCII contents).
/// The string is converted in place.
void strToLower(std::string& str);

/// Converts a character to uppercase (assuming ASCII).
inline char charToUpper(char c) {
    return (char)::toupper(c);
}

/// Converts a character to lowercase (assuming ASCII).
inline char charToLower(char c) {
    return (char)::tolower(c);
}

/// Determines the number of edits to the left string that are required to
/// change it into the right string.
/// If @a allowReplacements is true, characters can be substituted as needed.
/// Otherwise, only swaps are allowed.
///
/// If @a maxDistance is >0 and the computed distance is at least that much, give
/// up and return maxDistance + 1.
int editDistance(std::string_view left, std::string_view right, bool allowReplacements = true,
                 int maxDistance = 0);

/// C++20 is dumb and provides no way to get a std::string with the UTF-8
/// contents of a fs::path, so we have to use this method to copy the chars :(
std::string getU8Str(const std::filesystem::path& path);

#if defined(_WIN32)

/// Widens the provided UTF8 string into UTF16 wchars.
SLANG_EXPORT std::wstring widen(std::string_view str);

/// Narrows the provided UTF16 string into UTF8.
SLANG_EXPORT std::string narrow(std::wstring_view str);

#else

/// Widens the provided UTF8 string into UTF16 wchars.
inline std::string_view widen(std::string_view str) {
    return str;
}

/// Narrows the provided UTF16 string into UTF8.
inline std::string_view narrow(std::string_view str) {
    return str;
}

#endif

} // namespace slang
