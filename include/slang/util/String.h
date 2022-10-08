//------------------------------------------------------------------------------
//! @file String.h
//! @brief Various string utilities
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <optional>

#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang {

/// Converts a span of characters into a string_view.
inline string_view toStringView(span<char> text) {
    return string_view(text.data(), text.size());
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
std::optional<int32_t> strToInt(string_view str, size_t* pos = nullptr, int base = 10);

/// Parses the provided @a str in the specified @a base into an unsigned integer.
/// If @a pos is non-null, it will be set to point to the first character in the
/// source string that was not part of the conversion.
///
/// @return the converted value, or nullopt if conversion fails (invalid string, overflow, etc).
std::optional<uint32_t> strToUInt(string_view str, size_t* pos = nullptr, int base = 10);

/// Parses the provided @a str into a floating point value.
/// If @a pos is non-null, it will be set to point to the first character in the
/// source string that was not part of the conversion.
///
/// @return the converted value, or nullopt if conversion fails (invalid string, overflow, etc).
std::optional<double> strToDouble(string_view str, size_t* pos = nullptr);

/// Converts the provided string to all uppercase characters (assuming ASCII contents).
/// The string is converted in place.
void strToUpper(std::string& str);

/// Converts the provided string to all lowercase characters (assuming ASCII contents).
/// The string is converted in place.
void strToLower(std::string& str);

/// Determines the number of edits to the left string that are required to
/// change it into the right string.
/// If @a allowReplacements is true, characters can be substituted as needed.
/// Otherwise, only swaps are allowed.
///
/// If @a maxDistance is >0 and the computed distance is at least that much, give
/// up and return maxDistance + 1.
int editDistance(string_view left, string_view right, bool allowReplacements = true,
                 int maxDistance = 0);

// TODO: remove once we have C++20
inline bool startsWith(string_view str, string_view prefix) {
    return str.size() >= prefix.size() && str.compare(0, prefix.size(), prefix) == 0;
};
inline bool endsWith(string_view str, string_view suffix) {
    return str.size() >= suffix.size() &&
           str.compare(str.size() - suffix.size(), suffix.size(), suffix) == 0;
};

#if defined(_MSC_VER)

/// Widens the provided UTF8 string into UTF16 wchars.
SLANG_EXPORT std::wstring widen(string_view str);

/// Widens the provided UTF16 string into UTF8.
SLANG_EXPORT std::string narrow(std::wstring_view str);

#else

/// Widens the provided UTF8 string into UTF16 wchars.
inline string_view widen(string_view str) {
    return str;
}

/// Widens the provided UTF16 string into UTF8.
inline string_view narrow(string_view str) {
    return str;
}

#endif

} // namespace slang
