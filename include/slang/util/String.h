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
#include <vector>

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

/// Splits the provided string into substrings based on the provided delimiter.
std::vector<std::string_view> splitString(std::string_view str, char delimiter);

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

#if defined(_WIN32)

/// Gets a string representation of the given path, in UTF-8 encoding.
inline std::string getU8Str(const std::filesystem::path& path) {
    return path.string();
}

#else

/// Gets a string representation of the given path, in UTF-8 encoding.
inline const std::string& getU8Str(const std::filesystem::path& path) {
    return path.native();
}

#endif

} // namespace slang
