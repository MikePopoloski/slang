//------------------------------------------------------------------------------
//! @file String.h
//! @brief Various string utilities
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang {

/// Converts a span of characters into a string_view.
inline string_view toStringView(span<char> text) {
    return string_view(text.data(), text.size());
}

void uintToStr(SmallVector<char>& buffer, uint32_t value);
void uintToStr(SmallVector<char>& buffer, uint64_t value);

optional<int32_t> strToInt(string_view str, size_t* pos = nullptr, int base = 10);
optional<uint32_t> strToUInt(string_view str, size_t* pos = nullptr, int base = 10);
optional<double> strToDouble(string_view str, size_t* pos = nullptr);

/// Determines the number of edits to the left string that are required to
/// change it into the right string.
int editDistance(string_view left, string_view right, bool allowReplacements = true,
                 int maxDistance = 0);

#if defined(_MSC_VER)

std::wstring widen(string_view str);
std::string narrow(std::wstring_view str);

#else

inline string_view widen(string_view str) {
    return str;
}

inline string_view narrow(string_view str) {
    return str;
}

#endif

} // namespace slang