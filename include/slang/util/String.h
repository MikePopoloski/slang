//------------------------------------------------------------------------------
//! @file String.h
//! @brief Various string utilities
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang {

/// Converts a span of characters into a string_view.
inline string_view to_string_view(span<char> text) {
    return string_view(text.data(), text.size());
}

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