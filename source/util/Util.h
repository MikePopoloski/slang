//------------------------------------------------------------------------------
// Util.h
// Various utility functions and basic types used throughout the library.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

namespace slang {

/// Converts a span of characters into a string_view.
inline string_view to_string_view(span<char> text) {
    return string_view(text.data(), text.length());
}

}