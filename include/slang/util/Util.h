//------------------------------------------------------------------------------
// Util.h
// Various utility functions and basic types used throughout the library.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <climits>     // for type size macros
#include <cstddef>     // for std::byte
#include <cstdint>     // for sized integer types
#include <new>         // for placement new
#include <optional>    // for std::optional
#include <string_view> // for std::string_view
#include <utility>     // for many random utility functions

#include "slang/util/Assert.h"
#include "slang/util/NotNull.h"

using std::byte;
using std::int16_t;
using std::int32_t;
using std::int64_t;
using std::int8_t;
using std::intptr_t;
using std::nullptr_t;
using std::optional;
using std::ptrdiff_t;
using std::size_t;
using std::string_view;
using std::uint16_t;
using std::uint32_t;
using std::uint64_t;
using std::uint8_t;
using std::uintptr_t;

using namespace std::literals;

#define span_CONFIG_INDEX_TYPE std::size_t
#define span_FEATURE_COMPARISON 0
#include <span.hpp>
using nonstd::span;

#include <bitmask.hpp>
using bitmask_lib::bitmask;

namespace slang {

template<typename T>
struct always_false : std::false_type {};

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
