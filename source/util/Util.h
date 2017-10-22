//------------------------------------------------------------------------------
// Util.h
// Various utility functions and basic types used throughout the library.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <cstddef>                      // for std::byte
#include <cstdint>                      // for sized integer types
#include <climits>                      // for type size macros
#include <new>                          // for placement new
#include <optional>                     // for std::optional
#include <string_view>                  // for std::string_view
#include <utility>                      // for many random utility functions

using std::int8_t;
using std::int16_t;
using std::int32_t;
using std::int64_t;
using std::intptr_t;
using std::nullptr_t;
using std::optional;
using std::ptrdiff_t;
using std::size_t;
using std::string_view;
using std::uint8_t;
using std::uint16_t;
using std::uint32_t;
using std::uint64_t;
using std::uintptr_t;

// Clang 5.0 and 6.0 fails to compile <variant> from libstdc++
#ifdef __clang__
#include "compat/variant.h"
namespace std {
using mpark::variant;
using mpark::monostate;
using mpark::get;
using mpark::get_if;
using mpark::visit;
}
#else
#include <variant>
#endif

#include "ppk_assert/ppk_assert.h"

// Just delegate our assert handling to the 3rd part lib
#define ASSERT PPK_ASSERT
#define THROW_UNREACHABLE throw std::logic_error("Default case should be unreachable!")

#include "gsl/gsl"

using gsl::span;
using gsl::make_span;

namespace slang {

/// Converts a span of characters into a string_view.
inline string_view to_string_view(span<char> text) {
    return string_view(text.data(), text.length());
}

}