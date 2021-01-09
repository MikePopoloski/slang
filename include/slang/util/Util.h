//------------------------------------------------------------------------------
//! @file Util.h
//! @brief Various utility functions and basic types used throughout the library
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <climits>     // for type size macros
#include <cstddef>     // for std::byte
#include <cstdint>     // for sized integer types
#include <cstring>     // for memcpy
#include <new>         // for placement new
#include <optional>    // for std::optional
#include <string_view> // for std::string_view
#include <utility>     // for many random utility functions

#include "slang/util/Assert.h"
#include "slang/util/Enum.h"
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

#include <span.hpp>
using nonstd::span;

// TODO: remove once C++20 bit_cast is available
template<typename Dest, typename Source>
inline Dest bit_cast(const Source& src) noexcept {
    static_assert(sizeof(Dest) == sizeof(Source),
                  "bit_cast requires source and destination to be the same size");
    static_assert(std::is_trivially_copyable<Dest>::value,
                  "bit_cast requires the destination type to be copyable");
    static_assert(std::is_trivially_copyable<Source>::value,
                  "bit_cast requires the source type to be copyable");
    Dest dst;
    std::memcpy(&dst, &src, sizeof(Dest));
    return dst;
}
