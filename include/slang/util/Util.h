//------------------------------------------------------------------------------
//! @file Util.h
//! @brief Various utility functions and basic types used throughout the library
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <span.hpp>
#include <string_view>
#include <utility>

#include "slang/slang_export.h"
#include "slang/util/Assert.h"
#include "slang/util/Enum.h"
#include "slang/util/NotNull.h"

using namespace std::literals;

namespace slang {

using nonstd::span;
using string_view = std::string_view;
using byte = std::byte;
using int16_t = std::int16_t;
using int32_t = std::int32_t;
using int64_t = std::int64_t;
using int8_t = std::int8_t;
using intptr_t = std::intptr_t;
using nullptr_t = std::nullptr_t;
using ptrdiff_t = std::ptrdiff_t;
using size_t = std::size_t;
using string_view = std::string_view;
using uint16_t = std::uint16_t;
using uint32_t = std::uint32_t;
using uint64_t = std::uint64_t;
using uint8_t = std::uint8_t;
using uintptr_t = std::uintptr_t;

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

} // namespace slang
