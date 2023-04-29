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
#include <span>
#include <string_view>
#include <utility>

#include "slang/slang_export.h"
#include "slang/util/Assert.h"
#include "slang/util/Enum.h"
#include "slang/util/NotNull.h"

#if defined(__GNUC__) || defined(__INTEL_COMPILER) || defined(__clang__)
#    define SLANG_LIKELY(x) __builtin_expect(x, 1)
#    define SLANG_UNLIKELY(x) __builtin_expect(x, 0)
#else
#    define SLANG_LIKELY(x) (x)
#    define SLANG_UNLIKELY(x) (x)
#endif

using namespace std::literals;

namespace slang {

using byte = std::byte;
using int16_t = std::int16_t;
using int32_t = std::int32_t;
using int64_t = std::int64_t;
using int8_t = std::int8_t;
using intptr_t = std::intptr_t;
using nullptr_t = std::nullptr_t;
using ptrdiff_t = std::ptrdiff_t;
using size_t = std::size_t;
using uint16_t = std::uint16_t;
using uint32_t = std::uint32_t;
using uint64_t = std::uint64_t;
using uint8_t = std::uint8_t;
using uintptr_t = std::uintptr_t;

} // namespace slang
