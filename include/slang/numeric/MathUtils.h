//------------------------------------------------------------------------------
//! @file MathUtils.h
//! @brief Various math utilities
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <climits>
#include <cmath>
#include <cstdint>
#include <optional>

namespace slang {

/// Performs an addition of two signed 32-bit integers and returns the
/// result if it does not overflow. If it does, nullopt is returned instead.
inline std::optional<int32_t> checkedAddS32(int32_t a, int32_t b) {
#if defined(_MSC_VER)
    int64_t p = int64_t(a) + int64_t(b);
    bool fits = p >= std::numeric_limits<int32_t>::min() &&
                p <= std::numeric_limits<int32_t>::max();
    return fits ? std::make_optional(int32_t(p)) : std::nullopt;
#else
    int32_t result;
    return __builtin_add_overflow(a, b, &result) ? std::nullopt : std::make_optional(result);
#endif
}

/// Performs a subtraction of two signed 32-bit integers and returns the
/// result if it does not overflow. If it does, nullopt is returned instead.
inline std::optional<int32_t> checkedSubS32(int32_t a, int32_t b) {
#if defined(_MSC_VER)
    int64_t p = int64_t(a) - int64_t(b);
    bool fits = p >= std::numeric_limits<int32_t>::min() &&
                p <= std::numeric_limits<int32_t>::max();
    return fits ? std::make_optional(int32_t(p)) : std::nullopt;
#else
    int32_t result;
    return __builtin_sub_overflow(a, b, &result) ? std::nullopt : std::make_optional(result);
#endif
}

/// Performs a multiplication of two unsigned 32-bit integers and returns the
/// result if it does not overflow. If it does, nullopt is returned instead.
inline std::optional<uint32_t> checkedMulU32(uint32_t a, uint32_t b) {
#if defined(_MSC_VER)
    uint64_t p = uint64_t(a) * uint64_t(b);
    return p <= std::numeric_limits<uint32_t>::max() ? std::make_optional(uint32_t(p))
                                                     : std::nullopt;
#else
    uint32_t result;
    return __builtin_mul_overflow(a, b, &result) ? std::nullopt : std::make_optional(result);
#endif
}

/// Performs a multiplication of two unsigned 64-bit integers and returns the
/// result if it does not overflow. If it does, nullopt is returned instead.
inline std::optional<uint64_t> checkedMulU64(uint64_t a, uint64_t b) {
#if defined(_MSC_VER)
    uint64_t high;
    auto result = _umul128(a, b, &high);
    return high ? std::nullopt : std::make_optional(result);
#else
    uint64_t result;
    return __builtin_mul_overflow(a, b, &result) ? std::nullopt : std::make_optional(result);
#endif
}

} // namespace slang
