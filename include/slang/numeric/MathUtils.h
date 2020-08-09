//------------------------------------------------------------------------------
//! @file MathUtils.h
//! @brief Various math utilities
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <climits>
#include <cmath>
#include <optional>

#if defined(_MSC_VER)
#    include <intrin.h>
#endif

namespace slang {

inline uint32_t clog2(uint64_t value) {
#if defined(_MSC_VER)
    unsigned long index;
    if (!_BitScanReverse64(&index, value))
        return 0;
    return index + (value & (value - 1) ? 1 : 0);
#else
    if (value == 0)
        return 0;
    uint32_t log = sizeof(value) * CHAR_BIT - 1 - (uint32_t)__builtin_clzll(value);
    return (value - (1ULL << log)) ? log + 1 : log;
#endif
}

/// If value is zero, returns 32. Otherwise, returns the number of zeros, starting
/// from the MSB.
inline uint32_t countLeadingZeros32(uint32_t value) {
    if (value == 0)
        return 32;
#if defined(_MSC_VER)
    unsigned long index;
    _BitScanReverse(&index, value);
    return index ^ 31;
#else
    return (uint32_t)__builtin_clz(value);
#endif
}

/// If value is zero, returns 64. Otherwise, returns the number of zeros, starting
/// from the MSB.
inline uint32_t countLeadingZeros64(uint64_t value) {
    if (value == 0)
        return 64;
#if defined(_MSC_VER)
    unsigned long index;
    _BitScanReverse64(&index, value);
    return index ^ 63;
#else
    return (uint32_t)__builtin_clzll(value);
#endif
}

inline uint32_t countLeadingOnes64(uint64_t value) {
    return countLeadingZeros64(~value);
}

inline uint32_t countPopulation64(uint64_t value) {
#if defined(_MSC_VER)
    return (uint32_t)__popcnt64(value);
#else
    return (uint32_t)__builtin_popcountll(value);
#endif
}

/// Performs a multiplication of two unsigned 32-bit integers and return the
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

} // namespace slang
