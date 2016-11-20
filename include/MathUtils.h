//------------------------------------------------------------------------------
// Math.h
// Various math utilities.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <cmath>
#include <climits>
#include <cstdint>

namespace slang {

inline uint32_t clog2(uint64_t value) {
#if defined (_MSC_VER)
    unsigned long index;
    if (!_BitScanReverse64(&index, value))
        return 0;
    return index + (value & (value - 1) ? 1 : 0);
#else
    uint32_t log = sizeof(value) * CHAR_BIT - 1 - __builtin_clzll(value);
    return (value - (1 << log)) ? log + 1 : log;
#endif
}

/// If value is zero, returns 64. Otherwise, returns the number of zeros, starting
/// from the MSB.
inline uint32_t countLeadingZeros(uint64_t value) {
    if (value == 0)
        return 64;
#if defined (_MSC_VER)
    unsigned long index;
    _BitScanReverse64(&index, value);
    return index ^ 63;
#else
    return __builtin_clzll(value);
#endif
}

inline uint32_t countLeadingOnes(uint64_t value) {
    return countLeadingZeros(~value);
}

inline int countPopulation(uint64_t value) {
#if defined (_MSC_VER)
	return (int)__popcnt64(value);
#else
	return (int)__builtin_popcountll(value);
#endif
}

}