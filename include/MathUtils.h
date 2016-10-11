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

// TODO: better impl of this
inline uint32_t clog2(uint64_t value) { return (uint32_t)std::ceil(std::log2(value)); }

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