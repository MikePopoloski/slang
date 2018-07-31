//------------------------------------------------------------------------------
// Hash.cpp
// General hashing algorithms.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/util/Hash.h"

#include <cstdlib>

#define XXH_INLINE_ALL
#include <xxhash/xxhash.h>

namespace slang {

size_t xxhash(const void* input, size_t len, size_t seed) {
#ifdef PLATFORM_X64
    return xxhash64(input, len, (uint64_t)seed);
#else
    return xxhash32(input, len, (uint32_t)seed);
#endif
}

uint32_t xxhash32(const void* input, size_t len, uint32_t seed) {
    return XXH32(input, len, seed);
}

uint64_t xxhash64(const void* input, size_t len, uint64_t seed) {
    return XXH64(input, len, seed);
}

}