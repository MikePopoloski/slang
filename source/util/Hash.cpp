//------------------------------------------------------------------------------
// Hash.cpp
// General hashing algorithms
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/util/Hash.h"

#include <cstdlib>

#define XXH_INLINE_ALL
#include <xxhash/xxhash.h>

namespace slang {

size_t xxhash(const void* input, size_t len, size_t seed) {
    if constexpr (sizeof(input) == 4)
        return XXH32(input, len, (uint32_t)seed);
    else
        return XXH64(input, len, (uint64_t)seed);
}

} // namespace slang