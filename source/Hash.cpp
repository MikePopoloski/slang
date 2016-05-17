#include "Hash.h"

#include <cstdlib>

#define XXH_PRIVATE_API
#include "../external/xxhash/xxhash.c"

namespace slang {

size_t xxhash(const void* input, size_t len, size_t seed) {
#ifdef PLATFORM_X64
    return xxhash64(input, len, seed);
#else
    return xxhash32(input, len, seed);
#endif
}

uint32_t xxhash32(const void* input, size_t len, uint32_t seed) {
    return XXH32(input, len, seed);
}

uint64_t xxhash64(const void* input, size_t len, uint64_t seed) {
    return XXH64(input, len, seed);
}

}