#include "slang.h"

namespace slang {

// pulled from the xxHash project:
// https://github.com/Cyan4973/xxHash

#define PRIME32_1   2654435761U
#define PRIME32_2   2246822519U
#define PRIME32_3   3266489917U
#define PRIME32_4    668265263U
#define PRIME32_5    374761393U

#define XXH_rotl32(x,r) _rotl(x,r)

uint32_t xxhash32(const void* input, size_t len, uint32_t seed) {
    // we assume at least 4-byte alignment of input, which should
    // always be true for the systems we're running on
    const uint8_t* p = (const uint8_t*)input;
    const uint8_t* bEnd = p + len;
    uint32_t h32;

    if (len >= 16) {
        const uint8_t* const limit = bEnd - 16;
        uint32_t v1 = seed + PRIME32_1 + PRIME32_2;
        uint32_t v2 = seed + PRIME32_2;
        uint32_t v3 = seed + 0;
        uint32_t v4 = seed - PRIME32_1;

        do {
            v1 += *(uint32_t*)p * PRIME32_2;
            v1 = XXH_rotl32(v1, 13);
            v1 *= PRIME32_1;
            p += 4;
            v2 += *(uint32_t*)p * PRIME32_2;
            v2 = XXH_rotl32(v2, 13);
            v2 *= PRIME32_1;
            p += 4;
            v3 += *(uint32_t*)p * PRIME32_2;
            v3 = XXH_rotl32(v3, 13);
            v3 *= PRIME32_1;
            p += 4;
            v4 += *(uint32_t*)p * PRIME32_2;
            v4 = XXH_rotl32(v4, 13);
            v4 *= PRIME32_1;
            p += 4;
        } while (p <= limit);

        h32 = XXH_rotl32(v1, 1) + XXH_rotl32(v2, 7) + XXH_rotl32(v3, 12) + XXH_rotl32(v4, 18);
    }
    else
        h32 = seed + PRIME32_5;

    h32 += (uint32_t)len;
    while (p + 4 <= bEnd) {
        h32 += *(uint32_t*)p * PRIME32_3;
        h32 = XXH_rotl32(h32, 17) * PRIME32_4;
        p += 4;
    }

    while (p < bEnd) {
        h32 += (*p) * PRIME32_5;
        h32 = XXH_rotl32(h32, 11) * PRIME32_1;
        p++;
    }

    h32 ^= h32 >> 15;
    h32 *= PRIME32_2;
    h32 ^= h32 >> 13;
    h32 *= PRIME32_3;
    h32 ^= h32 >> 16;

    return h32;
}

}