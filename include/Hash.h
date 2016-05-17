#pragma once

#include <cstdint>

namespace slang {

uint32_t xxhash32(const void* input, size_t len, uint32_t seed);
uint64_t xxhash64(const void* input, size_t len, uint64_t seed);

// uses 32-bit or 64-bit implementation depending on platform
size_t xxhash(const void* input, size_t len, size_t seed);

}