#pragma once

namespace slang {

uint32_t xxhash32(const void* input, size_t len, uint32_t seed);
uint64_t xxhash64(const void* input, size_t len, uint64_t seed);

}