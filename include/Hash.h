//------------------------------------------------------------------------------
// Hash.h
// General hashing algorithms.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include <cstddef>
#include <cstdint>

namespace slang {

// Imported hashing functions from the xxhash library.
uint32_t xxhash32(const void* input, size_t len, uint32_t seed);
uint64_t xxhash64(const void* input, size_t len, uint64_t seed);

// uses 32-bit or 64-bit implementation depending on platform
size_t xxhash(const void* input, size_t len, size_t seed);

}
