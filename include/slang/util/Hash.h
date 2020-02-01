//------------------------------------------------------------------------------
//! @file Hash.h
//! @brief General hashing algorithms
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang {

// Imported hashing functions from the xxhash library.
uint32_t xxhash32(const void* input, size_t len, uint32_t seed);
uint64_t xxhash64(const void* input, size_t len, uint64_t seed);

// uses 32-bit or 64-bit implementation depending on platform
size_t xxhash(const void* input, size_t len, size_t seed);

inline void hash_combine(size_t&) {
}

/// Hash combining function, based on the function from Boost.
template<typename T, typename... Rest>
inline void hash_combine(size_t& seed, const T& v, Rest... rest) {
    std::hash<T> hasher;
    seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    hash_combine(seed, rest...);
}

namespace detail {

template<typename Tuple, size_t Index = std::tuple_size<Tuple>::value - 1>
struct HashValueImpl {
    static void apply(size_t& seed, const Tuple& tuple) {
        HashValueImpl<Tuple, Index - 1>::apply(seed, tuple);
        hash_combine(seed, std::get<Index>(tuple));
    }
};

template<typename Tuple>
struct HashValueImpl<Tuple, 0> {
    static void apply(size_t& seed, const Tuple& tuple) { hash_combine(seed, std::get<0>(tuple)); }
};

} // namespace detail

} // namespace slang

namespace std {

template<typename... TT>
struct hash<std::tuple<TT...>> {
    size_t operator()(const std::tuple<TT...>& tt) const {
        size_t seed = 0;
        slang::detail::HashValueImpl<std::tuple<TT...>>::apply(seed, tt);
        return seed;
    }
};

} // namespace std