//------------------------------------------------------------------------------
//! @file Hash.h
//! @brief General hashing algorithms
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <ankerl/unordered_dense.h>
#include <flat_hash_map.hpp>

#include "slang/util/Util.h"

namespace slang {

inline void hash_combine(size_t&) {
}

/// Hash combining function, based on the function from Boost.
/// It hashes the provided @a v object and combines it with the
/// previous hash value in @a seed.
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

namespace slang {

// Specialize a user-defined type instead of std::hash
template<typename T>
struct Hasher {
    size_t operator()(const T& t) const { return std::hash<T>()(t); }
};

template<typename... TT>
struct Hasher<std::tuple<TT...>> {
    size_t operator()(const std::tuple<TT...>& tt) const {
        size_t seed = 0;
        slang::detail::HashValueImpl<std::tuple<TT...>>::apply(seed, tt);
        return seed;
    }
};

template<typename K, typename V, typename H = slang::Hasher<K>, typename E = std::equal_to<K>,
         typename A = std::allocator<std::pair<K, V>>>
using flat_hash_map = ska::flat_hash_map<K, V, H, E, A>;

template<typename T, typename H = slang::Hasher<T>, typename E = std::equal_to<T>,
         typename A = std::allocator<T>>
using flat_hash_set = ska::flat_hash_set<T, H, E, A>;

} // namespace slang
