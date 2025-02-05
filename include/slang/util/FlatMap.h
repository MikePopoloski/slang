//------------------------------------------------------------------------------
//! @file FlatMap.h
//! @brief Flat unordered hash map and set
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Hash.h"

#ifdef SLANG_BOOST_SINGLE_HEADER
#    include <boost_unordered.hpp>
#else
#    include <boost/unordered/unordered_flat_map.hpp>
#    include <boost/unordered/unordered_flat_set.hpp>
#endif

namespace slang {

template<typename K, typename V, typename H = hash<K>, typename E = std::equal_to<K>,
         typename A = std::allocator<std::pair<const K, V>>>
using flat_hash_map = boost::unordered_flat_map<K, V, H, E, A>;

template<typename T, typename H = hash<T>, typename E = std::equal_to<T>,
         typename A = std::allocator<T>>
using flat_hash_set = boost::unordered_flat_set<T, H, E, A>;

} // namespace slang
