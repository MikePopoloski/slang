//------------------------------------------------------------------------------
//! @file ConcurrentMap.h
//! @brief Concurrent unordered hash map and set
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Hash.h"

#define BOOST_UNORDERED_DISABLE_PARALLEL_ALGORITHMS
#ifdef SLANG_BOOST_SINGLE_HEADER
#    include <boost_concurrent.hpp>
#else
#    include <boost/unordered/concurrent_flat_map.hpp>
#    include <boost/unordered/concurrent_flat_set.hpp>
#endif

namespace slang {

template<typename K, typename V, typename H = hash<K>, typename E = std::equal_to<K>,
         typename A = std::allocator<std::pair<const K, V>>>
using concurrent_map = boost::concurrent_flat_map<K, V, H, E, A>;

template<typename T, typename H = hash<T>, typename E = std::equal_to<T>,
         typename A = std::allocator<T>>
using concurrent_set = boost::concurrent_flat_set<T, H, E, A>;

} // namespace slang
