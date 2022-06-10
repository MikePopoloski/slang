#include <flat_hash_map.hpp>

#include "slang/util/Hash.h"
template<typename K, typename V, typename H = slang::Hasher<K>, typename E = std::equal_to<K>,
         typename A = std::allocator<std::pair<K, V>>> using flat_hash_map = ska::flat_hash_map<K, V, H, E, A>;
