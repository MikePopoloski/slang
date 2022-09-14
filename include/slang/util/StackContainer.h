//------------------------------------------------------------------------------
//! @file StackContainer.h
//! @brief Stack allocated containers
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Hash.h"

namespace slang {

template<typename T, size_t N>
struct StackAllocStorage {
    alignas(alignof(T)) char buffer[sizeof(T) * N];
    T* ptr = reinterpret_cast<T*>(buffer);

    T* getBuffer() { return reinterpret_cast<T*>(buffer); }
};

template<typename T, size_t N>
class StackAllocator {
public:
    using value_type = T;

    StackAllocator(const StackAllocator&) = default;
    StackAllocator& operator=(const StackAllocator&) = delete;

    StackAllocator(StackAllocStorage<T, N>* storage) noexcept : storage(storage) {}

    template<typename U>
    struct rebind {
        using other = StackAllocator<U, N>;
    };

    T* allocate(size_t n) {
        if (N - size_t(storage->ptr - storage->getBuffer()) >= n) {
            T* result = storage->ptr;
            storage->ptr += n;
            return result;
        }

        return static_cast<T*>(::operator new(sizeof(T) * n));
    }

    void deallocate(T* p, std::size_t n) noexcept {
        // If the pointer is in our buffer, possibly "deallocate" by moving the high water mark
        // back. Otherwise it was heap allocated and we must free with delete.
        if (std::less_equal<T*>()(storage->getBuffer(), p) &&
            std::less<T*>()(p, storage->getBuffer() + N)) {
            if (p + n == storage->ptr)
                storage->ptr = p;
        }
        else {
            ::operator delete(p);
        }
    }

    template<typename T1, size_t N1, class T2, size_t N2>
    friend bool operator==(const StackAllocator<T1, N1>& x,
                           const StackAllocator<T2, N2>& y) noexcept;

private:
    template<typename U, size_t M>
    friend class StackAllocator;

    StackAllocStorage<T, N>* storage;
};

template<typename T, size_t N, class U, size_t M>
inline bool operator==(const StackAllocator<T, N>& x, const StackAllocator<U, M>& y) noexcept {
    return N == M && x.storage == y.storage;
}

template<typename T, size_t N, class U, size_t M>
inline bool operator!=(const StackAllocator<T, N>& x, const StackAllocator<U, M>& y) noexcept {
    return !(x == y);
}

/// A hash map container that allocates room for its first `N` elements on the stack.
/// Prefer this over a normal hash map for temporary stack variables and small maps
/// where heap allocations can be avoided.
template<typename K, typename V, size_t N,
         typename Entry = ska::detailv3::sherwood_v3_entry<std::pair<K, V>>,
         typename Alloc = StackAllocator<Entry, N>>
class SmallMap : private StackAllocStorage<Entry, N>,
                 public flat_hash_map<K, V, std::hash<K>, std::equal_to<K>, Alloc> {

    using BaseType = flat_hash_map<K, V, std::hash<K>, std::equal_to<K>, Alloc>;

public:
    SmallMap() : BaseType(Alloc(this)) {}
};

/// A hash set container that allocates room for its first `N` elements on the stack.
/// Prefer this over a normal hash set for temporary stack variables and small sets
/// where heap allocations can be avoided.
template<typename T, size_t N, typename Entry = ska::detailv3::sherwood_v3_entry<T>,
         typename Alloc = StackAllocator<Entry, N>>
class SmallSet : private StackAllocStorage<Entry, N>,
                 public flat_hash_set<T, std::hash<T>, std::equal_to<T>, Alloc> {

    using BaseType = flat_hash_set<T, std::hash<T>, std::equal_to<T>, Alloc>;

public:
    SmallSet() : BaseType(Alloc(this)) {}
};

} // namespace slang
