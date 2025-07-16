//------------------------------------------------------------------------------
//! @file SmallMap.h
//! @brief Stack-allocated hash map and set
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/FlatMap.h"

namespace slang {

namespace detail::hashing {

template<size_t N, size_t Align = alignof(std::max_align_t)>
class StackAllocStorage {
public:
    StackAllocStorage() noexcept : ptr(buffer) {}
    StackAllocStorage(const StackAllocStorage& other) = delete;
    StackAllocStorage& operator=(const StackAllocStorage& other) = delete;

    template<size_t ReqAlign>
    char* allocate(size_t n) {
        static_assert(ReqAlign <= Align, "alignment is too small for this arena");

        SLANG_ASSERT(isInBuffer(ptr));
        auto aligned_n = alignUp(n);
        if (static_cast<decltype(aligned_n)>(buffer + N - ptr) >= aligned_n) {
            char* r = ptr;
            ptr += aligned_n;
            return r;
        }

        static_assert(Align <= alignof(std::max_align_t),
                      "you've chosen an alignment that is larger than alignof(std::max_align_t), "
                      "and cannot be guaranteed by normal operator new");
        return static_cast<char*>(::operator new(n));
    }

    void deallocate(char* p, size_t n) noexcept {
        SLANG_ASSERT(isInBuffer(ptr));
        if (isInBuffer(p)) {
            n = alignUp(n);
            if (p + n == ptr)
                ptr = p;
        }
        else {
            ::operator delete(p);
        }
    }

private:
    static constexpr size_t alignUp(size_t n) noexcept { return (n + (Align - 1)) & ~(Align - 1); }

    bool isInBuffer(char* p) noexcept {
        return uintptr_t(buffer) <= uintptr_t(p) && uintptr_t(p) <= uintptr_t(buffer) + N;
    }

    alignas(Align) char buffer[N];
    char* ptr;
};

template<typename T, size_t N, size_t Align = alignof(T)>
class StackAllocator {
public:
    using value_type = T;
    using Storage = StackAllocStorage<N, Align>;

    StackAllocator(Storage& storage) noexcept : storage(storage) {
        static_assert(N % Align == 0, "size N needs to be a multiple of alignment Align");
    }

    template<typename U>
    StackAllocator(const StackAllocator<U, N, Align>& other) noexcept : storage(other.storage) {}

    StackAllocator(const StackAllocator&) = default;
    StackAllocator& operator=(const StackAllocator&) = delete;

    template<typename U>
    struct rebind {
        using other = StackAllocator<U, N, Align>;
    };

    T* allocate(size_t n) {
        return reinterpret_cast<T*>(storage.template allocate<alignof(T)>(n * sizeof(T)));
    }

    void deallocate(T* p, size_t n) noexcept {
        storage.deallocate(reinterpret_cast<char*>(p), n * sizeof(T));
    }

    template<typename T1, size_t N1, size_t A1, typename T2, size_t N2, size_t A2>
    friend bool operator==(const StackAllocator<T1, N1, A1>& x,
                           const StackAllocator<T2, N2, A2>& y) noexcept;

private:
    template<typename U, size_t M, size_t A>
    friend class StackAllocator;

    Storage& storage;
};

template<typename T1, size_t N1, size_t A1, typename T2, size_t N2, size_t A2>
inline bool operator==(const StackAllocator<T1, N1, A1>& x,
                       const StackAllocator<T2, N2, A2>& y) noexcept {
    return N1 == N2 && A1 == A2 && &x.storage == &y.storage;
}

} // namespace detail::hashing

/// A hash map container that allocates room for its first `N` elements on the stack.
/// Prefer this over a normal hash map for temporary stack variables and small maps
/// where heap allocations can be avoided.
template<typename K, typename V, size_t N, typename Entry = std::pair<const K, V>,
         typename Alloc = detail::hashing::StackAllocator<Entry, N * sizeof(Entry)>>
class SmallMap : private Alloc::Storage,
                 public flat_hash_map<K, V, hash<K>, std::equal_to<K>, Alloc> {
    using BaseType = flat_hash_map<K, V, hash<K>, std::equal_to<K>, Alloc>;

public:
    SmallMap() : BaseType(Alloc(*this)) {}
};

/// A hash set container that allocates room for its first `N` elements on the stack.
/// Prefer this over a normal hash set for temporary stack variables and small sets
/// where heap allocations can be avoided.
template<typename T, size_t N, typename Alloc = detail::hashing::StackAllocator<T, N * sizeof(T)>>
class SmallSet : private Alloc::Storage, public flat_hash_set<T, hash<T>, std::equal_to<T>, Alloc> {
    using BaseType = flat_hash_set<T, hash<T>, std::equal_to<T>, Alloc>;

public:
    SmallSet() : BaseType(Alloc(*this)) {}

    template<typename TIterator>
    SmallSet(TIterator first, TIterator last) : BaseType(first, last, Alloc(*this)) {}
};

} // namespace slang
