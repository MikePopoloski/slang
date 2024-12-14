//------------------------------------------------------------------------------
//! @file Hash.h
//! @brief General hashing algorithms
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <array>
#include <cstring>

#ifdef SLANG_BOOST_SINGLE_HEADER
#    include <boost_unordered.hpp>
#else
#    include <boost/unordered/unordered_flat_map.hpp>
#    include <boost/unordered/unordered_flat_set.hpp>
#    include <boost/unordered/unordered_node_map.hpp>
#    include <boost/unordered/unordered_node_set.hpp>
#endif

#include "slang/util/Util.h"

#if defined(_MSC_VER) && defined(_M_X64)
#    include <intrin.h>
#    pragma intrinsic(_umul128)
#endif

namespace slang {

namespace detail::hashing {

// Hashing logic taken from:
// https://github.com/martinus/unordered_dense/blob/main/include/ankerl/unordered_dense.h
//
// This is a stripped-down implementation of wyhash: https://github.com/wangyi-fudan/wyhash
// No big-endian support (because different values on different machines don't matter),
// hardcodes seed and the secret, reformattes the code, and clang-tidy fixes.

static inline void mum(uint64_t* a, uint64_t* b) {
#if defined(__SIZEOF_INT128__)
    __uint128_t r = *a;
    r *= *b;
    *a = static_cast<uint64_t>(r);
    *b = static_cast<uint64_t>(r >> 64U);
#elif defined(_MSC_VER) && defined(_M_X64)
    *a = _umul128(*a, *b, b);
#else
    uint64_t ha = *a >> 32U;
    uint64_t hb = *b >> 32U;
    uint64_t la = static_cast<uint32_t>(*a);
    uint64_t lb = static_cast<uint32_t>(*b);
    uint64_t hi{};
    uint64_t lo{};
    uint64_t rh = ha * hb;
    uint64_t rm0 = ha * lb;
    uint64_t rm1 = hb * la;
    uint64_t rl = la * lb;
    uint64_t t = rl + (rm0 << 32U);
    auto c = static_cast<uint64_t>(t < rl);
    lo = t + (rm1 << 32U);
    c += static_cast<uint64_t>(lo < t);
    hi = rh + (rm0 >> 32U) + (rm1 >> 32U) + c;
    *a = lo;
    *b = hi;
#endif
}

// multiply and xor mix function, aka MUM
[[nodiscard]] static inline uint64_t mix(uint64_t a, uint64_t b) {
    mum(&a, &b);
    return a ^ b;
}

// read functions. WARNING: we don't care about endianness, so results are different on big endian!
[[nodiscard]] static inline uint64_t r8(const uint8_t* p) {
    uint64_t v{};
    std::memcpy(&v, p, 8U);
    return v;
}

[[nodiscard]] static inline uint64_t r4(const uint8_t* p) {
    uint32_t v{};
    std::memcpy(&v, p, 4);
    return v;
}

// reads 1, 2, or 3 bytes
[[nodiscard]] static inline uint64_t r3(const uint8_t* p, size_t k) {
    return (static_cast<uint64_t>(p[0]) << 16U) | (static_cast<uint64_t>(p[k >> 1U]) << 8U) |
           p[k - 1];
}

[[maybe_unused]] [[nodiscard]] static inline uint64_t hash(void const* key, size_t len) {
    static constexpr auto secret = std::array{UINT64_C(0xa0761d6478bd642f),
                                              UINT64_C(0xe7037ed1a0b428db),
                                              UINT64_C(0x8ebc6af09c88c6e3),
                                              UINT64_C(0x589965cc75374cc3)};

    auto const* p = static_cast<uint8_t const*>(key);
    uint64_t seed = secret[0];
    uint64_t a{};
    uint64_t b{};
    if (len <= 16) [[likely]] {
        if (len >= 4) [[likely]] {
            a = (r4(p) << 32U) | r4(p + ((len >> 3U) << 2U));
            b = (r4(p + len - 4) << 32U) | r4(p + len - 4 - ((len >> 3U) << 2U));
        }
        else if (len > 0) [[likely]] {
            a = r3(p, len);
            b = 0;
        }
        else {
            a = 0;
            b = 0;
        }
    }
    else {
        size_t i = len;
        if (i > 48) [[unlikely]] {
            uint64_t see1 = seed;
            uint64_t see2 = seed;
            do
                [[likely]] {
                    seed = mix(r8(p) ^ secret[1], r8(p + 8) ^ seed);
                    see1 = mix(r8(p + 16) ^ secret[2], r8(p + 24) ^ see1);
                    see2 = mix(r8(p + 32) ^ secret[3], r8(p + 40) ^ see2);
                    p += 48;
                    i -= 48;
                }
            while (i > 48);
            seed ^= see1 ^ see2;
        }
        while (i > 16) [[unlikely]] {
            seed = mix(r8(p) ^ secret[1], r8(p + 8) ^ seed);
            i -= 16;
            p += 16;
        }
        a = r8(p + i - 16);
        b = r8(p + i - 8);
    }

    return mix(secret[1] ^ len, mix(a ^ secret[1], b ^ seed));
}

[[nodiscard]] static inline uint64_t hash(uint64_t x) {
    return mix(x, UINT64_C(0x9E3779B97F4A7C15));
}

} // namespace detail::hashing

template<typename T, typename Enable = void>
struct hash {
    uint64_t operator()(T const& obj) const
        noexcept(noexcept(std::declval<std::hash<T>>().operator()(std::declval<T const&>()))) {
        return std::hash<T>{}(obj);
    }
};

template<typename CharT>
struct hash<std::basic_string<CharT>> {
    using is_avalanching = void;
    uint64_t operator()(const std::basic_string<CharT>& str) const noexcept {
        return detail::hashing::hash(str.data(), sizeof(CharT) * str.size());
    }
};

template<typename CharT>
struct hash<std::basic_string_view<CharT>> {
    using is_avalanching = void;
    uint64_t operator()(const std::basic_string_view<CharT>& sv) const noexcept {
        return detail::hashing::hash(sv.data(), sizeof(CharT) * sv.size());
    }
};

template<typename T>
struct hash<T*> {
    using is_avalanching = void;
    uint64_t operator()(T* ptr) const noexcept {
        return detail::hashing::hash(reinterpret_cast<uintptr_t>(ptr));
    }
};

template<typename T>
struct hash<std::unique_ptr<T>> {
    using is_avalanching = void;
    uint64_t operator()(std::unique_ptr<T> const& ptr) const noexcept {
        return detail::hashing::hash(reinterpret_cast<uintptr_t>(ptr.get()));
    }
};

template<typename T>
struct hash<std::shared_ptr<T>> {
    using is_avalanching = void;
    uint64_t operator()(const std::shared_ptr<T>& ptr) const noexcept {
        return detail::hashing::hash(reinterpret_cast<uintptr_t>(ptr.get()));
    }
};

template<typename Enum>
    requires std::is_enum_v<Enum>
struct hash<Enum> {
    using is_avalanching = void;
    uint64_t operator()(Enum e) const noexcept {
        using underlying = typename std::underlying_type_t<Enum>;
        return detail::hashing::hash(static_cast<uint64_t>(static_cast<underlying>(e)));
    }
};

#define SLANG_HASH_STATICCAST(T)                                      \
    template<>                                                        \
    struct hash<T> {                                                  \
        using is_avalanching = void;                                  \
        uint64_t operator()(const T& obj) const noexcept {            \
            return detail::hashing::hash(static_cast<uint64_t>(obj)); \
        }                                                             \
    }

#if defined(__GNUC__) && !defined(__clang__)
#    pragma GCC diagnostic push
#    pragma GCC diagnostic ignored "-Wuseless-cast"
#endif
SLANG_HASH_STATICCAST(bool);
SLANG_HASH_STATICCAST(char);
SLANG_HASH_STATICCAST(signed char);
SLANG_HASH_STATICCAST(unsigned char);
SLANG_HASH_STATICCAST(char16_t);
SLANG_HASH_STATICCAST(char32_t);
SLANG_HASH_STATICCAST(wchar_t);
SLANG_HASH_STATICCAST(short);
SLANG_HASH_STATICCAST(unsigned short);
SLANG_HASH_STATICCAST(int);
SLANG_HASH_STATICCAST(unsigned int);
SLANG_HASH_STATICCAST(long);
SLANG_HASH_STATICCAST(long long);
SLANG_HASH_STATICCAST(unsigned long);
SLANG_HASH_STATICCAST(unsigned long long);
#undef SLANG_HASH_STATICCAST
#if defined(__GNUC__) && !defined(__clang__)
#    pragma GCC diagnostic pop
#endif

inline void hash_combine(size_t&) {
}

/// Hash combining function, based on the function from Boost.
/// It hashes the provided @a v object and combines it with the
/// previous hash value in @a seed.
template<typename T, typename... Rest>
inline void hash_combine(size_t& seed, const T& v, Rest... rest) {
    hash<T> hasher;
    seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    hash_combine(seed, rest...);
}

namespace detail::hashing {

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

template<typename T, size_t N, size_t Align = alignof(std::max_align_t)>
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

template<typename... TT>
struct hash<std::tuple<TT...>> {
    size_t operator()(const std::tuple<TT...>& tt) const {
        size_t seed = 0;
        detail::hashing::HashValueImpl<std::tuple<TT...>>::apply(seed, tt);
        return seed;
    }
};

template<typename K, typename V, typename H = hash<K>, typename E = std::equal_to<K>,
         typename A = std::allocator<std::pair<const K, V>>>
using flat_hash_map = boost::unordered_flat_map<K, V, H, E, A>;

template<typename T, typename H = hash<T>, typename E = std::equal_to<T>,
         typename A = std::allocator<T>>
using flat_hash_set = boost::unordered_flat_set<T, H, E, A>;

template<typename K, typename V, typename H = hash<K>, typename E = std::equal_to<K>,
         typename A = std::allocator<std::pair<const K, V>>>
using flat_node_map = boost::unordered_node_map<K, V, H, E, A>;

template<typename T, typename H = hash<T>, typename E = std::equal_to<T>,
         typename A = std::allocator<T>>
using flat_node_set = boost::unordered_node_set<T, H, E, A>;

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
