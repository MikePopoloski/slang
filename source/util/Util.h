//------------------------------------------------------------------------------
// Util.h
// Various utility functions and basic types used throughout the library.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <cstddef>                      // for std::byte
#include <cstdint>                      // for sized integer types
#include <climits>                      // for type size macros
#include <new>                          // for placement new
#include <optional>                     // for std::optional
#include <string_view>                  // for std::string_view
#include <utility>                      // for many random utility functions

using std::byte;
using std::int8_t;
using std::int16_t;
using std::int32_t;
using std::int64_t;
using std::intptr_t;
using std::nullptr_t;
using std::optional;
using std::ptrdiff_t;
using std::size_t;
using std::string_view;
using std::uint8_t;
using std::uint16_t;
using std::uint32_t;
using std::uint64_t;
using std::uintptr_t;

// Clang 5.0 and 6.0 fails to compile <variant> from libstdc++
#ifdef __clang__
  #include "compat/variant.h"
  namespace std {
  using mpark::variant;
  using mpark::monostate;
  using mpark::get;
  using mpark::get_if;
  using mpark::visit;
}
#else
  #include <variant>
#endif

#if !defined(ASSERT_ENABLED)
  #if !defined(NDEBUG)
    #define ASSERT_ENABLED 1
  #endif
#endif

#if ASSERT_ENABLED
  #if defined(__GNUC__) || defined(__clang__)
    #define ASSERT_FUNCTION __PRETTY_FUNCTION__
  #elif defined(_MSC_VER)
    #define ASSERT_FUNCTION __FUNCSIG__
  #elif defined(__SUNPRO_CC)
    #define ASSERT_FUNCTION __func__
  #else
    #define ASSERT_FUNCTION __FUNCTION__
  #endif

  #define ASSERT(cond) \
    do { \
        if (!(cond)) slang::assert::assertFailed(#cond, __FILE__, __LINE__, ASSERT_FUNCTION); \
    } while (false)

#else
  #define ASSERT(cond) do { (void)sizeof(cond); } while (false)
#endif

#define THROW_UNREACHABLE \
  throw std::logic_error(std::string(__FILE__) + ":" + std::to_string(__LINE__) + \
                         ": " + "Default case should be unreachable!")

#include "gsl/gsl"

using gsl::span;
using gsl::make_span;
using gsl::not_null;

// Compiler-specific macros for warnings and suppressions
#ifdef __clang__
  #define NO_SANITIZE(warningName)  __attribute__((no_sanitize(warningName)))
#else
  #define NO_SANITIZE(warningName)
#endif

#include "bitmask.hpp"
using bitmask_lib::bitmask;

namespace slang {

/// Converts a span of characters into a string_view.
inline string_view to_string_view(span<char> text) {
    return string_view(text.data(), (size_t)text.size());
}

inline void hash_combine(size_t&) {}

/// Hash combining function, based on the function from Boost.
template<typename T, typename... Rest>
inline void hash_combine(size_t& seed, const T& v, Rest... rest) {
    std::hash<T> hasher;
    seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    hash_combine(seed, rest...);
}

namespace assert {

class AssertionException : public std::logic_error {
public:
    AssertionException(const std::string& message) : std::logic_error(message) {}
};

[[noreturn]] void assertFailed(const char* expr, const char* file, int line, const char* func);

}

}

namespace detail {

template<typename Tuple, size_t Index = std::tuple_size<Tuple>::value - 1>
struct HashValueImpl {
    static void apply(size_t& seed, const Tuple& tuple) {
        HashValueImpl<Tuple, Index - 1>::apply(seed, tuple);
        slang::hash_combine(seed, std::get<Index>(tuple));
    }
};

template<typename Tuple>
struct HashValueImpl<Tuple, 0> {
    static void apply(size_t& seed, const Tuple& tuple) {
        slang::hash_combine(seed, std::get<0>(tuple));
    }
};

}

namespace std {

template<typename... TT>
struct hash<std::tuple<TT...>> {
    size_t operator()(const std::tuple<TT...>& tt) const {
        size_t seed = 0;
        ::detail::HashValueImpl<std::tuple<TT...>>::apply(seed, tt);
        return seed;
    }
};

}
