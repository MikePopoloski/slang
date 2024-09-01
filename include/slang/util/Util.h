//------------------------------------------------------------------------------
//! @file Util.h
//! @brief Various utility functions and basic types used throughout the library
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <cstddef>
#include <cstdint>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <utility>

#include "slang/slang_export.h"
#include "slang/util/Enum.h"

#if __cpp_exceptions
#    define SLANG_TRY try
#    define SLANG_CATCH(X) catch (X)
#    define SLANG_THROW(e) throw(e)
#else
#    define SLANG_TRY if (true)
#    define SLANG_CATCH(X) if (false)
#    define SLANG_THROW(e) slang::assert::handleThrow((e).what(), std::source_location::current())
#endif

#if defined(__clang__)
#    if __has_feature(cxx_rtti)
#        define SLANG_RTTI_ENABLED
#    endif
#elif defined(__GNUG__)
#    if defined(__GXX_RTTI)
#        define SLANG_RTTI_ENABLED
#    endif
#elif defined(_MSC_VER)
#    if defined(_CPPRTTI)
#        define SLANG_RTTI_ENABLED
#    endif
#else
#    define SLANG_RTTI_ENABLED
#endif

// Note: typeid() appears to be broken under libc++ arm64,
// which is why we use our workaround type for that as well.
#if defined(SLANG_RTTI_ENABLED) && !defined(__ARM_ARCH_ISA_A64)
#    define SLANG_TYPEOF(x) std::type_index(typeid(x))
#    define SLANG_TYPEINDEX std::type_index
#else
#    define SLANG_TYPEOF(x) type_index::of<x>()
#    define SLANG_TYPEINDEX type_index
#endif

#if !defined(SLANG_ASSERT_ENABLED)
#    if !defined(NDEBUG)
#        define SLANG_ASSERT_ENABLED 1
#    endif
#endif

#if SLANG_ASSERT_ENABLED
#    define SLANG_ASSERT(cond)                                                       \
        do {                                                                         \
            if (!(cond))                                                             \
                slang::assert::assertFailed(#cond, std::source_location::current()); \
        } while (false)

#    define SLANG_UNREACHABLE slang::assert::handleUnreachable(std::source_location::current())
#else
#    define SLANG_ASSERT(cond)  \
        do {                    \
            (void)sizeof(cond); \
        } while (false)

#    if defined(__GNUC__) || defined(__clang__)
#        define SLANG_UNREACHABLE __builtin_unreachable()
#    elif defined(_MSC_VER)
#        define SLANG_UNREACHABLE __assume(false)
#    else
#        define SLANG_UNREACHABLE
#    endif

#endif

// Compiler-specific macros for warnings and suppressions
#ifdef __clang__
#    define SLANG_NO_SANITIZE(warningName) __attribute__((no_sanitize(warningName)))
#else
#    define SLANG_NO_SANITIZE(warningName)
#endif

using namespace std::literals;

namespace slang {

using byte = std::byte;
using int16_t = std::int16_t;
using int32_t = std::int32_t;
using int64_t = std::int64_t;
using int8_t = std::int8_t;
using intptr_t = std::intptr_t;
using nullptr_t = std::nullptr_t;
using ptrdiff_t = std::ptrdiff_t;
using size_t = std::size_t;
using uint16_t = std::uint16_t;
using uint32_t = std::uint32_t;
using uint64_t = std::uint64_t;
using uint8_t = std::uint8_t;
using uintptr_t = std::uintptr_t;

namespace assert {

/// An exception thrown when an ASSERT condition fails.
class SLANG_EXPORT AssertionException : public std::logic_error {
public:
    AssertionException(const std::string& message) : std::logic_error(message) {}
};

/// A handler that runs when an ASSERT condition fails; it will unconditionally
/// throw an exception.
[[noreturn]] SLANG_EXPORT void assertFailed(const char* expr, const std::source_location& location);

/// A handler that runs when an exception is thrown but exceptions are disabled; it will
/// unconditionally abort the program.
[[noreturn]] SLANG_EXPORT void handleThrow(const char* msg, const std::source_location& location);

/// A handler that runs when a code path is reached that is supposed to be unreachable.
/// An exception will be thrown or the program will be aborted.
[[noreturn]] SLANG_EXPORT void handleUnreachable(const std::source_location& location);
} // namespace assert

/// A wrapper around a pointer that indicates that it should never be null.
/// It deletes some operators and assignments from null, but it can only enforce at
/// runtime, via asserts, that the value is not actually null.
///
/// The real value of this type is in documenting in the API the intentions of the pointer,
/// so that consumers don't need to add explicit null checks.
template<typename T>
class not_null {
public:
    static_assert(std::is_assignable<T&, std::nullptr_t>::value, "T cannot be assigned nullptr.");

    template<std::convertible_to<T> U>
    constexpr not_null(U&& u) : ptr(std::forward<U>(u)) {
        SLANG_ASSERT(ptr);
    }

    template<std::convertible_to<T> U>
    constexpr not_null(const not_null<U>& other) : not_null(other.get()) {}

    not_null(not_null&& other) noexcept = default;
    not_null(const not_null& other) = default;
    not_null& operator=(const not_null& other) = default;

    // prevents compilation when someone attempts to assign a null pointer constant
    not_null(std::nullptr_t) = delete;
    not_null& operator=(std::nullptr_t) = delete;

    constexpr T get() const {
        SLANG_ASSERT(ptr);
        return ptr;
    }

    constexpr operator T() const { return get(); }
    constexpr T operator->() const { return get(); }
    constexpr decltype(auto) operator*() const { return *get(); }

    template<typename U>
    bool operator==(const not_null<U>& rhs) const {
        return get() == rhs.get();
    }

    template<typename U>
    auto operator<=>(const not_null<U>& rhs) const {
        return get() <=> rhs.get();
    }

    // unwanted operators... pointers only point to single objects!
    not_null& operator++() = delete;
    not_null& operator--() = delete;
    not_null operator++(int) = delete;
    not_null operator--(int) = delete;
    not_null& operator+=(std::ptrdiff_t) = delete;
    not_null& operator-=(std::ptrdiff_t) = delete;
    void operator[](std::ptrdiff_t) const = delete;

private:
    T ptr;
};

template<typename T>
std::ostream& operator<<(std::ostream& os, const not_null<T>& val) {
    os << val.get();
    return os;
}

// more unwanted operators
template<typename T, typename U>
std::ptrdiff_t operator-(const not_null<T>&, const not_null<U>&) = delete;
template<class T>
not_null<T> operator-(const not_null<T>&, std::ptrdiff_t) = delete;
template<class T>
not_null<T> operator+(const not_null<T>&, std::ptrdiff_t) = delete;
template<class T>
not_null<T> operator+(std::ptrdiff_t, const not_null<T>&) = delete;

} // namespace slang

namespace std {

template<typename T>
struct hash<slang::not_null<T>> {
    std::size_t operator()(const slang::not_null<T>& value) const { return hash<T>{}(value); }
};

} // namespace std
