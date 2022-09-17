//------------------------------------------------------------------------------
//! @file NotNull.h
//! @brief Contains the not_null pointer utility class
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Assert.h"

namespace slang {

/// A wrapper around a pointer that indicates that it should never be null.
/// It deletes some operators and assignments from null, but it can only enforce at
/// runtime, via asserts, that the value is not actually null.
///
/// The real value of this type is in documenting in the API the intentions of the pointer,
/// so that consumers don't need to add explicit null checks.
template<typename T>
class SLANG_EXPORT not_null {
public:
    static_assert(std::is_assignable<T&, std::nullptr_t>::value, "T cannot be assigned nullptr.");

    template<typename U, typename = std::enable_if_t<std::is_convertible<U, T>::value>>
    constexpr not_null(U&& u) : ptr(std::forward<U>(u)) {
        ASSERT(ptr);
    }

    template<typename U, typename = std::enable_if_t<std::is_convertible<U, T>::value>>
    constexpr not_null(const not_null<U>& other) : not_null(other.get()) {}

    not_null(not_null&& other) noexcept = default;
    not_null(const not_null& other) = default;
    not_null& operator=(const not_null& other) = default;

    constexpr T get() const {
        ASSERT(ptr);
        return ptr;
    }

    constexpr operator T() const { return get(); }
    constexpr T operator->() const { return get(); }
    constexpr decltype(auto) operator*() const { return *get(); }

    // prevents compilation when someone attempts to assign a null pointer constant
    not_null(std::nullptr_t) = delete;
    not_null& operator=(std::nullptr_t) = delete;

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

template<typename T, typename U>
auto operator==(const not_null<T>& lhs, const not_null<U>& rhs)
    -> decltype(lhs.get() == rhs.get()) {
    return lhs.get() == rhs.get();
}

template<typename T, typename U>
auto operator!=(const not_null<T>& lhs, const not_null<U>& rhs)
    -> decltype(lhs.get() != rhs.get()) {
    return lhs.get() != rhs.get();
}

template<typename T, typename U>
auto operator<(const not_null<T>& lhs, const not_null<U>& rhs) -> decltype(lhs.get() < rhs.get()) {
    return lhs.get() < rhs.get();
}

template<typename T, typename U>
auto operator<=(const not_null<T>& lhs, const not_null<U>& rhs)
    -> decltype(lhs.get() <= rhs.get()) {
    return lhs.get() <= rhs.get();
}

template<typename T, typename U>
auto operator>(const not_null<T>& lhs, const not_null<U>& rhs) -> decltype(lhs.get() > rhs.get()) {
    return lhs.get() > rhs.get();
}

template<typename T, typename U>
auto operator>=(const not_null<T>& lhs, const not_null<U>& rhs)
    -> decltype(lhs.get() >= rhs.get()) {
    return lhs.get() >= rhs.get();
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
