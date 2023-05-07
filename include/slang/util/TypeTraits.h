//------------------------------------------------------------------------------
//! @file TypeTraits.h
//! @brief Various type trait template helpers
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <type_traits>

namespace slang {

namespace detail {
template<class Default, class AlwaysVoid, template<class...> class Op, class... Args>
struct detector {
    using value_t = std::false_type;
    using type = Default;
};

template<class Default, template<class...> class Op, class... Args>
struct detector<Default, std::void_t<Op<Args...>>, Op, Args...> {
    using value_t = std::true_type;
    using type = Op<Args...>;
};

} // namespace detail

struct nonesuch {
    ~nonesuch() = delete;
    nonesuch(nonesuch const&) = delete;
    void operator=(nonesuch const&) = delete;
};

template<template<class...> class Op, class... Args>
using is_detected = typename detail::detector<nonesuch, void, Op, Args...>::value_t;

template<template<class...> class Op, class... Args>
using detected_t = typename detail::detector<nonesuch, void, Op, Args...>::type;

template<class Default, template<class...> class Op, class... Args>
using detected_or = detail::detector<Default, void, Op, Args...>;

template<template<class...> class Op, class... Args>
constexpr bool is_detected_v = is_detected<Op, Args...>::value;

template<typename TIter>
using IteratorCategory = typename std::iterator_traits<TIter>::iterator_category;

template<typename TIter, typename = void>
inline constexpr bool is_iterator_v = false;

template<typename TIter>
inline constexpr bool is_iterator_v<TIter, std::void_t<IteratorCategory<TIter>>> = true;

/// A simple implementation of a type index that can stand in for std::type_index
/// to allow building without RTTI enabled.
class SLANG_EXPORT type_index {
public:
    bool operator==(type_index t) const { return id == t.id; }
    bool operator!=(type_index t) const { return id != t.id; }
    bool operator<(type_index t) const { return std::less<int*>()(id, t.id); }
    bool operator<=(type_index t) const { return !(t > *this); }
    bool operator>(type_index t) const { return t < *this; }
    bool operator>=(type_index t) const { return !(*this < t); }

    size_t hash_code() const { return std::hash<int*>()(id); }

    template<typename T>
    static type_index of() {
        using t = std::remove_cv_t<std::remove_reference_t<T>>;
        return type_id_with_cvr<t>();
    }

private:
    int* id;
    type_index(int* id) : id(id) {}

    template<typename T>
    static type_index type_id_with_cvr() {
        static int id;
        return &id;
    }
};

} // namespace slang

namespace std {

template<>
struct hash<slang::type_index> {
    size_t operator()(slang::type_index t) const { return t.hash_code(); }
};

} // namespace std
