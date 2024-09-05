//------------------------------------------------------------------------------
//! @file Iterator.h
//! @brief Helper classes for working with iterators
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <concepts>
#include <iterator>
#include <type_traits>

namespace slang {

// Implementation is based on the blog post here:
// https://vector-of-bool.github.io/2020/06/13/cpp20-iter-facade.html
namespace detail {

template<typename T>
struct arrow_proxy {
    T object;

    constexpr T* operator->() noexcept { return &object; }
    constexpr const T* operator->() const noexcept { return &object; }

    constexpr T& operator*() noexcept { return object; }
    constexpr const T& operator*() const noexcept { return object; }

    constexpr operator T*() noexcept { return &object; }
    constexpr operator T const*() const noexcept { return &object; }
};

template<typename T>
struct inferred_value_type {
    using type = std::remove_cvref_t<decltype(*std::declval<T&>())>;
};
template<typename T>
    requires requires { typename T::value_type; }
struct inferred_value_type<T> {
    using type = typename T::value_type;
};
template<typename T>
using inferred_value_type_t = typename inferred_value_type<T>::type;

template<typename T>
concept has_increment = requires(T& it) { it.increment(); };
template<typename T>
concept has_nothrow_increment = requires(T& it) {
    { it.increment() } noexcept;
};

template<typename T>
concept has_decrement = requires(T& it) { it.decrement(); };
template<typename T>
concept has_nothrow_decrement = requires(T& it) {
    { it.decrement() } noexcept;
};

template<typename T, typename It = T>
concept has_distance_to = requires(const It& it, const T& other) { it.distance_to(other); };
template<typename T, typename It = T>
concept has_nothrow_distance_to = requires(const It& it, const T& other) {
    { it.distance_to(other) } noexcept;
};

template<typename>
struct inferred_difference_type {
    using type = std::ptrdiff_t;
};
template<has_distance_to T>
struct inferred_difference_type<T> {
    static const T& it;
    using type = decltype(it.distance_to(it));
};
template<typename T>
using inferred_difference_type_t = typename inferred_difference_type<T>::type;

template<typename T, typename Diff = inferred_difference_type_t<T>>
concept has_advance = requires(T& it, Diff offset) { it.advance(offset); };
template<typename T, typename Diff = inferred_difference_type_t<T>>
concept has_nothrow_advance = requires(T& it, Diff offset) {
    { it.advance(offset) } noexcept;
};

template<typename T, typename It = T>
concept equality_comparable = requires(const T& sentinel, const It& it) {
    { it.equals(sentinel) } -> std::convertible_to<bool>;
};
template<typename T, typename It = T>
concept nothrow_equality_comparable = requires(const T& sentinel, const It& it) {
    { it.equals(sentinel) } noexcept -> std::convertible_to<bool>;
};

template<typename T>
concept has_nothrow_dereference = requires(const T& it) {
    { it.dereference() } noexcept;
};
template<typename T>
concept lvalue_reference = std::is_lvalue_reference_v<T>;
template<typename T>
concept dereferences_lvalue = requires(const T& it) {
    { it.dereference() } -> lvalue_reference;
};

// We can meet "random access" if it provides
// both .advance() and .distance_to()
template<typename T>
concept meets_random_access = has_advance<T> && has_distance_to<T>;

// We meet `bidirectional` if we are random_access, OR we have .decrement()
template<typename T>
concept meets_bidirectional = meets_random_access<T> || has_decrement<T>;

template<typename T>
concept decls_contiguous = requires {
    { T::contiguous_iterator } -> std::convertible_to<bool>;
} && T::contiguous_iterator;

template<typename Arg, typename Iter>
concept difference_type_arg = std::convertible_to<Arg, inferred_difference_type_t<Iter>>;

template<typename Arg, typename Iter>
concept advance_type_arg = difference_type_arg<Arg, Iter> && has_advance<Iter, Arg>;

template<typename T>
concept incrementable = has_increment<T> || has_advance<T> || requires(T& it) {
    { ++it } -> std::common_reference_with<std::remove_cvref_t<T>>;
};

template<typename Iter>
using iterator_category_t =
    std::conditional_t<meets_random_access<Iter>,
                       // We meet the requirements of random-access:
                       std::random_access_iterator_tag,
                       // We don't:
                       std::conditional_t<meets_bidirectional<Iter>,
                                          // We meet requirements for bidirectional usage:
                                          std::bidirectional_iterator_tag,
                                          // We don't:
                                          std::conditional_t<equality_comparable<Iter>,
                                                             // equality equality_comparable
                                                             // satisfies forward iterator
                                                             std::forward_iterator_tag,
                                                             // Otherwise we are an input iterator:
                                                             std::input_iterator_tag>>>;

// contiguous_iterator is a special case of random_access and output iterator is deduced by STL
template<typename T>
concept satisfies_contiguous = meets_random_access<T> && decls_contiguous<T> &&
                               dereferences_lvalue<T>;

template<typename Iter>
using iterator_concept_t =
    std::conditional_t<satisfies_contiguous<Iter>, std::contiguous_iterator_tag,
                       iterator_category_t<Iter>>;

template<typename T>
constexpr T& arrow_helper(T& t) noexcept {
    return t;
}
template<typename T>
    requires(!std::is_lvalue_reference_v<T>)
constexpr arrow_proxy<std::remove_cvref_t<T>> arrow_helper(T&& t) noexcept(
    std::is_nothrow_move_constructible_v<std::remove_cvref_t<T>>) {
    return {std::move(t)};
}

} // namespace detail

/// @brief Iterator facade which infers iterator types and functionality
/// @tparam Derived iterator subclass type which implements: <br>
///
///    Input iterator (required): <br>
///    *   <code>reference dereference() const </code> <br>
///    *   <code>void increment() </code> <br>
///
///    Forward: <br>
///    *   <code>bool equals(T|sentinel) const </code> <br>
///
///    Bidirectional: <br>
///    *   <code>void decrement() </code> <br>
///
///    Random access: <br>
///    *   <code>difference_type distance_to(T|sized_sentinel) const </code>
///         (can replace equal) <br>
///    *   <code>void advance(difference_type) </code>
///         (can replace increment/decrement) <br>
///
/// @tparam Contiguous true if the derived iterator is contiguous,
///         otherwise false (since it cannot be inferred).
///
template<typename Derived, bool Contiguous = false>
class iterator_facade {
public:
    using self_type = Derived;

    constexpr static bool contiguous_iterator = Contiguous;

private:
    // cannot add any type aliases as Derived is incomplete at this point, can only rely on
    // decltype(auto) in declarations
    friend Derived;

    [[nodiscard]] constexpr self_type& self() noexcept { return static_cast<self_type&>(*this); }
    [[nodiscard]] constexpr const self_type& self() const noexcept {
        return static_cast<const self_type&>(*this);
    }

public:
    /// @brief Dereference operator
    /// @return decltype(Derived{}.dereference())
    constexpr decltype(auto) operator*() const
        noexcept(detail::has_nothrow_dereference<self_type>) {
        return self().dereference();
    }

    /// @brief Arrow operator
    /// @return Pointer or arrow proxy to the return value of
    /// <code>Derived::dereference() const</code>
    constexpr decltype(auto) operator->() const
        noexcept((detail::has_nothrow_dereference<self_type> &&
                  noexcept(detail::arrow_helper(**this)))) {
        if constexpr (detail::dereferences_lvalue<self_type>) {
            return std::addressof(**this);
        }
        else {
            return detail::arrow_helper(**this);
        }
    }

    /// @brief Equality comparison operator, the default overload which requires
    /// <code>Derived::equals(T) const</code>
    template<detail::equality_comparable<self_type> T>
    [[nodiscard]] constexpr bool friend operator==(const self_type& lhs, const T& rhs) noexcept(
        detail::nothrow_equality_comparable<T, self_type>) {
        return lhs.equals(rhs);
    }

    /// @brief Fallback equality comparison operator when <code>Derived::equals(T) const</code> is
    /// not available, but <code>Derived::distance_to(T) const</code> is.
    template<detail::has_distance_to<self_type> T>
        requires(!detail::equality_comparable<T, self_type>)
    [[nodiscard]] constexpr bool friend operator==(const self_type& lhs, const T& rhs) noexcept(
        detail::has_nothrow_distance_to<T, self_type>) {
        return lhs.distance_to(rhs) == 0;
    }

    /// @brief Default pre-increment operator, requires <code>Derived::increment()</code>
    template<typename T = self_type>
        requires(detail::has_increment<T>)
    constexpr self_type& operator++() noexcept(detail::has_nothrow_increment<self_type>) {
        self().increment();
        return self();
    }

    /// @brief Fallback pre-increment operator when <code>Derived::increment()</code> is not
    /// available, requires <code>Derived::advance(1)</code> to be valid
    template<typename T = self_type>
        requires(!detail::has_increment<T> && detail::has_advance<T, int>)
    constexpr self_type& operator++() noexcept(detail::has_nothrow_advance<self_type, int>) {
        self().advance(1);
        return self();
    }

    /// @brief Post-increment operator, requires <code>Derived::increment()</code> or
    /// <code>Derived::advance(1)</code>
    template<typename T = self_type>
        requires(detail::has_increment<T> || detail::has_advance<T, int>)
    constexpr self_type operator++(int) noexcept(std::is_nothrow_copy_constructible_v<self_type> &&
                                                 noexcept(++(*this))) {
        auto copy = self();
        ++(*this);
        return copy;
    }

    /// @brief Default pre-decrement operator, requires <code>Derived::decrement()</code>
    template<typename T = self_type>
        requires(detail::has_decrement<T>)
    constexpr self_type& operator--() noexcept(detail::has_nothrow_decrement<self_type>) {
        self().decrement();
        return self();
    }

    /// @brief Fallback pre-decrement operator when <code>Derived::decrement()</code> is not
    /// available, requires <code>Derived::advance(-1)</code> to be valid
    template<typename T = self_type>
        requires(!detail::has_decrement<T> && detail::has_advance<T, int>)
    constexpr self_type& operator--() noexcept(detail::has_nothrow_advance<self_type, int>) {
        self().advance(-1);
        return self();
    }

    /// @brief Post-decrement operator, requires <code>Derived::decrement()</code> or
    /// <code>Derived::advance(-1)</code>
    template<typename T = self_type>
        requires(detail::has_decrement<T> || detail::has_advance<T, int>)
    constexpr self_type operator--(int) noexcept(std::is_nothrow_copy_constructible_v<self_type> &&
                                                 noexcept(--(*this))) {
        auto copy = self();
        ++(*this);
        return copy;
    }

    /// @brief operator+=, requires <code>Derived::advance()</code>
    template<detail::advance_type_arg<self_type> D>
    friend constexpr self_type& operator+=(self_type& self, D offset) noexcept(
        detail::has_nothrow_advance<self_type, D>) {
        self.advance(offset);
        return self;
    }

    /// @brief operator+, requires <code>Derived::advance()</code>
    template<detail::advance_type_arg<self_type> D>
    [[nodiscard]] friend constexpr self_type operator+(self_type left, D off) noexcept(
        detail::has_nothrow_advance<self_type, D>) {
        return left += off;
    }

    /// @brief operator+, requires <code>Derived::advance()</code>
    template<detail::advance_type_arg<self_type> D>
    [[nodiscard]] friend constexpr auto operator+(D off, self_type right) noexcept(
        detail::has_nothrow_advance<self_type, D>) -> self_type {
        return right += off;
    }

    /// @brief operator-, requires <code>Derived::advance()</code>
    template<detail::advance_type_arg<self_type> D>
    [[nodiscard]] friend constexpr self_type operator-(self_type left, D off) noexcept(
        detail::has_nothrow_advance<self_type, D>) {
        return left + -off;
    }

    /// @brief operator-=, requires <code>Derived::advance()</code>
    template<detail::advance_type_arg<self_type> D>
    friend constexpr self_type& operator-=(self_type& left, D off) noexcept(
        detail::has_nothrow_advance<self_type, D>) {
        return left = left - off;
    }

    /// @brief Random access operator, requires <code>Derived::advance()</code>
    template<typename T = self_type, detail::advance_type_arg<T> D>
    [[nodiscard]] constexpr decltype(auto) operator[](D off) const
        noexcept(detail::has_nothrow_advance<self_type, D> &&
                 detail::has_nothrow_dereference<self_type>) {
        return (self() + off).dereference();
    }

    /// @brief Distance between two iterators or iterator and sentinel pair,
    /// requires <code>Derived::distance_to()</code>
    template<detail::has_distance_to<self_type> T>
    [[nodiscard]] friend constexpr decltype(auto) operator-(
        const T& left,
        const self_type& right) noexcept(detail::has_nothrow_distance_to<T, self_type>) {
        return right.distance_to(left);
    }

    /// @brief Distance between an iterator and a sentinel,
    /// requires <code>Derived::distance_to()</code>
    template<detail::has_distance_to<self_type> Sentinel>
    [[nodiscard]] friend constexpr decltype(auto) operator-(
        const self_type& left,
        const Sentinel& right) noexcept(detail::has_nothrow_distance_to<Sentinel, self_type>) {
        return -(right - left);
    }

    /// @brief Three way comparison operator, requires <code>Derived::distance_to()</code>
    template<detail::has_distance_to<self_type> Sentinel>
    [[nodiscard]] friend constexpr auto operator<=>(
        const self_type& left,
        const Sentinel& right) noexcept(detail::has_nothrow_distance_to<Sentinel, self_type>) {
        return -left.distance_to(right) <=> 0;
    }
};

namespace detail {

template<typename Derived>
class is_base_of_facade {
private:
    template<typename T, bool B>
    static std::true_type derives(const iterator_facade<T, B>&);
    static std::false_type derives(...);

public:
    constexpr static bool value = decltype(derives(std::declval<Derived>()))::value;
};

template<typename T>
concept iterator_facade_subclass = is_base_of_facade<T>::value;

template<typename NewFirst, typename T>
struct replace_first_param {
    using type = T;
};

template<typename NewFirst, template<typename, typename...> typename T, typename First,
         typename... Rest>
struct replace_first_param<NewFirst, T<First, Rest...>> {
    using type = T<NewFirst, Rest...>;
};

template<typename T, typename Other, typename = void>
struct rebind_alias {
    using type = typename replace_first_param<Other, T>::type;
};

template<typename T, typename Other>
struct rebind_alias<T, Other, std::void_t<typename T::template rebind<Other>>> {
    using type = typename T::template rebind<Other>;
};

} // namespace detail

} // namespace slang

template<slang::detail::iterator_facade_subclass Iter>
struct std::iterator_traits<Iter> {
    using reference = decltype(*std::declval<Iter&>());
    using pointer = decltype(std::declval<Iter&>().operator->());
    using difference_type = slang ::detail::inferred_difference_type_t<Iter>;
    using value_type = slang ::detail::inferred_value_type_t<Iter>;

    using iterator_category = slang ::detail::iterator_category_t<Iter>;
    using iterator_concept = slang ::detail::iterator_concept_t<Iter>;
};

// specialization for contiguous iterators since the standard implementation
// causes a compile error if Iter is not a template
template<slang::detail::iterator_facade_subclass Iter>
    requires(slang::detail::satisfies_contiguous<Iter>)
struct std::pointer_traits<Iter> {
    using pointer = Iter;
    using element_type = std::iter_value_t<Iter>;
    using difference_type = std::iter_difference_t<Iter>;

    template<typename Other>
    using rebind = typename slang::detail::rebind_alias<Iter, Other>::type;

    using reference = std::conditional_t<std::is_void_v<element_type>, char, element_type>&;

    static pointer pointer_to(reference value) noexcept(noexcept(Iter::pointer_to(value))) {
        return Iter::pointer_to(value);
    }
};
