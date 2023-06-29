//------------------------------------------------------------------------------
//! @file Enum.h
//! @brief Various enum utilities
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <array>
#include <limits>

#include "slang/util/Util.h"

#define SLANG_UTIL_ENUM_ELEMENT(x) x,
#define SLANG_UTIL_ENUM_STRING(x) #x,

/// The SLANG_ENUM macro defines a strongly-typed enum with the given elements
/// along with a toString() method and an overload of operator<< for formatting.
#define SLANG_ENUM(name, elements) SLANG_ENUM_SIZED(name, int, elements)
#define SLANG_ENUM_SIZED(name, underlying, elements)                                            \
    enum class SLANG_EXPORT name : underlying { elements(SLANG_UTIL_ENUM_ELEMENT) };            \
    inline std::string_view toString(name e) {                                                  \
        static const char* strings[] = {elements(SLANG_UTIL_ENUM_STRING)};                      \
        return strings[static_cast<std::underlying_type_t<name>>(e)];                           \
    }                                                                                           \
    inline std::ostream& operator<<(std::ostream& os, name e) {                                 \
        return os << toString(e);                                                               \
    }                                                                                           \
    class name##_traits {                                                                       \
        enum e { elements(SLANG_UTIL_ENUM_ELEMENT) };                                           \
        static constexpr auto vals = {elements(SLANG_UTIL_ENUM_ELEMENT)};                       \
        static constexpr auto getValues() {                                                     \
            std::array<name, vals.size()> result{};                                             \
            for (size_t i = 0; i < vals.size(); i++)                                            \
                result[i] = name(i);                                                            \
            return result;                                                                      \
        }                                                                                       \
                                                                                                \
    public:                                                                                     \
        static const std::array<name, vals.size()> values;                                      \
    };                                                                                          \
    inline constexpr const std::array<name, name##_traits::vals.size()> name##_traits::values = \
        getValues();

#define SLANG_BITMASK_DEFINE_OPS(value_type)                                                     \
    inline constexpr slang::bitmask<value_type> operator&(value_type l, value_type r) noexcept { \
        return slang::bitmask<value_type>{l} & r;                                                \
    }                                                                                            \
    inline constexpr slang::bitmask<value_type> operator|(value_type l, value_type r) noexcept { \
        return slang::bitmask<value_type>{l} | r;                                                \
    }                                                                                            \
    inline constexpr slang::bitmask<value_type> operator^(value_type l, value_type r) noexcept { \
        return slang::bitmask<value_type>{l} ^ r;                                                \
    }                                                                                            \
    inline constexpr slang::bitmask<value_type> operator~(value_type op) noexcept {              \
        return ~slang::bitmask<value_type>{op};                                                  \
    }                                                                                            \
    inline constexpr slang::bitmask<value_type>::underlying_type bits(value_type op) noexcept {  \
        return slang::bitmask<value_type>{op}.bits();                                            \
    }

#define SLANG_BITMASK_DEFINE_MAX_ELEMENT(value_type, max_element)                            \
    inline constexpr slang::bitmask_detail::underlying_type_t<value_type> get_enum_mask(     \
        value_type) noexcept {                                                               \
        return slang::bitmask_detail::mask_from_max_element<value_type,                      \
                                                            value_type::max_element>::value; \
    }

/// The SLANG_BITMASK macro defines convenience operators for a bitmask type.
/// This is to work around strongly typed enums not being combinable by
/// operators like | and & in C++.
#define SLANG_BITMASK(value_type, max_element)                \
    SLANG_BITMASK_DEFINE_MAX_ELEMENT(value_type, max_element) \
    SLANG_BITMASK_DEFINE_OPS(value_type)

namespace slang {

namespace bitmask_detail {

template<class T>
struct underlying_type {
    static_assert(std::is_enum<T>::value, "T is not a enum type");
    using type = typename std::make_unsigned<typename std::underlying_type<T>::type>::type;
};

template<class T>
using underlying_type_t = typename underlying_type<T>::type;

template<class T, T MaxElement = T::_bitmask_max_element>
struct mask_from_max_element {
    static constexpr underlying_type_t<T> max_element_value_ = static_cast<underlying_type_t<T>>(
        MaxElement);

    static_assert(max_element_value_ >= 0, "Max element is negative");

    // If you really have to define a bitmask that uses the highest bit of signed type (i.e. the
    // sign bit) then define the value mask rather than the max element.
    static_assert(max_element_value_ <=
                      (std::numeric_limits<typename std::underlying_type<T>::type>::max() >> 1) + 1,
                  "Max element is greater than the underlying type's highest bit");

    // `((value - 1) << 1) + 1` is used rather that simpler `(value << 1) - 1`
    // because latter overflows in case if `value` is the highest bit of the underlying type.
    static constexpr underlying_type_t<T> value = max_element_value_
                                                      ? ((max_element_value_ - 1) << 1) + 1
                                                      : 0;
};

template<class T>
struct enum_mask : std::integral_constant<underlying_type_t<T>, mask_from_max_element<T>::value> {};

} // namespace bitmask_detail

template<class T>
inline constexpr bitmask_detail::underlying_type_t<T> get_enum_mask(const T&) noexcept {
    return bitmask_detail::enum_mask<T>::value;
}

/// A convenience wrapper around an enum that is intended to be used as a combination
/// of bitwise-combined flags. Built-in strongly-typed C++ enums are not otherwise
/// combinable via operators like | and &.
template<typename T>
class bitmask {
public:
    using underlying_type = bitmask_detail::underlying_type_t<T>;

    static constexpr underlying_type mask_value = get_enum_mask(static_cast<T>(0));

    constexpr bitmask() noexcept = default;
    constexpr bitmask(T value) noexcept : m_bits{static_cast<underlying_type>(value)} {}

    /// Returns true iff (*this & r) != 0.
    constexpr bool has(const bitmask& r) const noexcept { return (*this & r) != 0; }

    /// @return the underlying integer value containing the combined flags.
    constexpr underlying_type bits() const noexcept { return m_bits; }

    /// @return true if any flags at all are set (non-zero), otherwise false.
    constexpr explicit operator bool() const noexcept { return bits() ? true : false; }

    bool operator==(const bitmask<T>& r) const { return bits() == r.bits(); }
    bool operator==(T r) const { return bits() == static_cast<underlying_type>(r); }
    bool operator==(underlying_type r) const { return bits() == r; }

    constexpr bitmask operator~() const noexcept {
        return bitmask{std::true_type{}, ~m_bits & mask_value};
    }

    constexpr bitmask operator&(const bitmask& r) const noexcept {
        return bitmask{std::true_type{}, m_bits & r.m_bits};
    }

    constexpr bitmask operator|(const bitmask& r) const noexcept {
        return bitmask{std::true_type{}, m_bits | r.m_bits};
    }

    constexpr bitmask operator^(const bitmask& r) const noexcept {
        return bitmask{std::true_type{}, m_bits ^ r.m_bits};
    }

    bitmask& operator|=(const bitmask& r) noexcept {
        m_bits |= r.m_bits;
        return *this;
    }

    bitmask& operator&=(const bitmask& r) noexcept {
        m_bits &= r.m_bits;
        return *this;
    }

    bitmask& operator^=(const bitmask& r) noexcept {
        m_bits ^= r.m_bits;
        return *this;
    }

private:
    template<class U>
    constexpr bitmask(std::true_type, U bits) noexcept :
        m_bits(static_cast<underlying_type>(bits)) {}

    underlying_type m_bits = 0;
};

template<class T>
inline constexpr bitmask<T> operator&(T l, const bitmask<T>& r) noexcept {
    return r & l;
}

template<class T>
inline constexpr bitmask<T> operator|(T l, const bitmask<T>& r) noexcept {
    return r | l;
}

template<class T>
inline constexpr bitmask<T> operator^(T l, const bitmask<T>& r) noexcept {
    return r ^ l;
}

} // namespace slang
