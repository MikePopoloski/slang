//------------------------------------------------------------------------------
//! @file TypeTraits.h
//! @brief Various type trait template helpers
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <type_traits>

#include "slang/util/Util.h"

namespace slang {

/// Returns the demangled name of the template argument's C++ type.
template<typename T>
constexpr std::string_view typeName();

template<>
constexpr std::string_view typeName<void>() {
    return "void";
}

namespace detail {

template<typename T>
constexpr std::string_view wrappedTypeName() {
    return SLANG_ASSERT_FUNCTION;
}

constexpr std::size_t wrappedTypeNamePrefixLength() {
    return wrappedTypeName<void>().find(typeName<void>());
}

constexpr std::size_t wrappedTypeNameSuffixLength() {
    return wrappedTypeName<void>().length() - wrappedTypeNamePrefixLength() -
           typeName<void>().length();
}

} // namespace detail

template<typename T>
constexpr std::string_view typeName() {
    // https://stackoverflow.com/questions/81870/is-it-possible-to-print-a-variables-type-in-standard-c/64490578#64490578
    auto name = detail::wrappedTypeName<T>();
    auto prefixLength = detail::wrappedTypeNamePrefixLength();
    auto suffixLength = detail::wrappedTypeNameSuffixLength();
    return name.substr(prefixLength, name.length() - prefixLength - suffixLength);
}

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
