//------------------------------------------------------------------------------
//! @file TypePrinter.h
//! @brief Utility function that let's you print the type of a variable
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

// Courtesy of:
// https://stackoverflow.com/questions/81870/is-it-possible-to-print-a-variables-type-in-standard-c/64490578#64490578

#include <string_view>

namespace slang {

/// Allows you to print the demangled name of a C++ type.
template<typename T>
constexpr std::string_view typeName();

template<>
constexpr std::string_view typeName<void>() {
    return "void";
}

namespace type_printer_inner {

using type_name_prober = void;

template<typename T>
constexpr std::string_view wrappedTypeName() {
#ifdef __clang__
    return __PRETTY_FUNCTION__;
#elif defined(__GNUC__)
    return __PRETTY_FUNCTION__;
#elif defined(_MSC_VER)
    return __FUNCSIG__;
#else
#    error "Unsupported compiler"
#endif
}

constexpr std::size_t wrappedTypeNamePrefixLength() {
    return wrappedTypeName<type_name_prober>().find(typeName<type_name_prober>());
}

constexpr std::size_t wrappedTypeNameSuffixLength() {
    return wrappedTypeName<type_name_prober>().length() - wrappedTypeNamePrefixLength() -
           typeName<type_name_prober>().length();
}

} // namespace type_printer_inner

template<typename T>
constexpr std::string_view typeName() {
    constexpr auto wrapped_name = type_printer_inner::wrappedTypeName<T>();
    constexpr auto prefix_length = type_printer_inner::wrappedTypeNamePrefixLength();
    constexpr auto suffix_length = type_printer_inner::wrappedTypeNameSuffixLength();
    constexpr auto type_name_length = wrapped_name.length() - prefix_length - suffix_length;
    return wrapped_name.substr(prefix_length, type_name_length);
}
} // namespace slang
