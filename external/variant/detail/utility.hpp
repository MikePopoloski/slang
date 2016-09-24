//! \file eggs/variant/detail/utility.hpp
// Eggs.Variant
//
// Copyright Agustin K-ballo Berge, Fusion Fenix 2014-2016
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef EGGS_VARIANT_DETAIL_UTILITY_HPP
#define EGGS_VARIANT_DETAIL_UTILITY_HPP

#include <type_traits>

#include <eggs/variant/detail/config/prefix.hpp>

namespace eggs { namespace variants { namespace detail
{
    template <typename T>
    EGGS_CXX11_CONSTEXPR T&& forward(
        typename std::remove_reference<T>::type& t) EGGS_CXX11_NOEXCEPT
    {
        return static_cast<T&&>(t);
    }

    template <typename T>
    EGGS_CXX11_CONSTEXPR T&& forward(
        typename std::remove_reference<T>::type&& t) EGGS_CXX11_NOEXCEPT
    {
        return static_cast<T&&>(t);
    }

    ///////////////////////////////////////////////////////////////////////////
    template <typename T>
    EGGS_CXX11_CONSTEXPR typename std::remove_reference<T>::type&& move(
        T&& t) EGGS_CXX11_NOEXCEPT
    {
        return static_cast<typename std::remove_reference<T>::type&&>(t);
    }

}}}

#include <eggs/variant/detail/config/suffix.hpp>

#endif /*EGGS_VARIANT_DETAIL_UTILITY_HPP*/
