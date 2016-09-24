//! \file eggs/variant/in_place.hpp
// Eggs.Variant
//
// Copyright Agustin K-ballo Berge, Fusion Fenix 2014-2016
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef EGGS_VARIANT_IN_PLACE_HPP
#define EGGS_VARIANT_IN_PLACE_HPP

#include <cstddef>
#include <stdexcept>
#include <string>

#include <eggs/variant/detail/config/prefix.hpp>

namespace eggs { namespace variants
{
    namespace detail
    {
        template <std::size_t I>
        struct in_place_index_tag {};

        template <typename T>
        struct in_place_type_tag {};
    }

    ///////////////////////////////////////////////////////////////////////////
    //! struct in_place_tag {};
    //!
    //! The struct `in_place_tag` is used as a unique type to disambiguate
    //! constructor and function overloading. Specifically, `variant<Ts...>`
    //! has a constructor with `in_place_type_t<T>`as the first parameter,
    //! followed by a parameter pack; this indicates that `T` should be
    //! constructed in-place (as if by a call to a placement new expression)
    //! with the forwarded pack expansion as arguments for the initialization
    //! of `T`.
    struct in_place_tag {};

    //! template <std::size_t I>
    //! using in_place_index_t = in_place_tag(&)(unspecified<I>);
    template <std::size_t I>
    using in_place_index_t = in_place_tag(&)(detail::in_place_index_tag<I>);

    //! template <class T>
    //! using in_place_type_t = in_place_tag(&)(unspecified<T>);
    template <typename T>
    using in_place_type_t = in_place_tag(&)(detail::in_place_type_tag<T>);

    //! template <std::size_t I>
    //! in_place_tag in_place(unspecified<I>);
    template <std::size_t I>
    inline in_place_tag in_place(detail::in_place_index_tag<I> = {})
    {
        return {};
    }

    //! template <class T>
    //! in_place_tag in_place(unspecified<T>);
    template <typename T>
    inline in_place_tag in_place(detail::in_place_type_tag<T> = {})
    {
        return {};
    }
}}

#include <eggs/variant/detail/config/suffix.hpp>

#endif /*EGGS_VARIANT_IN_PLACE_HPP*/
