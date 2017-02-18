// MPark.Variant
//
// Copyright Michael Park, 2015-2016
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

#ifndef MPARK_IN_PLACE_HPP
#define MPARK_IN_PLACE_HPP

#include <cstddef>

namespace mpark {

  struct in_place_t {
    explicit in_place_t() = default;
  };

  constexpr in_place_t in_place{};

  template <std::size_t I>
  struct in_place_index_t {
    explicit in_place_index_t() = default;
  };

  template <std::size_t I>
  constexpr in_place_index_t<I> in_place_index{};

  template <typename T>
  struct in_place_type_t {
    explicit in_place_type_t() = default;
  };

  template <typename T>
  constexpr in_place_type_t<T> in_place_type{};

}  // namespace mpark

#endif  // MPARK_IN_PLACE_HPP
