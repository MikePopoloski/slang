// MPark.Variant
//
// Copyright Michael Park, 2015-2016
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

#ifndef MPARK_CONFIG_HPP
#define MPARK_CONFIG_HPP

#ifndef __has_builtin
#define __has_builtin(x) 0
#endif

#if __has_builtin(__builtin_addressof) || __GNUC__ >= 7
#define MPARK_BUILTIN_ADDRESSOF
#endif

#if __has_builtin(__type_pack_element)
#define MPARK_TYPE_PACK_ELEMENT
#endif

#endif  // MPARK_CONFIG_HPP
