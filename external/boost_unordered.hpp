// Copyright 2001, 2002 Peter Dimov and Multi Media Ltd
// Copyright 2002, 2018-2022 Peter Dimov
// Copyright 2002-2018 Peter Dimov
// Copyright 2004 Pavel Vozenilek
// Copyright 2005-2009 Daniel James
// Copyright 2005-2014 Daniel James
// Copyright 2006-2009 Emil Dotchevski and Reverge Studios, Inc
// Copyright 2007, 2014 Peter Dimov
// Copyright 2008-2009 Emil Dotchevski and Reverge Studios, Inc
// Copyright 2008-2016 Daniel James
// Copyright 2015 Ion Gaztanaga
// Copyright 2017 Peter Dimov
// Copyright 2017, 2018 Peter Dimov
// Copyright 2017, 2022 Peter Dimov
// Copyright 2018 Glen Joseph Fernandes
// Copyright 2019, 2021 Peter Dimov
// Copyright 2021 Peter Dimov
// Copyright 2021, 2022 Peter Dimov
// Copyright 2022 Christian Mazakas
// Copyright 2022 Joaquin M Lopez Munoz
// Copyright 2022 Peter Dimov
// Copyright 2022, 2023 Peter Dimov
// Copyright 2022-2023 Christian Mazakas
// Copyright 2022-2023 Joaquin M Lopez Munoz
// Copyright 2023 Christian Mazakas
// Copyright Beman Dawes 2011
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
#pragma once

#include <atomic>
#include <bit>
#include <climits>
#include <cmath>
#include <complex>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <exception>
#include <functional>
#include <initializer_list>
#include <iosfwd>
#include <iterator>
#include <limits>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <system_error>
#include <tuple>
#include <type_traits>
#include <typeindex>
#include <utility>
#include <variant>

#pragma once

// This is a minimal header that contains only the small set
// config entries needed to use boost::unordered, so that the
// whole boost config lib doesn't need to be pulled in.
#ifdef __clang__
#ifndef BOOST_CLANG
#define BOOST_CLANG 1
#define BOOST_CLANG_VERSION (__clang_major__ * 10000 + __clang_minor__ * 100 + __clang_patchlevel__ % 100)
#endif
#elif defined(__GNUC__)
#ifndef BOOST_GCC
#define BOOST_GCC (__GNUC__ * 10000 + __GNUC_MINOR__ * 100 + __GNUC_PATCHLEVEL__)
#define BOOST_GCC_VERSION BOOST_GCC
#endif
#elif defined(_MSC_VER)
#ifndef BOOST_MSVC
#define BOOST_MSVC _MSC_VER
#endif
#endif

#ifndef BOOST_FORCEINLINE
#ifdef _MSC_VER
#define BOOST_FORCEINLINE __forceinline
#elif defined(__GNUC__) && __GNUC__ > 3
// Clang also defines __GNUC__ (as 4)
#define BOOST_FORCEINLINE inline __attribute__((__always_inline__))
#else
#define BOOST_FORCEINLINE inline
#endif
#endif

#ifndef BOOST_NOINLINE
#ifdef _MSC_VER
#define BOOST_NOINLINE __declspec(noinline)
#elif defined(__GNUC__) && __GNUC__ > 3
// Clang also defines __GNUC__ (as 4)
#ifdef __CUDACC__
// nvcc doesn't always parse __noinline__,
// see: https://svn.boost.org/trac/boost/ticket/9392
#define BOOST_NOINLINE __attribute__((noinline))
#elif defined(__HIP__)
// See https://github.com/boostorg/config/issues/392
#define BOOST_NOINLINE __attribute__((noinline))
#else
#define BOOST_NOINLINE __attribute__((__noinline__))
#endif
#else
#define BOOST_NOINLINE
#endif
#endif

#if defined(BOOST_GCC) || defined(BOOST_CLANG)
#define BOOST_LIKELY(x) __builtin_expect(x, 1)
#define BOOST_UNLIKELY(x) __builtin_expect(x, 0)
#define BOOST_SYMBOL_VISIBLE __attribute__((__visibility__("default")))
#else
#define BOOST_SYMBOL_VISIBLE
#endif

#ifndef BOOST_LIKELY
#define BOOST_LIKELY(x) x
#endif
#ifndef BOOST_UNLIKELY
#define BOOST_UNLIKELY(x) x
#endif

#ifndef BOOST_NORETURN
#ifdef _MSC_VER
#define BOOST_NORETURN __declspec(noreturn)
#elif defined(__GNUC__) || defined(__CODEGEARC__) && defined(__clang__)
#define BOOST_NORETURN __attribute__((__noreturn__))
#elif defined(__has_attribute) && defined(__SUNPRO_CC) && (__SUNPRO_CC > 0x5130)
#if __has_attribute(noreturn)
#define BOOST_NORETURN [[noreturn]]
#endif
#elif defined(__has_cpp_attribute)
#if __has_cpp_attribute(noreturn)
#define BOOST_NORETURN [[noreturn]]
#endif
#endif
#endif

#ifndef BOOST_NORETURN
#define BOOST_NO_NORETURN
#define BOOST_NORETURN
#endif

#if BOOST_MSVC
#if !defined(_CPPUNWIND) && !defined(BOOST_NO_EXCEPTIONS)
#define BOOST_NO_EXCEPTIONS
#endif
#if !defined(_CPPRTTI) && !defined(BOOST_NO_RTTI)
#define BOOST_NO_RTTI
#endif
#elif BOOST_GCC
#if !defined(__EXCEPTIONS) && !defined(BOOST_NO_EXCEPTIONS)
#define BOOST_NO_EXCEPTIONS
#endif
#if !defined(__GXX_RTTI) && !defined(BOOST_NO_RTTI)
#define BOOST_NO_RTTI
#endif
#elif BOOST_CLANG
#if !__has_feature(cxx_exceptions) && !defined(BOOST_NO_EXCEPTIONS)
#define BOOST_NO_EXCEPTIONS
#endif
#if !__has_feature(cxx_rtti) && !defined(BOOST_NO_RTTI)
#define BOOST_NO_RTTI
#endif
#endif

// This is the only predef define needed for boost::unordered, so pull it
// out here so we don't need to include all of predef.
#if defined(__ARM_ARCH) || defined(__TARGET_ARCH_ARM) ||                   \
    defined(__TARGET_ARCH_THUMB) || defined(_M_ARM) ||                     \
    defined(__arm__) || defined(__arm64) || defined(__thumb__) ||          \
    defined(_M_ARM64) || defined(__aarch64__) || defined(__AARCH64EL__) || \
    defined(__ARM_ARCH_7__) || defined(__ARM_ARCH_7A__) ||                 \
    defined(__ARM_ARCH_7R__) || defined(__ARM_ARCH_7M__) ||                \
    defined(__ARM_ARCH_6K__) || defined(__ARM_ARCH_6Z__) ||                \
    defined(__ARM_ARCH_6KZ__) || defined(__ARM_ARCH_6T2__) ||              \
    defined(__ARM_ARCH_5TE__) || defined(__ARM_ARCH_5TEJ__) ||             \
    defined(__ARM_ARCH_4T__) || defined(__ARM_ARCH_4__)
#define BOOST_ARCH_ARM 1
#else
#define BOOST_ARCH_ARM 0
#endif

#define BOOST_HAS_NRVO
#define BOOST_HAS_THREADS

#ifndef _MSC_VER
#define BOOST_HAS_PTHREADS
#define BOOST_HAS_NANOSLEEP
#define BOOST_HAS_SCHED_YIELD
#endif
// Copyright 2005-2009 Daniel James.
// Copyright 2021, 2022 Peter Dimov.
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

#ifndef BOOST_FUNCTIONAL_HASH_FWD_HPP
#define BOOST_FUNCTIONAL_HASH_FWD_HPP

namespace boost
{

namespace container_hash
{

template<class T> struct is_unordered_range;
template<class T> struct is_described_class;
template<class T> struct is_tuple_like;

} // namespace container_hash

template<class T> struct hash;

template<class T> void hash_combine( std::size_t& seed, T const& v );

template<class It> void hash_range( std::size_t&, It, It );
template<class It> std::size_t hash_range( It, It );

template<class It> void hash_unordered_range( std::size_t&, It, It );
template<class It> std::size_t hash_unordered_range( It, It );

} // namespace boost

#endif // #ifndef BOOST_FUNCTIONAL_HASH_FWD_HPP
/* Fast open-addressing concurrent hashset.
 *
 * Copyright 2023 Christian Mazakas.
 * Copyright 2023 Joaquin M Lopez Munoz.
 * Copyright 2024 Braden Ganetsky.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifndef BOOST_UNORDERED_CONCURRENT_FLAT_SET_FWD_HPP
#define BOOST_UNORDERED_CONCURRENT_FLAT_SET_FWD_HPP

#ifndef BOOST_NO_CXX17_HDR_MEMORY_RESOURCE
#include <memory_resource>
#endif

namespace boost {
  namespace unordered {

    template <class Key, class Hash = boost::hash<Key>,
      class Pred = std::equal_to<Key>,
      class Allocator = std::allocator<Key> >
    class concurrent_flat_set;

    template <class Key, class Hash, class KeyEqual, class Allocator>
    bool operator==(
      concurrent_flat_set<Key, Hash, KeyEqual, Allocator> const& lhs,
      concurrent_flat_set<Key, Hash, KeyEqual, Allocator> const& rhs);

    template <class Key, class Hash, class KeyEqual, class Allocator>
    bool operator!=(
      concurrent_flat_set<Key, Hash, KeyEqual, Allocator> const& lhs,
      concurrent_flat_set<Key, Hash, KeyEqual, Allocator> const& rhs);

    template <class Key, class Hash, class Pred, class Alloc>
    void swap(concurrent_flat_set<Key, Hash, Pred, Alloc>& x,
      concurrent_flat_set<Key, Hash, Pred, Alloc>& y)
      noexcept(noexcept(x.swap(y)));

    template <class K, class H, class P, class A, class Predicate>
    typename concurrent_flat_set<K, H, P, A>::size_type erase_if(
      concurrent_flat_set<K, H, P, A>& c, Predicate pred);

#ifndef BOOST_NO_CXX17_HDR_MEMORY_RESOURCE
    namespace pmr {
      template <class Key, class Hash = boost::hash<Key>,
        class Pred = std::equal_to<Key> >
      using concurrent_flat_set = boost::unordered::concurrent_flat_set<Key,
        Hash, Pred, std::pmr::polymorphic_allocator<Key> >;
    } // namespace pmr
#endif

  } // namespace unordered

  using boost::unordered::concurrent_flat_set;
} // namespace boost

#endif // BOOST_UNORDERED_CONCURRENT_FLAT_SET_FWD_HPP
// Copyright (C) 2024 Braden Ganetsky
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_UNORDERED_DETAIL_FOA_TYPES_CONSTRUCTIBILITY_HPP
#define BOOST_UNORDERED_DETAIL_FOA_TYPES_CONSTRUCTIBILITY_HPP

namespace boost {
  namespace unordered {
    namespace detail {
      namespace foa {
        template <class Key, class... Args> struct check_key_type_t
        {
          static_assert(std::is_constructible<Key, Args...>::value,
            "key_type must be constructible from Args");
        };
        template <class Key> struct check_key_type_t<Key>
        {
          static_assert(std::is_constructible<Key>::value,
            "key_type must be default constructible");
        };
        template <class Key> struct check_key_type_t<Key, const Key&>
        {
          static_assert(std::is_constructible<Key, const Key&>::value,
            "key_type must be copy constructible");
        };
        template <class Key> struct check_key_type_t<Key, Key&&>
        {
          static_assert(std::is_constructible<Key, Key&&>::value,
            "key_type must be move constructible");
        };

        template <class Mapped, class... Args> struct check_mapped_type_t
        {
          static_assert(std::is_constructible<Mapped, Args...>::value,
            "mapped_type must be constructible from Args");
        };
        template <class Mapped> struct check_mapped_type_t<Mapped>
        {
          static_assert(std::is_constructible<Mapped>::value,
            "mapped_type must be default constructible");
        };
        template <class Mapped>
        struct check_mapped_type_t<Mapped, const Mapped&>
        {
          static_assert(std::is_constructible<Mapped, const Mapped&>::value,
            "mapped_type must be copy constructible");
        };
        template <class Mapped> struct check_mapped_type_t<Mapped, Mapped&&>
        {
          static_assert(std::is_constructible<Mapped, Mapped&&>::value,
            "mapped_type must be move constructible");
        };

        template <class TypePolicy> struct map_types_constructibility
        {
          using key_type = typename TypePolicy::key_type;
          using mapped_type = typename TypePolicy::mapped_type;
          using init_type = typename TypePolicy::init_type;
          using value_type = typename TypePolicy::value_type;

          template <class A, class X, class... Args>
          static void check(A&, X*, Args&&...)
          {
            // Pass through, as we cannot say anything about a general allocator
          }

          template <class... Args> static void check_key_type()
          {
            (void)check_key_type_t<key_type, Args...>{};
          }
          template <class... Args> static void check_mapped_type()
          {
            (void)check_mapped_type_t<mapped_type, Args...>{};
          }

          template <class Arg>
          static void check(std::allocator<value_type>&, key_type*, Arg&&)
          {
            check_key_type<Arg&&>();
          }

          template <class Arg1, class Arg2>
          static void check(
            std::allocator<value_type>&, value_type*, Arg1&&, Arg2&&)
          {
            check_key_type<Arg1&&>();
            check_mapped_type<Arg2&&>();
          }
          template <class Arg1, class Arg2>
          static void check(std::allocator<value_type>&, value_type*,
            const std::pair<Arg1, Arg2>&)
          {
            check_key_type<const Arg1&>();
            check_mapped_type<const Arg2&>();
          }
          template <class Arg1, class Arg2>
          static void check(
            std::allocator<value_type>&, value_type*, std::pair<Arg1, Arg2>&&)
          {
            check_key_type<Arg1&&>();
            check_mapped_type<Arg2&&>();
          }
          template <class... Args1, class... Args2>
          static void check(std::allocator<value_type>&, value_type*,
            std::piecewise_construct_t, std::tuple<Args1...>&&,
            std::tuple<Args2...>&&)
          {
            check_key_type<Args1&&...>();
            check_mapped_type<Args2&&...>();
          }

          template <class Arg1, class Arg2>
          static void check(
            std::allocator<value_type>&, init_type*, Arg1&&, Arg2&&)
          {
            check_key_type<Arg1&&>();
            check_mapped_type<Arg2&&>();
          }
          template <class Arg1, class Arg2>
          static void check(std::allocator<value_type>&, init_type*,
            const std::pair<Arg1, Arg2>&)
          {
            check_key_type<const Arg1&>();
            check_mapped_type<const Arg2&>();
          }
          template <class Arg1, class Arg2>
          static void check(
            std::allocator<value_type>&, init_type*, std::pair<Arg1, Arg2>&&)
          {
            check_key_type<Arg1&&>();
            check_mapped_type<Arg2&&>();
          }
          template <class... Args1, class... Args2>
          static void check(std::allocator<value_type>&, init_type*,
            std::piecewise_construct_t, std::tuple<Args1...>&&,
            std::tuple<Args2...>&&)
          {
            check_key_type<Args1&&...>();
            check_mapped_type<Args2&&...>();
          }
        };

        template <class TypePolicy> struct set_types_constructibility
        {
          using key_type = typename TypePolicy::key_type;
          using value_type = typename TypePolicy::value_type;
          static_assert(std::is_same<key_type, value_type>::value, "");

          template <class A, class X, class... Args>
          static void check(A&, X*, Args&&...)
          {
            // Pass through, as we cannot say anything about a general allocator
          }

          template <class... Args>
          static void check(std::allocator<value_type>&, key_type*, Args&&...)
          {
            (void)check_key_type_t<key_type, Args&&...>{};
          }
        };
      } // namespace foa
    } // namespace detail
  } // namespace unordered
} // namespace boost

#endif // BOOST_UNORDERED_DETAIL_FOA_TYPES_CONSTRUCTIBILITY_HPP
// Copyright (C) 2023 Christian Mazakas
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_UNORDERED_DETAIL_FOA_FLAT_SET_TYPES_HPP
#define BOOST_UNORDERED_DETAIL_FOA_FLAT_SET_TYPES_HPP

namespace boost {
  namespace unordered {
    namespace detail {
      namespace foa {
        template <class Key> struct flat_set_types
        {
          using key_type = Key;
          using init_type = Key;
          using value_type = Key;

          static Key const& extract(value_type const& key) { return key; }

          using element_type = value_type;

          using types = flat_set_types<Key>;
          using constructibility_checker = set_types_constructibility<types>;

          static Key& value_from(element_type& x) { return x; }

          static element_type&& move(element_type& x) { return std::move(x); }

          template <class A, class... Args>
          static void construct(A& al, value_type* p, Args&&... args)
          {
            constructibility_checker::check(al, p, std::forward<Args>(args)...);
            std::allocator_traits<std::remove_cvref_t<decltype(al)>>::construct(al, p, std::forward<Args>(args)...);
          }

          template <class A> static void destroy(A& al, value_type* p) noexcept
          {
            std::allocator_traits<std::remove_cvref_t<decltype(al)>>::destroy(al,  p);
          }
        };
      } // namespace foa
    } // namespace detail
  } // namespace unordered
} // namespace boost

#endif // BOOST_UNORDERED_DETAIL_FOA_FLAT_SET_TYPES_HPP
#ifndef BOOST_CURRENT_FUNCTION_HPP_INCLUDED
#define BOOST_CURRENT_FUNCTION_HPP_INCLUDED

// MS compatible compilers support #pragma once

#if defined(_MSC_VER) && (_MSC_VER >= 1020)
# pragma once
#endif

//
//  boost/current_function.hpp - BOOST_CURRENT_FUNCTION
//
//  Copyright 2002-2018 Peter Dimov
//
//  Distributed under the Boost Software License, Version 1.0.
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt
//
//  http://www.boost.org/libs/assert
//

namespace boost
{

namespace detail
{

inline void current_function_helper()
{

#ifdef  BOOST_DISABLE_CURRENT_FUNCTION

# define BOOST_CURRENT_FUNCTION "(unknown)"

#elif defined(__GNUC__) || (defined(__MWERKS__) && (__MWERKS__ >= 0x3000)) || (defined(__ICC) && (__ICC >= 600)) || defined(__ghs__) || defined(__clang__)

# define BOOST_CURRENT_FUNCTION __PRETTY_FUNCTION__

#elif defined(__DMC__) && (__DMC__ >= 0x810)

# define BOOST_CURRENT_FUNCTION __PRETTY_FUNCTION__

#elif defined(__FUNCSIG__)

# define BOOST_CURRENT_FUNCTION __FUNCSIG__

#elif (defined(__INTEL_COMPILER) && (__INTEL_COMPILER >= 600)) || (defined(__IBMCPP__) && (__IBMCPP__ >= 500))

# define BOOST_CURRENT_FUNCTION __FUNCTION__

#elif defined(__BORLANDC__) && (__BORLANDC__ >= 0x550)

# define BOOST_CURRENT_FUNCTION __FUNC__

#elif defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 199901)

# define BOOST_CURRENT_FUNCTION __func__

#elif defined(__cplusplus) && (__cplusplus >= 201103)

# define BOOST_CURRENT_FUNCTION __func__

#else

# define BOOST_CURRENT_FUNCTION "(unknown)"

#endif

}

} // namespace detail

} // namespace boost

#endif // #ifndef BOOST_CURRENT_FUNCTION_HPP_INCLUDED
//
//  boost/assert.hpp - BOOST_ASSERT(expr)
//                     BOOST_ASSERT_MSG(expr, msg)
//                     BOOST_VERIFY(expr)
//                     BOOST_VERIFY_MSG(expr, msg)
//                     BOOST_ASSERT_IS_VOID
//
//  Copyright (c) 2001, 2002 Peter Dimov and Multi Media Ltd.
//  Copyright (c) 2007, 2014 Peter Dimov
//  Copyright (c) Beman Dawes 2011
//  Copyright (c) 2015 Ion Gaztanaga
//
//  Distributed under the Boost Software License, Version 1.0.
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt
//
//  Note: There are no include guards. This is intentional.
//
//  See http://www.boost.org/libs/assert/assert.html for documentation.
//

//
// Stop inspect complaining about use of 'assert':
//
// boostinspect:naassert_macro
//

//
// BOOST_ASSERT, BOOST_ASSERT_MSG, BOOST_ASSERT_IS_VOID
//

#undef BOOST_ASSERT
#undef BOOST_ASSERT_MSG
#undef BOOST_ASSERT_IS_VOID

#if defined(BOOST_DISABLE_ASSERTS) || ( defined(BOOST_ENABLE_ASSERT_DEBUG_HANDLER) && defined(NDEBUG) )

# define BOOST_ASSERT(expr) ((void)0)
# define BOOST_ASSERT_MSG(expr, msg) ((void)0)
# define BOOST_ASSERT_IS_VOID

#elif defined(BOOST_ENABLE_ASSERT_HANDLER) || ( defined(BOOST_ENABLE_ASSERT_DEBUG_HANDLER) && !defined(NDEBUG) )

namespace boost
{
#ifdef BOOST_ASSERT_HANDLER_IS_NORETURN
    BOOST_NORETURN
#endif
    void assertion_failed(char const * expr, char const * function, char const * file, long line); // user defined
#ifdef BOOST_ASSERT_HANDLER_IS_NORETURN
    BOOST_NORETURN
#endif
    void assertion_failed_msg(char const * expr, char const * msg, char const * function, char const * file, long line); // user defined
} // namespace boost

#define BOOST_ASSERT(expr) (BOOST_LIKELY(!!(expr))? ((void)0): ::boost::assertion_failed(#expr, BOOST_CURRENT_FUNCTION, __FILE__, __LINE__))
#define BOOST_ASSERT_MSG(expr, msg) (BOOST_LIKELY(!!(expr))? ((void)0): ::boost::assertion_failed_msg(#expr, msg, BOOST_CURRENT_FUNCTION, __FILE__, __LINE__))

#else

# include <assert.h> // .h to support old libraries w/o <cassert> - effect is the same

# define BOOST_ASSERT(expr) assert(expr)
# define BOOST_ASSERT_MSG(expr, msg) assert((expr)&&(msg))
#ifdef NDEBUG
# define BOOST_ASSERT_IS_VOID
#endif

#endif

//
// BOOST_VERIFY, BOOST_VERIFY_MSG
//

#undef BOOST_VERIFY
#undef BOOST_VERIFY_MSG

#if defined(BOOST_DISABLE_ASSERTS) || ( !defined(BOOST_ENABLE_ASSERT_HANDLER) && defined(NDEBUG) )

# define BOOST_VERIFY(expr) ((void)(expr))
# define BOOST_VERIFY_MSG(expr, msg) ((void)(expr))

#else

# define BOOST_VERIFY(expr) BOOST_ASSERT(expr)
# define BOOST_VERIFY_MSG(expr, msg) BOOST_ASSERT_MSG(expr,msg)

#endif
/*
Copyright 2019 Glen Joseph Fernandes
(glenjofe@gmail.com)

Distributed under the Boost Software License, Version 1.0.
(http://www.boost.org/LICENSE_1_0.txt)
*/
#ifndef BOOST_CORE_NVP_HPP
#define BOOST_CORE_NVP_HPP

namespace boost {
namespace serialization {

template<class T>
class nvp {
public:
    nvp(const char* n, T& v) noexcept
        : n_(n)
        , v_(std::addressof(v)) { }

    const char* name() const noexcept {
        return n_;
    }

    T& value() const noexcept {
        return *v_;
    }

    const T& const_value() const noexcept {
        return *v_;
    }

private:
    const char* n_;
    T* v_;
};

template<class T>
inline const nvp<T>
make_nvp(const char* n, T& v) noexcept
{
    return nvp<T>(n, v);
}

}

using serialization::nvp;
using serialization::make_nvp;

}

#define BOOST_NVP(v) boost::make_nvp(BOOST_STRINGIZE(v), v)

#endif
#ifndef BOOST_CORE_SERIALIZATION_HPP_INCLUDED
#define BOOST_CORE_SERIALIZATION_HPP_INCLUDED

// MS compatible compilers support #pragma once

#if defined(_MSC_VER) && (_MSC_VER >= 1020)
# pragma once
#endif

// Copyright 2023 Peter Dimov
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt
//
// Utilities needed to implement serialization support
// without including a Boost.Serialization header

namespace boost
{

namespace serialization
{

// Forward declarations (needed for specializations)

template<class T> struct version;

class access;

// Our own version_type replacement. This has to be in
// the `serialization` namespace, because its only purpose
// is to add `serialization` as an associated namespace.

struct core_version_type
{
    unsigned int version_;

    core_version_type( unsigned int version ): version_( version ) {}
    operator unsigned int () const { return version_; }
};

} // namespace serialization

namespace core
{

// nvp

using serialization::nvp;
using serialization::make_nvp;

// split_free

namespace detail
{

template<bool IsSaving> struct load_or_save_f;

template<> struct load_or_save_f<true>
{
    template<class A, class T> void operator()( A& a, T& t, unsigned int v ) const
    {
        save( a, t, serialization::core_version_type( v ) );
    }
};

template<> struct load_or_save_f<false>
{
    template<class A, class T> void operator()( A& a, T& t, unsigned int v ) const
    {
        load( a, t, serialization::core_version_type( v ) );
    }
};

} // namespace detail

template<class A, class T> inline void split_free( A& a, T& t, unsigned int v )
{
    detail::load_or_save_f< A::is_saving::value >()( a, t, v );
}

// split_member

namespace detail
{

template<bool IsSaving, class Access = serialization::access> struct load_or_save_m;

template<class Access> struct load_or_save_m<true, Access>
{
    template<class A, class T> void operator()( A& a, T const& t, unsigned int v ) const
    {
        Access::member_save( a, t, v );
    }
};

template<class Access> struct load_or_save_m<false, Access>
{
    template<class A, class T> void operator()( A& a, T& t, unsigned int v ) const
    {
        Access::member_load( a, t, v );
    }
};

} // namespace detail

template<class A, class T> inline void split_member( A& a, T& t, unsigned int v )
{
    detail::load_or_save_m< A::is_saving::value >()( a, t, v );
}

// load_construct_data_adl

template<class Ar, class T> void load_construct_data_adl( Ar& ar, T* t, unsigned int v )
{
    load_construct_data( ar, t, serialization::core_version_type( v ) );
}

// save_construct_data_adl

template<class Ar, class T> void save_construct_data_adl( Ar& ar, T const* t, unsigned int v )
{
    save_construct_data( ar, t, serialization::core_version_type( v ) );
}

} // namespace core
} // namespace boost

#endif // #ifndef BOOST_CORE_SERIALIZATION_HPP_INCLUDED
/*
Copyright 2018 Glen Joseph Fernandes
(glenjofe@gmail.com)

Distributed under the Boost Software License, Version 1.0.
(http://www.boost.org/LICENSE_1_0.txt)
*/
#ifndef BOOST_CORE_EMPTY_VALUE_HPP
#define BOOST_CORE_EMPTY_VALUE_HPP

#if defined(BOOST_GCC_VERSION) && (BOOST_GCC_VERSION >= 40700)
#define BOOST_DETAIL_EMPTY_VALUE_BASE
#elif defined(BOOST_INTEL) && defined(_MSC_VER) && (_MSC_VER >= 1800)
#define BOOST_DETAIL_EMPTY_VALUE_BASE
#elif defined(BOOST_MSVC) && (BOOST_MSVC >= 1800)
#define BOOST_DETAIL_EMPTY_VALUE_BASE
#elif defined(BOOST_CLANG) && !defined(__CUDACC__)
#if __has_feature(is_empty) && __has_feature(is_final)
#define BOOST_DETAIL_EMPTY_VALUE_BASE
#endif
#endif

#ifdef _MSC_VER
#pragma warning(push)
#pragma warning(disable:4510)
#endif

namespace boost {

template<class T>
struct use_empty_value_base {
    enum {
#ifdef BOOST_DETAIL_EMPTY_VALUE_BASE
        value = __is_empty(T) && !__is_final(T)
#else
        value = false
#endif
    };
};

struct empty_init_t { };

namespace empty_ {

template<class T, unsigned N = 0,
    bool E = boost::use_empty_value_base<T>::value>
class empty_value {
public:
    typedef T type;

    empty_value() = default;

    constexpr empty_value(boost::empty_init_t)
        : value_() { }

    template<class U, class... Args>
    constexpr empty_value(boost::empty_init_t, U&& value, Args&&... args)
        : value_(std::forward<U>(value), std::forward<Args>(args)...) { }

    constexpr const T& get() const noexcept {
        return value_;
    }

    constexpr T& get() noexcept {
        return value_;
    }

private:
    T value_;
};

#ifdef BOOST_MSVC
/*
This is a workaround to an MSVC bug when T is a nested class:
https://developercommunity.visualstudio.com/t/Compiler-bug:-Incorrect-C2247-and-C2248/10690025
*/
namespace detail {

template<class T>
class empty_value_base
    : public T {
public:
    empty_value_base() = default;

    template<class U, class... Args>
    constexpr empty_value_base(U&& value, Args&&... args)
        : T(std::forward<U>(value), std::forward<Args>(args)...) { }
};

}
#endif

template<class T, unsigned N>
class empty_value<T, N, true>
#ifdef BOOST_MSVC
    : detail::empty_value_base<T> {
    typedef detail::empty_value_base<T> empty_base_;
#else
    : T {
    typedef T empty_base_;
#endif

public:
    typedef T type;

    empty_value() = default;

    constexpr empty_value(boost::empty_init_t)
        : empty_base_() { }

    template<class U, class... Args>
    constexpr empty_value(boost::empty_init_t, U&& value, Args&&... args)
        : empty_base_(std::forward<U>(value), std::forward<Args>(args)...) { }

    constexpr const T& get() const noexcept {
        return *this;
    }

    constexpr T& get() noexcept {
        return *this;
    }
};

}

using empty_::empty_value;

inline constexpr empty_init_t empty_init = empty_init_t();

}

#ifdef _MSC_VER
#pragma warning(pop)
#endif

#endif
#ifndef BOOST_CORE_NO_EXCEPTIONS_SUPPORT_HPP
#define BOOST_CORE_NO_EXCEPTIONS_SUPPORT_HPP

#ifdef _MSC_VER
#  pragma once
#endif

//----------------------------------------------------------------------
// (C) Copyright 2004 Pavel Vozenilek.
// Use, modification and distribution is subject to the Boost Software
// License, Version 1.0. (See accompanying file LICENSE_1_0.txt
// or copy at http://www.boost.org/LICENSE_1_0.txt)
//
//
// This file contains helper macros used when exception support may be
// disabled (as indicated by macro BOOST_NO_EXCEPTIONS).
//
// Before picking up these macros you may consider using RAII techniques
// to deal with exceptions - their syntax can be always the same with
// or without exception support enabled.
//----------------------------------------------------------------------

#if !(defined BOOST_NO_EXCEPTIONS)
#    define BOOST_TRY { try
#    define BOOST_CATCH(x) catch(x)
#    define BOOST_RETHROW throw;
#    define BOOST_CATCH_END }
#else
#    if !defined(BOOST_MSVC) || BOOST_MSVC >= 1900
#        define BOOST_TRY { if (true)
#        define BOOST_CATCH(x) else if (false)
#    else
         // warning C4127: conditional expression is constant
#        define BOOST_TRY { \
             __pragma(warning(push)) \
             __pragma(warning(disable: 4127)) \
             if (true) \
             __pragma(warning(pop))
#        define BOOST_CATCH(x) else \
             __pragma(warning(push)) \
             __pragma(warning(disable: 4127)) \
             if (false) \
             __pragma(warning(pop))
#    endif
#    define BOOST_RETHROW
#    define BOOST_CATCH_END }
#endif

#endif
// Copyright (C) 2023 Christian Mazakas
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_UNORDERED_DETAIL_OPT_STORAGE_HPP
#define BOOST_UNORDERED_DETAIL_OPT_STORAGE_HPP

namespace boost {
  namespace unordered {
    namespace detail {
      template <class T> union opt_storage
      {
        [[no_unique_address]] T t_;

        opt_storage() {}
        ~opt_storage() {}

        T* address() noexcept { return std::addressof(t_); }
        T const* address() const noexcept { return std::addressof(t_); }
      };
    } // namespace detail
  } // namespace unordered
} // namespace boost

#endif // BOOST_UNORDERED_DETAIL_OPT_STORAGE_HPP
/* Copyright 2024 Braden Ganetsky.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifndef BOOST_UNORDERED_DETAIL_ALLOCATOR_CONSTRUCTED_HPP
#define BOOST_UNORDERED_DETAIL_ALLOCATOR_CONSTRUCTED_HPP

namespace boost {
  namespace unordered {
    namespace detail {

      struct allocator_policy
      {
        template <class Allocator, class T, class... Args>
        static void construct(Allocator& a, T* p, Args&&... args)
        {
          std::allocator_traits<std::remove_cvref_t<decltype(a)>>::construct(a, p, std::forward<Args>(args)...);
        }

        template <class Allocator, class T>
        static void destroy(Allocator& a, T* p)
        {
          std::allocator_traits<std::remove_cvref_t<decltype(a)>>::destroy(a,  p);
        }
      };

      /* constructs a stack-based object with the given policy and allocator */
      template <class Allocator, class T, class Policy = allocator_policy>
      class allocator_constructed
      {
        opt_storage<T> storage;
        Allocator alloc;

      public:
        template <class... Args>
        allocator_constructed(Allocator const& alloc_, Args&&... args)
            : alloc(alloc_)
        {
          Policy::construct(
            alloc, storage.address(), std::forward<Args>(args)...);
        }

        ~allocator_constructed() { Policy::destroy(alloc, storage.address()); }

        T& value() { return *storage.address(); }
      };

    }
  }
}

#endif
// Copyright 2023 Christian Mazakas
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_UNORDERED_DETAIL_STATIC_ASSERT_HPP
#define BOOST_UNORDERED_DETAIL_STATIC_ASSERT_HPP

#pragma once

#define BOOST_UNORDERED_STATIC_ASSERT(...)                                     \
  static_assert(__VA_ARGS__, #__VA_ARGS__)

#endif // BOOST_UNORDERED_DETAIL_STATIC_ASSERT_HPP
/* Copyright 2022 Joaquin M Lopez Munoz.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifndef BOOST_UNORDERED_DETAIL_NARROW_CAST_HPP
#define BOOST_UNORDERED_DETAIL_NARROW_CAST_HPP

namespace boost{
namespace unordered{
namespace detail{

template<typename To,typename From>
constexpr To narrow_cast(From x) noexcept
{
  BOOST_UNORDERED_STATIC_ASSERT(std::is_integral<From>::value);
  BOOST_UNORDERED_STATIC_ASSERT(std::is_integral<To>::value);
  BOOST_UNORDERED_STATIC_ASSERT(sizeof(From)>=sizeof(To));

  return static_cast<To>(
    x

#ifdef __MSVC_RUNTIME_CHECKS
    /* Avoids VS's "Run-Time Check Failure #1 - A cast to a smaller data type
     * has caused a loss of data."
     */
    &static_cast<typename std::make_unsigned<To>::type>(~static_cast<To>(0))
#endif
  );
}

}
}
}

#endif
#ifndef BOOST_UNORDERED_DETAIL_MULX_HPP
#define BOOST_UNORDERED_DETAIL_MULX_HPP

// Copyright 2022 Peter Dimov.
// Copyright 2022 Joaquin M Lopez Munoz.
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt)

#if defined(_MSC_VER) && !defined(__clang__)
# include <intrin.h>
#endif

namespace boost {
namespace unordered {
namespace detail {

// Bit mixer based on the mulx primitive

#if defined(_MSC_VER) && defined(_M_X64) && !defined(__clang__)

__forceinline std::uint64_t mulx64( std::uint64_t x, std::uint64_t y )
{
    std::uint64_t r2;
    std::uint64_t r = _umul128( x, y, &r2 );
    return r ^ r2;
}

#elif defined(_MSC_VER) && defined(_M_ARM64) && !defined(__clang__)

__forceinline std::uint64_t mulx64( std::uint64_t x, std::uint64_t y )
{
    std::uint64_t r = x * y;
    std::uint64_t r2 = __umulh( x, y );
    return r ^ r2;
}

#elif defined(__SIZEOF_INT128__)

inline std::uint64_t mulx64( std::uint64_t x, std::uint64_t y )
{
    __uint128_t r = (__uint128_t)x * y;
    return (std::uint64_t)r ^ (std::uint64_t)( r >> 64 );
}

#else

inline std::uint64_t mulx64( std::uint64_t x, std::uint64_t y )
{
    std::uint64_t x1 = (std::uint32_t)x;
    std::uint64_t x2 = x >> 32;

    std::uint64_t y1 = (std::uint32_t)y;
    std::uint64_t y2 = y >> 32;

    std::uint64_t r3 = x2 * y2;

    std::uint64_t r2a = x1 * y2;

    r3 += r2a >> 32;

    std::uint64_t r2b = x2 * y1;

    r3 += r2b >> 32;

    std::uint64_t r1 = x1 * y1;

    std::uint64_t r2 = (r1 >> 32) + (std::uint32_t)r2a + (std::uint32_t)r2b;

    r1 = (r2 << 32) + (std::uint32_t)r1;
    r3 += r2 >> 32;

    return r1 ^ r3;
}

#endif

inline std::uint32_t mulx32( std::uint32_t x, std::uint32_t y )
{
    std::uint64_t r = (std::uint64_t)x * y;

#ifdef __MSVC_RUNTIME_CHECKS

    return (std::uint32_t)(r & UINT32_MAX) ^ (std::uint32_t)(r >> 32);

#else

    return (std::uint32_t)r ^ (std::uint32_t)(r >> 32);

#endif
}

#ifdef SIZE_MAX
#if ((((SIZE_MAX >> 16) >> 16) >> 16) >> 15) != 0
#define BOOST_UNORDERED_64B_ARCHITECTURE
#endif
#elif defined(UINTPTR_MAX) /* used as proxy for std::size_t */
#if ((((UINTPTR_MAX >> 16) >> 16) >> 16) >> 15) != 0
#define BOOST_UNORDERED_64B_ARCHITECTURE
#endif
#endif

inline std::size_t mulx( std::size_t x ) noexcept
{
#ifdef BOOST_UNORDERED_64B_ARCHITECTURE

    // multiplier is phi
    return (std::size_t)mulx64( (std::uint64_t)x, 0x9E3779B97F4A7C15ull );

#else /* 32 bits assumed */

    // multiplier from https://arxiv.org/abs/2001.05304
    return mulx32( x, 0xE817FB2Du );

#endif
}

#ifdef BOOST_UNORDERED_64B_ARCHITECTURE
#undef BOOST_UNORDERED_64B_ARCHITECTURE
#endif

} // namespace detail
} // namespace unordered
} // namespace boost

#endif // #ifndef BOOST_UNORDERED_DETAIL_MULX_HPP
// Copyright (C) 2022-2023 Christian Mazakas
// Copyright (C) 2024 Braden Ganetsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_UNORDERED_DETAIL_TYPE_TRAITS_HPP
#define BOOST_UNORDERED_DETAIL_TYPE_TRAITS_HPP

#pragma once

// BOOST_UNORDERED_TEMPLATE_DEDUCTION_GUIDES

#ifndef BOOST_UNORDERED_TEMPLATE_DEDUCTION_GUIDES
#ifndef BOOST_NO_CXX17_DEDUCTION_GUIDES
#define BOOST_UNORDERED_TEMPLATE_DEDUCTION_GUIDES 1
#endif
#endif

#ifndef BOOST_UNORDERED_TEMPLATE_DEDUCTION_GUIDES
#define BOOST_UNORDERED_TEMPLATE_DEDUCTION_GUIDES 0
#endif

namespace boost {
  namespace unordered {
    namespace detail {

      template <class T> struct type_identity
      {
        using type = T;
      };

      template <typename... Ts> struct make_void
      {
        typedef void type;
      };

      template <typename... Ts> using void_t = typename make_void<Ts...>::type;

      template <class T, class = void> struct is_complete : std::false_type
      {
      };

      template <class T>
      struct is_complete<T, void_t<int[sizeof(T)]> > : std::true_type
      {
      };

      template <class T>
      using is_complete_and_move_constructible =
        typename std::conditional<is_complete<T>::value,
          std::is_move_constructible<T>, std::false_type>::type;

      using std::is_trivially_default_constructible;

      using std::is_trivially_copy_constructible;

      using std::is_trivially_copy_assignable;

      namespace type_traits_detail {
        using std::swap;

        template <class T, class = void> struct is_nothrow_swappable_helper
        {
          constexpr static bool const value = false;
        };

        template <class T>
        struct is_nothrow_swappable_helper<T,
          void_t<decltype(swap(std::declval<T&>(), std::declval<T&>()))> >
        {
          constexpr static bool const value =
            noexcept(swap(std::declval<T&>(), std::declval<T&>()));
        };

      } // namespace type_traits_detail

      template <class T>
      struct is_nothrow_swappable
          : public std::integral_constant<bool,
              type_traits_detail::is_nothrow_swappable_helper<T>::value>
      {
      };

      ////////////////////////////////////////////////////////////////////////////
      // Type checkers used for the transparent member functions added by C++20
      // and up

      template <class, class = void>
      struct is_transparent : public std::false_type
      {
      };

      template <class T>
      struct is_transparent<T,
        boost::unordered::detail::void_t<typename T::is_transparent> >
          : public std::true_type
      {
      };

      template <class, class Hash, class KeyEqual> struct are_transparent
      {
        static bool const value =
          is_transparent<Hash>::value && is_transparent<KeyEqual>::value;
      };

      template <class Key, class UnorderedMap> struct transparent_non_iterable
      {
        typedef typename UnorderedMap::hasher hash;
        typedef typename UnorderedMap::key_equal key_equal;
        typedef typename UnorderedMap::iterator iterator;
        typedef typename UnorderedMap::const_iterator const_iterator;

        static bool const value =
          are_transparent<Key, hash, key_equal>::value &&
          !std::is_convertible<Key, iterator>::value &&
          !std::is_convertible<Key, const_iterator>::value;
      };

      template <class T>
      using remove_cvref_t =
        typename std::remove_cv<typename std::remove_reference<T>::type>::type;

      template <class T, class U>
      using is_similar = std::is_same<remove_cvref_t<T>, remove_cvref_t<U> >;

      template <class, class...> struct is_similar_to_any : std::false_type
      {
      };
      template <class T, class U, class... Us>
      struct is_similar_to_any<T, U, Us...>
          : std::conditional<is_similar<T, U>::value, is_similar<T, U>,
              is_similar_to_any<T, Us...> >::type
      {
      };

#if BOOST_UNORDERED_TEMPLATE_DEDUCTION_GUIDES
      // https://eel.is/c++draft/container.requirements#container.alloc.reqmts-34
      // https://eel.is/c++draft/container.requirements#unord.req.general-243

      template <class InputIterator>
      constexpr bool const is_input_iterator_v =
        !std::is_integral<InputIterator>::value;

      template <class A, class = void> struct is_allocator
      {
        constexpr static bool const value = false;
      };

      template <class A>
      struct is_allocator<A,
        boost::unordered::detail::void_t<typename A::value_type,
          decltype(std::declval<A&>().allocate(std::size_t{}))> >
      {
        constexpr static bool const value = true;
      };

      template <class A>
      constexpr bool const is_allocator_v = is_allocator<A>::value;

      template <class H>
      constexpr bool const is_hash_v =
        !std::is_integral<H>::value && !is_allocator_v<H>;

      template <class P> constexpr bool const is_pred_v = !is_allocator_v<P>;

      template <typename T>
      using iter_key_t =
        typename std::iterator_traits<T>::value_type::first_type;
      template <typename T>
      using iter_val_t =
        typename std::iterator_traits<T>::value_type::second_type;
      template <typename T>
      using iter_to_alloc_t =
        typename std::pair<iter_key_t<T> const, iter_val_t<T> >;
#endif

#if BOOST_CXX_VERSION < 201703L
      template <class T>
      constexpr typename std::add_const<T>::type& as_const(T& t) noexcept
      {
        return t;
      }
      template <class T> void as_const(const T&&) = delete;
#else
      using std::as_const;
#endif
    } // namespace detail
  } // namespace unordered
} // namespace boost

#endif // BOOST_UNORDERED_DETAIL_TYPE_TRAITS_HPP
/* Hash function characterization.
 *
 * Copyright 2022-2024 Joaquin M Lopez Munoz.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifndef BOOST_UNORDERED_HASH_TRAITS_HPP
#define BOOST_UNORDERED_HASH_TRAITS_HPP

namespace boost{
namespace unordered{

namespace detail{

template<typename Hash,typename=void>
struct hash_is_avalanching_impl:std::false_type{};

template<typename IsAvalanching>
struct avalanching_value
{
  static constexpr bool value=IsAvalanching::value;
};

/* may be explicitly marked as BOOST_DEPRECATED in the future */
template<> struct avalanching_value<void>
{
  static constexpr bool value=true;
};

template<typename Hash>
struct hash_is_avalanching_impl<
  Hash,
  boost::unordered::detail::void_t<typename Hash::is_avalanching>
>:std::integral_constant<
  bool,
  avalanching_value<typename Hash::is_avalanching>::value
>{};

template<typename Hash>
struct hash_is_avalanching_impl<
  Hash,
  typename std::enable_if<((void)Hash::is_avalanching,true)>::type
>{};

}

/* Each trait can be partially specialized by users for concrete hash functions
 * when actual characterization differs from default.
 */

/* hash_is_avalanching<Hash>::value is:
 *   - false if Hash::is_avalanching is not present.
 *   - Hash::is_avalanching::value if this is present and constexpr-convertible
 *     to a bool.
 *   - true if Hash::is_avalanching is void (deprecated).
 *   - ill-formed otherwise.
 */
template<typename Hash>
struct hash_is_avalanching: detail::hash_is_avalanching_impl<Hash>::type{};

}
}

#endif
// Copyright 2024 Braden Ganetsky
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

// Generated on 2024-08-25T17:48:54

#ifndef BOOST_UNORDERED_UNORDERED_PRINTERS_HPP
#define BOOST_UNORDERED_UNORDERED_PRINTERS_HPP

#ifndef BOOST_ALL_NO_EMBEDDED_GDB_SCRIPTS
#ifdef __ELF__
#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Woverlength-strings"
#endif
__asm__(".pushsection \".debug_gdb_scripts\", \"MS\",%progbits,1\n"
        ".ascii \"\\4gdb.inlined-script.BOOST_UNORDERED_UNORDERED_PRINTERS_HPP\\n\"\n"
        ".ascii \"import gdb.printing\\n\"\n"
        ".ascii \"import gdb.xmethod\\n\"\n"
        ".ascii \"import re\\n\"\n"
        ".ascii \"import math\\n\"\n"

        ".ascii \"class BoostUnorderedHelpers:\\n\"\n"
        ".ascii \"    def maybe_unwrap_atomic(n):\\n\"\n"
        ".ascii \"        if f\\\"{n.type.strip_typedefs()}\\\".startswith(\\\"std::atomic<\\\"):\\n\"\n"
        ".ascii \"            underlying_type = n.type.template_argument(0)\\n\"\n"
        ".ascii \"            return n.cast(underlying_type)\\n\"\n"
        ".ascii \"        else:\\n\"\n"
        ".ascii \"            return n\\n\"\n"

        ".ascii \"    def maybe_unwrap_foa_element(e):\\n\"\n"
        ".ascii \"        if f\\\"{e.type.strip_typedefs()}\\\".startswith(\\\"boost::unordered::detail::foa::element_type<\\\"):\\n\"\n"
        ".ascii \"            return e[\\\"p\\\"]\\n\"\n"
        ".ascii \"        else:\\n\"\n"
        ".ascii \"            return e\\n\"\n"

        ".ascii \"    def maybe_unwrap_reference(value):\\n\"\n"
        ".ascii \"        if value.type.code == gdb.TYPE_CODE_REF:\\n\"\n"
        ".ascii \"            return value.referenced_value()\\n\"\n"
        ".ascii \"        else:\\n\"\n"
        ".ascii \"            return value\\n\"\n"

        ".ascii \"    def countr_zero(n):\\n\"\n"
        ".ascii \"        for i in range(32):\\n\"\n"
        ".ascii \"            if (n & (1 << i)) != 0:\\n\"\n"
        ".ascii \"                return i\\n\"\n"
        ".ascii \"        return 32\\n\"\n"

        ".ascii \"class BoostUnorderedPointerCustomizationPoint:\\n\"\n"
        ".ascii \"    def __init__(self, any_ptr):\\n\"\n"
        ".ascii \"        vis = gdb.default_visualizer(any_ptr)\\n\"\n"
        ".ascii \"        if vis is None:\\n\"\n"
        ".ascii \"            self.to_address = lambda ptr: ptr\\n\"\n"
        ".ascii \"            self.next = lambda ptr, offset: ptr + offset\\n\"\n"
        ".ascii \"        else:\\n\"\n"
        ".ascii \"            self.to_address = lambda ptr: ptr if (ptr.type.code == gdb.TYPE_CODE_PTR) else type(vis).boost_to_address(ptr)\\n\"\n"
        ".ascii \"            self.next = lambda ptr, offset: type(vis).boost_next(ptr, offset)\\n\"\n"

        ".ascii \"class BoostUnorderedFcaPrinter:\\n\"\n"
        ".ascii \"    def __init__(self, val):\\n\"\n"
        ".ascii \"        self.val = BoostUnorderedHelpers.maybe_unwrap_reference(val)\\n\"\n"
        ".ascii \"        self.name = f\\\"{self.val.type.strip_typedefs()}\\\".split(\\\"<\\\")[0]\\n\"\n"
        ".ascii \"        self.name = self.name.replace(\\\"boost::unordered::\\\", \\\"boost::\\\")\\n\"\n"
        ".ascii \"        self.is_map = self.name.endswith(\\\"map\\\")\\n\"\n"
        ".ascii \"        self.cpo = BoostUnorderedPointerCustomizationPoint(self.val[\\\"table_\\\"][\\\"buckets_\\\"][\\\"buckets\\\"])\\n\"\n"

        ".ascii \"    def to_string(self):\\n\"\n"
        ".ascii \"        size = self.val[\\\"table_\\\"][\\\"size_\\\"]\\n\"\n"
        ".ascii \"        return f\\\"{self.name} with {size} elements\\\"\\n\"\n"

        ".ascii \"    def display_hint(self):\\n\"\n"
        ".ascii \"        return \\\"map\\\"\\n\"\n"

        ".ascii \"    def children(self):\\n\"\n"
        ".ascii \"        def generator():\\n\"\n"
        ".ascii \"            grouped_buckets = self.val[\\\"table_\\\"][\\\"buckets_\\\"]\\n\"\n"

        ".ascii \"            size = grouped_buckets[\\\"size_\\\"]\\n\"\n"
        ".ascii \"            buckets = grouped_buckets[\\\"buckets\\\"]\\n\"\n"
        ".ascii \"            bucket_index = 0\\n\"\n"

        ".ascii \"            count = 0\\n\"\n"
        ".ascii \"            while bucket_index != size:\\n\"\n"
        ".ascii \"                current_bucket = self.cpo.next(self.cpo.to_address(buckets), bucket_index)\\n\"\n"
        ".ascii \"                node = self.cpo.to_address(current_bucket.dereference()[\\\"next\\\"])\\n\"\n"
        ".ascii \"                while node != 0:\\n\"\n"
        ".ascii \"                    value = node.dereference()[\\\"buf\\\"][\\\"t_\\\"]\\n\"\n"
        ".ascii \"                    if self.is_map:\\n\"\n"
        ".ascii \"                        first = value[\\\"first\\\"]\\n\"\n"
        ".ascii \"                        second = value[\\\"second\\\"]\\n\"\n"
        ".ascii \"                        yield \\\"\\\", first\\n\"\n"
        ".ascii \"                        yield \\\"\\\", second\\n\"\n"
        ".ascii \"                    else:\\n\"\n"
        ".ascii \"                        yield \\\"\\\", count\\n\"\n"
        ".ascii \"                        yield \\\"\\\", value\\n\"\n"
        ".ascii \"                    count += 1\\n\"\n"
        ".ascii \"                    node = self.cpo.to_address(node.dereference()[\\\"next\\\"])\\n\"\n"
        ".ascii \"                bucket_index += 1\\n\"\n"

        ".ascii \"        return generator()\\n\"\n"

        ".ascii \"class BoostUnorderedFcaIteratorPrinter:\\n\"\n"
        ".ascii \"    def __init__(self, val):\\n\"\n"
        ".ascii \"        self.val = val\\n\"\n"
        ".ascii \"        self.cpo = BoostUnorderedPointerCustomizationPoint(self.val[\\\"p\\\"])\\n\"\n"

        ".ascii \"    def to_string(self):\\n\"\n"
        ".ascii \"        if self.valid():\\n\"\n"
        ".ascii \"            value = self.cpo.to_address(self.val[\\\"p\\\"]).dereference()[\\\"buf\\\"][\\\"t_\\\"]\\n\"\n"
        ".ascii \"            return f\\\"iterator = {{ {value} }}\\\"\\n\"\n"
        ".ascii \"        else:\\n\"\n"
        ".ascii \"            return \\\"iterator = { end iterator }\\\"\\n\"\n"

        ".ascii \"    def valid(self):\\n\"\n"
        ".ascii \"        return (self.cpo.to_address(self.val[\\\"p\\\"]) != 0) and (self.cpo.to_address(self.val[\\\"itb\\\"][\\\"p\\\"]) != 0)\\n\"\n"

        ".ascii \"class BoostUnorderedFoaTableCoreCumulativeStatsPrinter:\\n\"\n"
        ".ascii \"    def __init__(self, val):\\n\"\n"
        ".ascii \"        self.val = val\\n\"\n"

        ".ascii \"    def to_string(self):\\n\"\n"
        ".ascii \"        return \\\"[stats]\\\"\\n\"\n"

        ".ascii \"    def display_hint(self):\\n\"\n"
        ".ascii \"        return \\\"map\\\"\\n\"\n"

        ".ascii \"    def children(self):\\n\"\n"
        ".ascii \"        def generator():\\n\"\n"
        ".ascii \"            members = [\\\"insertion\\\", \\\"successful_lookup\\\", \\\"unsuccessful_lookup\\\"]\\n\"\n"
        ".ascii \"            for member in members:\\n\"\n"
        ".ascii \"                yield \\\"\\\", member\\n\"\n"
        ".ascii \"                yield \\\"\\\", self.val[member]\\n\"\n"
        ".ascii \"        return generator()\\n\"\n"

        ".ascii \"class BoostUnorderedFoaCumulativeStatsPrinter:\\n\"\n"
        ".ascii \"    def __init__(self, val):\\n\"\n"
        ".ascii \"        self.val = val\\n\"\n"
        ".ascii \"        self.n = self.val[\\\"n\\\"]\\n\"\n"
        ".ascii \"        self.N = self.val.type.template_argument(0)\\n\"\n"

        ".ascii \"    def display_hint(self):\\n\"\n"
        ".ascii \"        return \\\"map\\\"\\n\"\n"

        ".ascii \"    def children(self):\\n\"\n"
        ".ascii \"        def generator():\\n\"\n"
        ".ascii \"            yield \\\"\\\", \\\"count\\\"\\n\"\n"
        ".ascii \"            yield \\\"\\\", self.n\\n\"\n"

        ".ascii \"            sequence_stats_data = gdb.lookup_type(\\\"boost::unordered::detail::foa::sequence_stats_data\\\")\\n\"\n"
        ".ascii \"            data = self.val[\\\"data\\\"]\\n\"\n"
        ".ascii \"            arr = data.address.reinterpret_cast(sequence_stats_data.pointer())\\n\"\n"
        ".ascii \"            def build_string(idx):\\n\"\n"
        ".ascii \"                entry = arr[idx]\\n\"\n"
        ".ascii \"                avg = float(entry[\\\"m\\\"])\\n\"\n"
        ".ascii \"                var = float(entry[\\\"s\\\"] / self.n) if (self.n != 0) else 0.0\\n\"\n"
        ".ascii \"                dev = math.sqrt(var)\\n\"\n"
        ".ascii \"                return f\\\"{{avg = {avg}, var = {var}, dev = {dev}}}\\\"\\n\"\n"

        ".ascii \"            if self.N > 0:\\n\"\n"
        ".ascii \"                yield \\\"\\\", \\\"probe_length\\\"\\n\"\n"
        ".ascii \"                yield \\\"\\\", build_string(0)\\n\"\n"
        ".ascii \"            if self.N > 1:\\n\"\n"
        ".ascii \"                yield \\\"\\\", \\\"num_comparisons\\\"\\n\"\n"
        ".ascii \"                yield \\\"\\\", build_string(1)\\n\"\n"

        ".ascii \"        return generator()\\n\"\n"

        ".ascii \"class BoostUnorderedFoaPrinter:\\n\"\n"
        ".ascii \"    def __init__(self, val):\\n\"\n"
        ".ascii \"        self.val = BoostUnorderedHelpers.maybe_unwrap_reference(val)\\n\"\n"
        ".ascii \"        self.name = f\\\"{self.val.type.strip_typedefs()}\\\".split(\\\"<\\\")[0]\\n\"\n"
        ".ascii \"        self.name = self.name.replace(\\\"boost::unordered::\\\", \\\"boost::\\\")\\n\"\n"
        ".ascii \"        self.is_map = self.name.endswith(\\\"map\\\")\\n\"\n"
        ".ascii \"        self.cpo = BoostUnorderedPointerCustomizationPoint(self.val[\\\"table_\\\"][\\\"arrays\\\"][\\\"groups_\\\"])\\n\"\n"

        ".ascii \"    def to_string(self):\\n\"\n"
        ".ascii \"        size = BoostUnorderedHelpers.maybe_unwrap_atomic(self.val[\\\"table_\\\"][\\\"size_ctrl\\\"][\\\"size\\\"])\\n\"\n"
        ".ascii \"        return f\\\"{self.name} with {size} elements\\\"\\n\"\n"

        ".ascii \"    def display_hint(self):\\n\"\n"
        ".ascii \"        return \\\"map\\\"\\n\"\n"

        ".ascii \"    def is_regular_layout(self, group):\\n\"\n"
        ".ascii \"        typename = group[\\\"m\\\"].type.strip_typedefs()\\n\"\n"
        ".ascii \"        array_size = typename.sizeof // typename.target().sizeof\\n\"\n"
        ".ascii \"        if array_size == 16:\\n\"\n"
        ".ascii \"            return True\\n\"\n"
        ".ascii \"        elif array_size == 2:\\n\"\n"
        ".ascii \"            return False\\n\"\n"

        ".ascii \"    def match_occupied(self, group):\\n\"\n"
        ".ascii \"        m = group[\\\"m\\\"]\\n\"\n"
        ".ascii \"        at = lambda b: BoostUnorderedHelpers.maybe_unwrap_atomic(m[b][\\\"n\\\"])\\n\"\n"

        ".ascii \"        if self.is_regular_layout(group):\\n\"\n"
        ".ascii \"            bits = [1 << b for b in range(16) if at(b) == 0]\\n\"\n"
        ".ascii \"            return 0x7FFF & ~sum(bits)\\n\"\n"
        ".ascii \"        else:\\n\"\n"
        ".ascii \"            xx = at(0) | at(1)\\n\"\n"
        ".ascii \"            yy = xx | (xx >> 32)\\n\"\n"
        ".ascii \"            return 0x7FFF & (yy | (yy >> 16))\\n\"\n"

        ".ascii \"    def is_sentinel(self, group, pos):\\n\"\n"
        ".ascii \"        m = group[\\\"m\\\"]\\n\"\n"
        ".ascii \"        at = lambda b: BoostUnorderedHelpers.maybe_unwrap_atomic(m[b][\\\"n\\\"])\\n\"\n"

        ".ascii \"        N = group[\\\"N\\\"]\\n\"\n"
        ".ascii \"        sentinel_ = group[\\\"sentinel_\\\"]\\n\"\n"
        ".ascii \"        if self.is_regular_layout(group):\\n\"\n"
        ".ascii \"            return pos == N-1 and at(N-1) == sentinel_\\n\"\n"
        ".ascii \"        else:\\n\"\n"
        ".ascii \"            return pos == N-1 and (at(0) & 0x4000400040004000) == 0x4000 and (at(1) & 0x4000400040004000) == 0\\n\"\n"

        ".ascii \"    def children(self):\\n\"\n"
        ".ascii \"        def generator():\\n\"\n"
        ".ascii \"            table = self.val[\\\"table_\\\"]\\n\"\n"
        ".ascii \"            groups = self.cpo.to_address(table[\\\"arrays\\\"][\\\"groups_\\\"])\\n\"\n"
        ".ascii \"            elements = self.cpo.to_address(table[\\\"arrays\\\"][\\\"elements_\\\"])\\n\"\n"

        ".ascii \"            pc_ = groups.cast(gdb.lookup_type(\\\"unsigned char\\\").pointer())\\n\"\n"
        ".ascii \"            p_ = elements\\n\"\n"
        ".ascii \"            first_time = True\\n\"\n"
        ".ascii \"            mask = 0\\n\"\n"
        ".ascii \"            n0 = 0\\n\"\n"
        ".ascii \"            n = 0\\n\"\n"

        ".ascii \"            count = 0\\n\"\n"
        ".ascii \"            while p_ != 0:\\n\"\n"
        ".ascii \"                # This if block mirrors the condition in the begin() call\\n\"\n"
        ".ascii \"                if (not first_time) or (self.match_occupied(groups.dereference()) & 1):\\n\"\n"
        ".ascii \"                    pointer = BoostUnorderedHelpers.maybe_unwrap_foa_element(p_)\\n\"\n"
        ".ascii \"                    value = self.cpo.to_address(pointer).dereference()\\n\"\n"
        ".ascii \"                    if self.is_map:\\n\"\n"
        ".ascii \"                        first = value[\\\"first\\\"]\\n\"\n"
        ".ascii \"                        second = value[\\\"second\\\"]\\n\"\n"
        ".ascii \"                        yield \\\"\\\", first\\n\"\n"
        ".ascii \"                        yield \\\"\\\", second\\n\"\n"
        ".ascii \"                    else:\\n\"\n"
        ".ascii \"                        yield \\\"\\\", count\\n\"\n"
        ".ascii \"                        yield \\\"\\\", value\\n\"\n"
        ".ascii \"                    count += 1\\n\"\n"
        ".ascii \"                first_time = False\\n\"\n"

        ".ascii \"                n0 = pc_.cast(gdb.lookup_type(\\\"uintptr_t\\\")) % groups.dereference().type.sizeof\\n\"\n"
        ".ascii \"                pc_ = self.cpo.next(pc_, -n0)\\n\"\n"

        ".ascii \"                mask = (self.match_occupied(pc_.cast(groups.type).dereference()) >> (n0+1)) << (n0+1)\\n\"\n"
        ".ascii \"                while mask == 0:\\n\"\n"
        ".ascii \"                    pc_ = self.cpo.next(pc_, groups.dereference().type.sizeof)\\n\"\n"
        ".ascii \"                    p_ = self.cpo.next(p_, groups.dereference()[\\\"N\\\"])\\n\"\n"
        ".ascii \"                    mask = self.match_occupied(pc_.cast(groups.type).dereference())\\n\"\n"

        ".ascii \"                n = BoostUnorderedHelpers.countr_zero(mask)\\n\"\n"
        ".ascii \"                if self.is_sentinel(pc_.cast(groups.type).dereference(), n):\\n\"\n"
        ".ascii \"                    p_ = 0\\n\"\n"
        ".ascii \"                else:\\n\"\n"
        ".ascii \"                    pc_ = self.cpo.next(pc_, n)\\n\"\n"
        ".ascii \"                    p_ = self.cpo.next(p_, n - n0)\\n\"\n"

        ".ascii \"        return generator()\\n\"\n"

        ".ascii \"class BoostUnorderedFoaIteratorPrinter:\\n\"\n"
        ".ascii \"    def __init__(self, val):\\n\"\n"
        ".ascii \"        self.val = val\\n\"\n"
        ".ascii \"        self.cpo = BoostUnorderedPointerCustomizationPoint(self.val[\\\"p_\\\"])\\n\"\n"

        ".ascii \"    def to_string(self):\\n\"\n"
        ".ascii \"        if self.valid():\\n\"\n"
        ".ascii \"            element = self.cpo.to_address(self.val[\\\"p_\\\"])\\n\"\n"
        ".ascii \"            pointer = BoostUnorderedHelpers.maybe_unwrap_foa_element(element)\\n\"\n"
        ".ascii \"            value = self.cpo.to_address(pointer).dereference()\\n\"\n"
        ".ascii \"            return f\\\"iterator = {{ {value} }}\\\"\\n\"\n"
        ".ascii \"        else:\\n\"\n"
        ".ascii \"            return \\\"iterator = { end iterator }\\\"\\n\"\n"

        ".ascii \"    def valid(self):\\n\"\n"
        ".ascii \"        return (self.cpo.to_address(self.val[\\\"p_\\\"]) != 0) and (self.cpo.to_address(self.val[\\\"pc_\\\"]) != 0)\\n\"\n"

        ".ascii \"def boost_unordered_build_pretty_printer():\\n\"\n"
        ".ascii \"    pp = gdb.printing.RegexpCollectionPrettyPrinter(\\\"boost_unordered\\\")\\n\"\n"
        ".ascii \"    add_template_printer = lambda name, printer: pp.add_printer(name, f\\\"^{name}<.*>$\\\", printer)\\n\"\n"
        ".ascii \"    add_concrete_printer = lambda name, printer: pp.add_printer(name, f\\\"^{name}$\\\", printer)\\n\"\n"

        ".ascii \"    add_template_printer(\\\"boost::unordered::unordered_map\\\", BoostUnorderedFcaPrinter)\\n\"\n"
        ".ascii \"    add_template_printer(\\\"boost::unordered::unordered_multimap\\\", BoostUnorderedFcaPrinter)\\n\"\n"
        ".ascii \"    add_template_printer(\\\"boost::unordered::unordered_set\\\", BoostUnorderedFcaPrinter)\\n\"\n"
        ".ascii \"    add_template_printer(\\\"boost::unordered::unordered_multiset\\\", BoostUnorderedFcaPrinter)\\n\"\n"

        ".ascii \"    add_template_printer(\\\"boost::unordered::detail::iterator_detail::iterator\\\", BoostUnorderedFcaIteratorPrinter)\\n\"\n"
        ".ascii \"    add_template_printer(\\\"boost::unordered::detail::iterator_detail::c_iterator\\\", BoostUnorderedFcaIteratorPrinter)\\n\"\n"

        ".ascii \"    add_template_printer(\\\"boost::unordered::unordered_flat_map\\\", BoostUnorderedFoaPrinter)\\n\"\n"
        ".ascii \"    add_template_printer(\\\"boost::unordered::unordered_flat_set\\\", BoostUnorderedFoaPrinter)\\n\"\n"
        ".ascii \"    add_template_printer(\\\"boost::unordered::unordered_node_map\\\", BoostUnorderedFoaPrinter)\\n\"\n"
        ".ascii \"    add_template_printer(\\\"boost::unordered::unordered_node_set\\\", BoostUnorderedFoaPrinter)\\n\"\n"
        ".ascii \"    add_template_printer(\\\"boost::unordered::concurrent_flat_map\\\", BoostUnorderedFoaPrinter)\\n\"\n"
        ".ascii \"    add_template_printer(\\\"boost::unordered::concurrent_flat_set\\\", BoostUnorderedFoaPrinter)\\n\"\n"
        ".ascii \"    add_template_printer(\\\"boost::unordered::concurrent_node_map\\\", BoostUnorderedFoaPrinter)\\n\"\n"
        ".ascii \"    add_template_printer(\\\"boost::unordered::concurrent_node_set\\\", BoostUnorderedFoaPrinter)\\n\"\n"

        ".ascii \"    add_template_printer(\\\"boost::unordered::detail::foa::table_iterator\\\", BoostUnorderedFoaIteratorPrinter)\\n\"\n"

        ".ascii \"    add_concrete_printer(\\\"boost::unordered::detail::foa::table_core_cumulative_stats\\\", BoostUnorderedFoaTableCoreCumulativeStatsPrinter)\\n\"\n"
        ".ascii \"    add_template_printer(\\\"boost::unordered::detail::foa::cumulative_stats\\\", BoostUnorderedFoaCumulativeStatsPrinter)\\n\"\n"
        ".ascii \"    add_template_printer(\\\"boost::unordered::detail::foa::concurrent_cumulative_stats\\\", BoostUnorderedFoaCumulativeStatsPrinter)\\n\"\n"

        ".ascii \"    return pp\\n\"\n"

        ".ascii \"gdb.printing.register_pretty_printer(gdb.current_objfile(), boost_unordered_build_pretty_printer())\\n\"\n"

        ".ascii \"# https://sourceware.org/gdb/current/onlinedocs/gdb.html/Writing-an-Xmethod.html\\n\"\n"
        ".ascii \"class BoostUnorderedFoaGetStatsMethod(gdb.xmethod.XMethod):\\n\"\n"
        ".ascii \"    def __init__(self):\\n\"\n"
        ".ascii \"        gdb.xmethod.XMethod.__init__(self, \\\"get_stats\\\")\\n\"\n"

        ".ascii \"    def get_worker(self, method_name):\\n\"\n"
        ".ascii \"        if method_name == \\\"get_stats\\\":\\n\"\n"
        ".ascii \"            return BoostUnorderedFoaGetStatsWorker()\\n\"\n"

        ".ascii \"class BoostUnorderedFoaGetStatsWorker(gdb.xmethod.XMethodWorker):\\n\"\n"
        ".ascii \"    def get_arg_types(self):\\n\"\n"
        ".ascii \"        return None\\n\"\n"

        ".ascii \"    def get_result_type(self, obj):\\n\"\n"
        ".ascii \"        return gdb.lookup_type(\\\"boost::unordered::detail::foa::table_core_cumulative_stats\\\")\\n\"\n"

        ".ascii \"    def __call__(self, obj):\\n\"\n"
        ".ascii \"        try:\\n\"\n"
        ".ascii \"            return obj[\\\"table_\\\"][\\\"cstats\\\"]\\n\"\n"
        ".ascii \"        except gdb.error:\\n\"\n"
        ".ascii \"            print(\\\"Error: Binary was compiled without stats. Recompile with `BOOST_UNORDERED_ENABLE_STATS` defined.\\\")\\n\"\n"
        ".ascii \"            return\\n\"\n"

        ".ascii \"class BoostUnorderedFoaMatcher(gdb.xmethod.XMethodMatcher):\\n\"\n"
        ".ascii \"    def __init__(self):\\n\"\n"
        ".ascii \"        gdb.xmethod.XMethodMatcher.__init__(self, 'BoostUnorderedFoaMatcher')\\n\"\n"
        ".ascii \"        self.methods = [BoostUnorderedFoaGetStatsMethod()]\\n\"\n"

        ".ascii \"    def match(self, class_type, method_name):\\n\"\n"
        ".ascii \"        template_name = f\\\"{class_type.strip_typedefs()}\\\".split(\\\"<\\\")[0]\\n\"\n"
        ".ascii \"        regex = \\\"^boost::unordered::(unordered|concurrent)_(flat|node)_(map|set)$\\\"\\n\"\n"
        ".ascii \"        if not re.match(regex, template_name):\\n\"\n"
        ".ascii \"            return None\\n\"\n"

        ".ascii \"        workers = []\\n\"\n"
        ".ascii \"        for method in self.methods:\\n\"\n"
        ".ascii \"            if method.enabled:\\n\"\n"
        ".ascii \"                worker = method.get_worker(method_name)\\n\"\n"
        ".ascii \"                if worker:\\n\"\n"
        ".ascii \"                    workers.append(worker)\\n\"\n"
        ".ascii \"        return workers\\n\"\n"

        ".ascii \"gdb.xmethod.register_xmethod_matcher(None, BoostUnorderedFoaMatcher())\\n\"\n"

        ".ascii \"\\\"\\\"\\\" Fancy pointer support \\\"\\\"\\\"\\n\"\n"

        ".ascii \"\\\"\\\"\\\"\\n\"\n"
        ".ascii \"To allow your own fancy pointer type to interact with Boost.Unordered GDB pretty-printers,\\n\"\n"
        ".ascii \"create a pretty-printer for your own type with the following additional methods.\\n\"\n"

        ".ascii \"(Note, this is assuming the presence of a type alias `pointer` for the underlying\\n\"\n"
        ".ascii \"raw pointer type, Substitute whichever name is applicable in your case.)\\n\"\n"

        ".ascii \"`boost_to_address(fancy_ptr)`\\n\"\n"
        ".ascii \"    * A static method, but `@staticmethod` is not required\\n\"\n"
        ".ascii \"    * Parameter `fancy_ptr` of type `gdb.Value`\\n\"\n"
        ".ascii \"        * Its `.type` will be your fancy pointer type\\n\"\n"
        ".ascii \"    * Returns a `gdb.Value` with the raw pointer equivalent to your fancy pointer\\n\"\n"
        ".ascii \"        * This method should be equivalent to calling `operator->()` on your fancy pointer in C++\\n\"\n"

        ".ascii \"`boost_next(raw_ptr, offset)`\\n\"\n"
        ".ascii \"    * Parameter `raw_ptr` of type `gdb.Value`\\n\"\n"
        ".ascii \"        * Its `.type` will be `pointer`\\n\"\n"
        ".ascii \"    * Parameter `offset`\\n\"\n"
        ".ascii \"        * Either has integer type, or is of type `gdb.Value` with an underlying integer\\n\"\n"
        ".ascii \"    * Returns a `gdb.Value` with the raw pointer equivalent to your fancy pointer, as if you did the following operations\\n\"\n"
        ".ascii \"        1. Convert the incoming raw pointer to your fancy pointer\\n\"\n"
        ".ascii \"        2. Use operator+= to add the offset to the fancy pointer\\n\"\n"
        ".ascii \"        3. Convert back to the raw pointer\\n\"\n"
        ".ascii \"    * Note, you will not actually do these operations as stated. You will do equivalent lower-level operations that emulate having done the above\\n\"\n"
        ".ascii \"        * Ultimately, it will be as if you called `operator+()` on your fancy pointer in C++, but using only raw pointers\\n\"\n"

        ".ascii \"Example\\n\"\n"
        ".ascii \"```\\n\"\n"
        ".ascii \"class MyFancyPtrPrinter:\\n\"\n"
        ".ascii \"    ...\\n\"\n"

        ".ascii \"    # Equivalent to `operator->()`\\n\"\n"
        ".ascii \"    def boost_to_address(fancy_ptr):\\n\"\n"
        ".ascii \"        ...\\n\"\n"
        ".ascii \"        return ...\\n\"\n"

        ".ascii \"    # Equivalent to `operator+()`\\n\"\n"
        ".ascii \"    def boost_next(raw_ptr, offset):\\n\"\n"
        ".ascii \"        ...\\n\"\n"
        ".ascii \"        return ...\\n\"\n"

        ".ascii \"    ...\\n\"\n"
        ".ascii \"```\\n\"\n"
        ".ascii \"\\\"\\\"\\\"\\n\"\n"

        ".byte 0\n"
        ".popsection\n");
#ifdef __clang__
#pragma clang diagnostic pop
#endif
#endif // defined(__ELF__)
#endif // !defined(BOOST_ALL_NO_EMBEDDED_GDB_SCRIPTS)

#endif // !defined(BOOST_UNORDERED_UNORDERED_PRINTERS_HPP)
#ifndef BOOST_MP11_VERSION_HPP_INCLUDED
#define BOOST_MP11_VERSION_HPP_INCLUDED

//  Copyright 2019 Peter Dimov
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

// Same format as BOOST_VERSION:
//   major * 100000 + minor * 100 + patch

#define BOOST_MP11_VERSION 108800

#endif // #ifndef BOOST_MP11_VERSION_HPP_INCLUDED
#ifndef BOOST_MP11_INTEGER_SEQUENCE_HPP_INCLUDED
#define BOOST_MP11_INTEGER_SEQUENCE_HPP_INCLUDED

// Copyright 2015, 2017, 2019 Peter Dimov.
//
// Distributed under the Boost Software License, Version 1.0.
//
// See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt

#if defined(_MSC_VER) || defined(__GNUC__)
# pragma push_macro( "I" )
# undef I
#endif

#ifdef __has_builtin
# if __has_builtin(__make_integer_seq)
#  define BOOST_MP11_HAS_MAKE_INTEGER_SEQ
# endif
#endif

namespace boost
{
namespace mp11
{

// integer_sequence
template<class T, T... I> struct integer_sequence
{
};

#ifdef BOOST_MP11_HAS_MAKE_INTEGER_SEQ

template<class T, T N> using make_integer_sequence = __make_integer_seq<integer_sequence, T, N>;

#else

// detail::make_integer_sequence_impl
namespace detail
{

// iseq_if_c
template<bool C, class T, class E> struct iseq_if_c_impl;

template<class T, class E> struct iseq_if_c_impl<true, T, E>
{
    using type = T;
};

template<class T, class E> struct iseq_if_c_impl<false, T, E>
{
    using type = E;
};

template<bool C, class T, class E> using iseq_if_c = typename iseq_if_c_impl<C, T, E>::type;

// iseq_identity
template<class T> struct iseq_identity
{
    using type = T;
};

template<class S1, class S2> struct append_integer_sequence;

template<class T, T... I, T... J> struct append_integer_sequence<integer_sequence<T, I...>, integer_sequence<T, J...>>
{
    using type = integer_sequence< T, I..., ( J + sizeof...(I) )... >;
};

template<class T, T N> struct make_integer_sequence_impl;

template<class T, T N> struct make_integer_sequence_impl_
{
private:

    static_assert( N >= 0, "make_integer_sequence<T, N>: N must not be negative" );

    static T const M = N / 2;
    static T const R = N % 2;

    using S1 = typename make_integer_sequence_impl<T, M>::type;
    using S2 = typename append_integer_sequence<S1, S1>::type;
    using S3 = typename make_integer_sequence_impl<T, R>::type;
    using S4 = typename append_integer_sequence<S2, S3>::type;

public:

    using type = S4;
};

template<class T, T N> struct make_integer_sequence_impl: iseq_if_c<N == 0, iseq_identity<integer_sequence<T>>, iseq_if_c<N == 1, iseq_identity<integer_sequence<T, 0>>, make_integer_sequence_impl_<T, N> > >
{
};

} // namespace detail

// make_integer_sequence
template<class T, T N> using make_integer_sequence = typename detail::make_integer_sequence_impl<T, N>::type;

#endif // defined(BOOST_MP11_HAS_MAKE_INTEGER_SEQ)

// index_sequence
template<std::size_t... I> using index_sequence = integer_sequence<std::size_t, I...>;

// make_index_sequence
template<std::size_t N> using make_index_sequence = make_integer_sequence<std::size_t, N>;

// index_sequence_for
template<class... T> using index_sequence_for = make_integer_sequence<std::size_t, sizeof...(T)>;

} // namespace mp11
} // namespace boost

#if defined(_MSC_VER) || defined(__GNUC__)
# pragma pop_macro( "I" )
#endif

#endif // #ifndef BOOST_MP11_INTEGER_SEQUENCE_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_CONFIG_HPP_INCLUDED
#define BOOST_MP11_DETAIL_CONFIG_HPP_INCLUDED

// Copyright 2016, 2018, 2019 Peter Dimov.
//
// Distributed under the Boost Software License, Version 1.0.
//
// See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt

// BOOST_MP11_WORKAROUND

//

#define BOOST_MP11_CUDA 0
#define BOOST_MP11_CLANG 0
#define BOOST_MP11_INTEL 0
#define BOOST_MP11_GCC 0
#define BOOST_MP11_MSVC 0

#define BOOST_MP11_CONSTEXPR constexpr

#ifdef  __CUDACC__

// nvcc

# undef BOOST_MP11_CUDA
# define BOOST_MP11_CUDA (__CUDACC_VER_MAJOR__ * 1000000 + __CUDACC_VER_MINOR__ * 10000 + __CUDACC_VER_BUILD__)

// CUDA (8.0) has no constexpr support in msvc mode:
# if defined(_MSC_VER) && (BOOST_MP11_CUDA < 9000000)

#  define BOOST_MP11_NO_CONSTEXPR

#  undef BOOST_MP11_CONSTEXPR
#  define BOOST_MP11_CONSTEXPR

# endif

#endif

#ifdef __clang__

// Clang

# undef BOOST_MP11_CLANG
# define BOOST_MP11_CLANG (__clang_major__ * 100 + __clang_minor__)

# if defined(__has_cpp_attribute)
#  if __has_cpp_attribute(fallthrough) && __cplusplus >= 201406L // Clang 3.9+ in c++1z mode
#   define BOOST_MP11_HAS_FOLD_EXPRESSIONS
#  endif
# endif

#if BOOST_MP11_CLANG < 400 && __cplusplus >= 201402L \
   && defined( __GLIBCXX__ ) && !__has_include(<shared_mutex>)

// Clang pre-4 in C++14 mode, libstdc++ pre-4.9, ::gets is not defined,
// but Clang tries to import it into std

   extern "C" char *gets (char *__s);
#endif

#elif defined(__INTEL_COMPILER)

// Intel C++

# undef BOOST_MP11_INTEL
# define BOOST_MP11_INTEL __INTEL_COMPILER

#elif defined(__GNUC__)

// g++

# undef BOOST_MP11_GCC
# define BOOST_MP11_GCC (__GNUC__ * 10000 + __GNUC_MINOR__ * 100 + __GNUC_PATCHLEVEL__)

#elif defined(_MSC_VER)

// MS Visual C++

# undef BOOST_MP11_MSVC
# define BOOST_MP11_MSVC _MSC_VER

#if _MSC_FULL_VER < 190024210 // 2015u3
#  undef BOOST_MP11_CONSTEXPR
#  define BOOST_MP11_CONSTEXPR
#endif

#endif

// BOOST_MP11_HAS_CXX14_CONSTEXPR

#if !defined(BOOST_MP11_NO_CONSTEXPR) && defined(__cpp_constexpr) && __cpp_constexpr >= 201304
#  define BOOST_MP11_HAS_CXX14_CONSTEXPR
#endif

// BOOST_MP11_HAS_FOLD_EXPRESSIONS

#if !defined(BOOST_MP11_HAS_FOLD_EXPRESSIONS) && defined(__cpp_fold_expressions) && __cpp_fold_expressions >= 201603
#  define BOOST_MP11_HAS_FOLD_EXPRESSIONS
#endif

// BOOST_MP11_HAS_TYPE_PACK_ELEMENT

#ifdef __has_builtin
# if __has_builtin(__type_pack_element)
#  define BOOST_MP11_HAS_TYPE_PACK_ELEMENT
# endif
#endif

// BOOST_MP11_HAS_TEMPLATE_AUTO

#if defined(__cpp_nontype_template_parameter_auto) && __cpp_nontype_template_parameter_auto >= 201606L
# define BOOST_MP11_HAS_TEMPLATE_AUTO
#endif

// BOOST_MP11_DEPRECATED(msg)

#if defined(__GNUC__) || defined(__clang__)
#  define BOOST_MP11_DEPRECATED(msg) __attribute__((deprecated(msg)))
#elif defined(_MSC_VER) && _MSC_VER >= 1900
#  define BOOST_MP11_DEPRECATED(msg) [[deprecated(msg)]]
#else
#  define BOOST_MP11_DEPRECATED(msg)
#endif

#endif // #ifndef BOOST_MP11_DETAIL_CONFIG_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_VALUE_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_VALUE_HPP_INCLUDED

// Copyright 2023 Peter Dimov
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

namespace boost
{
namespace mp11
{

template<auto A> using mp_value = std::integral_constant<decltype(A), A>;

} // namespace mp11
} // namespace boost

#endif // #if defined(BOOST_MP11_HAS_TEMPLATE_AUTO)

#endif // #ifndef BOOST_MP11_DETAIL_MP_VALUE_HPP_INCLUDED
#ifndef BOOST_MP11_INTEGRAL_HPP_INCLUDED
#define BOOST_MP11_INTEGRAL_HPP_INCLUDED

//  Copyright 2015 Peter Dimov.
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

#if defined(_MSC_VER) || defined(__GNUC__)
# pragma push_macro( "I" )
# undef I
#endif

namespace boost
{
namespace mp11
{

// mp_bool
template<bool B> using mp_bool = std::integral_constant<bool, B>;

using mp_true = mp_bool<true>;
using mp_false = mp_bool<false>;

// mp_to_bool
template<class T> using mp_to_bool = mp_bool<static_cast<bool>( T::value )>;

// mp_not<T>
template<class T> using mp_not = mp_bool< !T::value >;

// mp_int
template<int I> using mp_int = std::integral_constant<int, I>;

// mp_size_t
template<std::size_t N> using mp_size_t = std::integral_constant<std::size_t, N>;

} // namespace mp11
} // namespace boost

#if defined(_MSC_VER) || defined(__GNUC__)
# pragma pop_macro( "I" )
#endif

#endif // #ifndef BOOST_MP11_INTEGRAL_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_LIST_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_LIST_HPP_INCLUDED

//  Copyright 2015, 2016 Peter Dimov.
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_list<T...>
template<class... T> struct mp_list
{
};

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_DETAIL_MP_LIST_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_LIST_V_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_LIST_V_HPP_INCLUDED

// Copyright 2023 Peter Dimov
// Distributed under the Boost Software License, Version 1.0.
// http://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

// mp_list_v<A...>
template<auto... A> struct mp_list_v
{
};

#endif

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_DETAIL_MP_LIST_V_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_IS_LIST_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_IS_LIST_HPP_INCLUDED

// Copyright 2015-2019 Peter Dimov.
//
// Distributed under the Boost Software License, Version 1.0.
//
// See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_is_list<L>
namespace detail
{

template<class L> struct mp_is_list_impl
{
    using type = mp_false;
};

template<template<class...> class L, class... T> struct mp_is_list_impl<L<T...>>
{
    using type = mp_true;
};

} // namespace detail

template<class L> using mp_is_list = typename detail::mp_is_list_impl<L>::type;

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_DETAIL_MP_IS_LIST_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_IS_VALUE_LIST_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_IS_VALUE_LIST_HPP_INCLUDED

// Copyright 2023 Peter Dimov
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_is_value_list<L>
namespace detail
{

template<class L> struct mp_is_value_list_impl
{
    using type = mp_false;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto... A> struct mp_is_value_list_impl<L<A...>>
{
    using type = mp_true;
};

#endif

} // namespace detail

template<class L> using mp_is_value_list = typename detail::mp_is_value_list_impl<L>::type;

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_DETAIL_MP_IS_VALUE_LIST_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_FRONT_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_FRONT_HPP_INCLUDED

//  Copyright 2015-2023 Peter Dimov.
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_front<L>
namespace detail
{

template<class L> struct mp_front_impl
{
// An error "no type named 'type'" here means that the argument to mp_front
// is either not a list, or is an empty list
};

template<template<class...> class L, class T1, class... T> struct mp_front_impl<L<T1, T...>>
{
    using type = T1;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto A1, auto... A> struct mp_front_impl<L<A1, A...>>
{
    using type = mp_value<A1>;
};

#endif

} // namespace detail

template<class L> using mp_front = typename detail::mp_front_impl<L>::type;

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_DETAIL_MP_FRONT_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_DEFER_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_DEFER_HPP_INCLUDED

// Copyright 2015-2020, 2023 Peter Dimov
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_if, mp_if_c
namespace detail
{

template<bool C, class T, class... E> struct mp_if_c_impl
{
};

template<class T, class... E> struct mp_if_c_impl<true, T, E...>
{
    using type = T;
};

template<class T, class E> struct mp_if_c_impl<false, T, E>
{
    using type = E;
};

} // namespace detail

template<bool C, class T, class... E> using mp_if_c = typename detail::mp_if_c_impl<C, T, E...>::type;
template<class C, class T, class... E> using mp_if = typename detail::mp_if_c_impl<static_cast<bool>(C::value), T, E...>::type;

// mp_valid

// implementation by Bruno Dutra (by the name is_evaluable)
namespace detail
{

template<template<class...> class F, class... T> struct mp_valid_impl
{
    template<template<class...> class G, class = G<T...>> static mp_true check(int);
    template<template<class...> class> static mp_false check(...);

    using type = decltype(check<F>(0));
};

} // namespace detail

template<template<class...> class F, class... T> using mp_valid = typename detail::mp_valid_impl<F, T...>::type;

template<class Q, class... T> using mp_valid_q = mp_valid<Q::template fn, T...>;

// mp_defer
namespace detail
{

template<template<class...> class F, class... T> struct mp_defer_impl
{
    using type = F<T...>;
};

struct mp_no_type
{
};

} // namespace detail

template<template<class...> class F, class... T> using mp_defer = mp_if<mp_valid<F, T...>, detail::mp_defer_impl<F, T...>, detail::mp_no_type>;

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_DETAIL_MP_DEFER_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_RENAME_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_RENAME_HPP_INCLUDED

//  Copyright 2015-2023 Peter Dimov.
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_rename<L, B>
namespace detail
{

template<class L, template<class...> class B> struct mp_rename_impl
{
// An error "no type named 'type'" here means that the first argument to mp_rename is not a list
};

template<template<class...> class L, class... T, template<class...> class B> struct mp_rename_impl<L<T...>, B>: mp_defer<B, T...>
{
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto... A, template<class...> class B> struct mp_rename_impl<L<A...>, B>: mp_defer<B, mp_value<A>...>
{
};

#endif

} // namespace detail

template<class L, template<class...> class B> using mp_rename = typename detail::mp_rename_impl<L, B>::type;

// mp_apply<F, L>
template<template<class...> class F, class L> using mp_apply = typename detail::mp_rename_impl<L, F>::type;

// mp_apply_q<Q, L>
template<class Q, class L> using mp_apply_q = typename detail::mp_rename_impl<L, Q::template fn>::type;

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_DETAIL_MP_RENAME_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_PLUS_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_PLUS_HPP_INCLUDED

//  Copyright 2015 Peter Dimov.
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_plus
namespace detail
{

#ifdef  BOOST_MP11_HAS_FOLD_EXPRESSIONS

// msvc fails with parser stack overflow for large sizeof...(T)
// clang exceeds -fbracket-depth, which defaults to 256

template<class... T> struct mp_plus_impl
{
    static const auto _v = (T::value + ... + 0);
    using type = std::integral_constant<typename std::remove_const<decltype(_v)>::type, _v>;
};

#else

template<class... T> struct mp_plus_impl;

template<> struct mp_plus_impl<>
{
    using type = std::integral_constant<int, 0>;
};

template<class T1, class... T> struct mp_plus_impl<T1, T...>
{
    static const auto _v = T1::value + mp_plus_impl<T...>::type::value;
    using type = std::integral_constant<typename std::remove_const<decltype(_v)>::type, _v>;
};

template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class T9, class T10, class... T> struct mp_plus_impl<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T...>
{
    static const auto _v = T1::value + T2::value + T3::value + T4::value + T5::value + T6::value + T7::value + T8::value + T9::value + T10::value + mp_plus_impl<T...>::type::value;
    using type = std::integral_constant<typename std::remove_const<decltype(_v)>::type, _v>;
};

#endif

} // namespace detail

template<class... T> using mp_plus = typename detail::mp_plus_impl<T...>::type;

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_DETAIL_MP_PLUS_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_COUNT_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_COUNT_HPP_INCLUDED

//  Copyright 2015, 2016 Peter Dimov.
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_count<L, V>
namespace detail
{

#ifndef  BOOST_MP11_NO_CONSTEXPR

constexpr std::size_t cx_plus()
{
    return 0;
}

template<class T1, class... T> constexpr std::size_t cx_plus(T1 t1, T... t)
{
    return static_cast<std::size_t>(t1) + cx_plus(t...);
}

template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class T9, class T10, class... T>
constexpr std::size_t cx_plus(T1 t1, T2 t2, T3 t3, T4 t4, T5 t5, T6 t6, T7 t7, T8 t8, T9 t9, T10 t10, T... t)
{
    return static_cast<std::size_t>(t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10) + cx_plus(t...);
}

#endif

template<class L, class V> struct mp_count_impl;

#ifdef  BOOST_MP11_HAS_CXX14_CONSTEXPR

template<class V, class... T> constexpr std::size_t cx_count()
{
    constexpr bool a[] = { false, std::is_same<T, V>::value... };

    std::size_t r = 0;

    for( std::size_t i = 0; i < sizeof...(T); ++i )
    {
        r += a[ i+1 ];
    }

    return r;
}

template<template<class...> class L, class... T, class V> struct mp_count_impl<L<T...>, V>
{
    using type = mp_size_t<cx_count<V, T...>()>;
};

#elif !defined( BOOST_MP11_NO_CONSTEXPR )

template<template<class...> class L, class... T, class V> struct mp_count_impl<L<T...>, V>
{
    using type = mp_size_t<cx_plus(std::is_same<T, V>::value...)>;
};

#else

template<template<class...> class L, class... T, class V> struct mp_count_impl<L<T...>, V>
{
    using type = mp_size_t<mp_plus<std::is_same<T, V>...>::value>;
};

#endif

} // namespace detail

template<class L, class V> using mp_count = typename detail::mp_count_impl<L, V>::type;

// mp_count_if<L, P>
namespace detail
{

template<class L, template<class...> class P> struct mp_count_if_impl;

#ifdef  BOOST_MP11_HAS_CXX14_CONSTEXPR

template<template<class...> class P, class... T> constexpr std::size_t cx_count_if()
{
    constexpr bool a[] = { false, static_cast<bool>( P<T>::value )... };

    std::size_t r = 0;

    for( std::size_t i = 0; i < sizeof...(T); ++i )
    {
        r += a[ i+1 ];
    }

    return r;
}

template<template<class...> class L, class... T, template<class...> class P> struct mp_count_if_impl<L<T...>, P>
{
    using type = mp_size_t<cx_count_if<P, T...>()>;
};

#elif !defined( BOOST_MP11_NO_CONSTEXPR )

template<template<class...> class L, class... T, template<class...> class P> struct mp_count_if_impl<L<T...>, P>
{
    using type = mp_size_t<cx_plus(mp_to_bool<P<T>>::value...)>;
};

#else

template<template<class...> class L, class... T, template<class...> class P> struct mp_count_if_impl<L<T...>, P>
{

    using type = mp_size_t<mp_plus<mp_to_bool<P<T>>...>::value>;

};

#endif

} // namespace detail

template<class L, template<class...> class P> using mp_count_if = typename detail::mp_count_if_impl<L, P>::type;
template<class L, class Q> using mp_count_if_q = mp_count_if<L, Q::template fn>;

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_DETAIL_MP_COUNT_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_FOLD_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_FOLD_HPP_INCLUDED

//  Copyright 2015-2017 Peter Dimov.
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_fold<L, V, F>
namespace detail
{

template<class L, class V, template<class...> class F> struct mp_fold_impl
{
// An error "no type named 'type'" here means that the first argument to mp_fold is not a list
};

template<template<class...> class L, class V, template<class...> class F> struct mp_fold_impl<L<>, V, F>
{
    using type = V;
};

//

template<class V, template<class...> class F> struct mp_fold_Q1
{
    template<class T1>
        using fn = F<V, T1>;
};

template<class V, template<class...> class F> struct mp_fold_Q2
{
    template<class T1, class T2>
        using fn = F<F<V, T1>, T2>;
};

template<class V, template<class...> class F> struct mp_fold_Q3
{
    template<class T1, class T2, class T3>
        using fn = F<F<F<V, T1>, T2>, T3>;
};

template<class V, template<class...> class F> struct mp_fold_Q4
{
    template<class T1, class T2, class T3, class T4>
        using fn = F<F<F<F<V, T1>, T2>, T3>, T4>;
};

template<class V, template<class...> class F> struct mp_fold_Q5
{
    template<class T1, class T2, class T3, class T4, class T5>
        using fn = F<F<F<F<F<V, T1>, T2>, T3>, T4>, T5>;
};

template<class V, template<class...> class F> struct mp_fold_Q6
{
    template<class T1, class T2, class T3, class T4, class T5, class T6>
        using fn = F<F<F<F<F<F<V, T1>, T2>, T3>, T4>, T5>, T6>;
};

template<class V, template<class...> class F> struct mp_fold_Q7
{
    template<class T1, class T2, class T3, class T4, class T5, class T6, class T7>
        using fn = F<F<F<F<F<F<F<V, T1>, T2>, T3>, T4>, T5>, T6>, T7>;
};

template<class V, template<class...> class F> struct mp_fold_Q8
{
    template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8>
        using fn = F<F<F<F<F<F<F<F<V, T1>, T2>, T3>, T4>, T5>, T6>, T7>, T8>;
};

template<class V, template<class...> class F> struct mp_fold_Q9
{
    template<class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class T9>
        using fn = F<F<F<F<F<F<F<F<F<V, T1>, T2>, T3>, T4>, T5>, T6>, T7>, T8>, T9>;
};

//

template<template<class...> class L, class T1, class V, template<class...> class F>
struct mp_fold_impl<L<T1>, V, F>: mp_defer<mp_fold_Q1<V, F>::template fn, T1>
{
};

template<template<class...> class L, class T1, class T2, class V, template<class...> class F>
struct mp_fold_impl<L<T1, T2>, V, F>: mp_defer<mp_fold_Q2<V, F>::template fn, T1, T2>
{
};

template<template<class...> class L, class T1, class T2, class T3, class V, template<class...> class F>
struct mp_fold_impl<L<T1, T2, T3>, V, F>: mp_defer<mp_fold_Q3<V, F>::template fn, T1, T2, T3>
{
};

template<template<class...> class L, class T1, class T2, class T3, class T4, class V, template<class...> class F>
struct mp_fold_impl<L<T1, T2, T3, T4>, V, F>: mp_defer<mp_fold_Q4<V, F>::template fn, T1, T2, T3, T4>
{
};

template<template<class...> class L, class T1, class T2, class T3, class T4, class T5, class V, template<class...> class F>
struct mp_fold_impl<L<T1, T2, T3, T4, T5>, V, F>: mp_defer<mp_fold_Q5<V, F>::template fn, T1, T2, T3, T4, T5>
{
};

template<template<class...> class L, class T1, class T2, class T3, class T4, class T5, class T6, class V, template<class...> class F>
struct mp_fold_impl<L<T1, T2, T3, T4, T5, T6>, V, F>: mp_defer<mp_fold_Q6<V, F>::template fn, T1, T2, T3, T4, T5, T6>
{
};

template<template<class...> class L, class T1, class T2, class T3, class T4, class T5, class T6, class T7, class V, template<class...> class F>
struct mp_fold_impl<L<T1, T2, T3, T4, T5, T6, T7>, V, F>: mp_defer<mp_fold_Q7<V, F>::template fn, T1, T2, T3, T4, T5, T6, T7>
{
};

template<template<class...> class L, class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class V, template<class...> class F>
struct mp_fold_impl<L<T1, T2, T3, T4, T5, T6, T7, T8>, V, F>: mp_defer<mp_fold_Q8<V, F>::template fn, T1, T2, T3, T4, T5, T6, T7, T8>
{
};

template<template<class...> class L, class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class T9, class V, template<class...> class F>
struct mp_fold_impl<L<T1, T2, T3, T4, T5, T6, T7, T8, T9>, V, F>: mp_defer<mp_fold_Q9<V, F>::template fn, T1, T2, T3, T4, T5, T6, T7, T8, T9>
{
};

//

template<template<class...> class L, class T1, class T2, class T3, class T4, class T5, class T6, class T7, class T8, class T9, class T10, class... T, class V, template<class...> class F>
struct mp_fold_impl<L<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T...>, V, F>
{
    using type = typename mp_fold_impl<L<T...>, F<F<F<F<F<F<F<F<F<F<V, T1>, T2>, T3>, T4>, T5>, T6>, T7>, T8>, T9>, T10>, F>::type;
};

} // namespace detail

template<class L, class V, template<class...> class F> using mp_fold = typename detail::mp_fold_impl<mp_rename<L, mp_list>, V, F>::type;
template<class L, class V, class Q> using mp_fold_q = mp_fold<L, V, Q::template fn>;

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_DETAIL_MP_FOLD_HPP_INCLUDED
#ifndef BOOST_MP11_UTILITY_HPP_INCLUDED
#define BOOST_MP11_UTILITY_HPP_INCLUDED

// Copyright 2015-2020 Peter Dimov.
//
// Distributed under the Boost Software License, Version 1.0.
//
// See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_identity
template<class T> struct mp_identity
{
    using type = T;
};

// mp_identity_t
template<class T> using mp_identity_t = typename mp_identity<T>::type;

// mp_inherit
template<class... T> struct mp_inherit: T... {};

// mp_if, mp_if_c
// mp_valid
// mp_defer
//   moved to detail/mp_defer.hpp

// mp_eval_if, mp_eval_if_c
namespace detail
{

template<bool C, class T, template<class...> class F, class... U> struct mp_eval_if_c_impl;

template<class T, template<class...> class F, class... U> struct mp_eval_if_c_impl<true, T, F, U...>
{
    using type = T;
};

template<class T, template<class...> class F, class... U> struct mp_eval_if_c_impl<false, T, F, U...>: mp_defer<F, U...>
{
};

} // namespace detail

template<bool C, class T, template<class...> class F, class... U> using mp_eval_if_c = typename detail::mp_eval_if_c_impl<C, T, F, U...>::type;
template<class C, class T, template<class...> class F, class... U> using mp_eval_if = typename detail::mp_eval_if_c_impl<static_cast<bool>(C::value), T, F, U...>::type;
template<class C, class T, class Q, class... U> using mp_eval_if_q = typename detail::mp_eval_if_c_impl<static_cast<bool>(C::value), T, Q::template fn, U...>::type;

// mp_eval_if_not
template<class C, class T, template<class...> class F, class... U> using mp_eval_if_not = mp_eval_if<mp_not<C>, T, F, U...>;
template<class C, class T, class Q, class... U> using mp_eval_if_not_q = mp_eval_if<mp_not<C>, T, Q::template fn, U...>;

// mp_eval_or
template<class T, template<class...> class F, class... U> using mp_eval_or = mp_eval_if_not<mp_valid<F, U...>, T, F, U...>;
template<class T, class Q, class... U> using mp_eval_or_q = mp_eval_or<T, Q::template fn, U...>;

// mp_valid_and_true
template<template<class...> class F, class... T> using mp_valid_and_true = mp_eval_or<mp_false, F, T...>;
template<class Q, class... T> using mp_valid_and_true_q = mp_valid_and_true<Q::template fn, T...>;

// mp_cond

// so elegant; so doesn't work
// template<class C, class T, class... E> using mp_cond = mp_eval_if<C, T, mp_cond, E...>;

namespace detail
{

template<class C, class T, class... E> struct mp_cond_impl;

} // namespace detail

template<class C, class T, class... E> using mp_cond = typename detail::mp_cond_impl<C, T, E...>::type;

namespace detail
{

template<class C, class T, class... E> using mp_cond_ = mp_eval_if<C, T, mp_cond, E...>;

template<class C, class T, class... E> struct mp_cond_impl: mp_defer<mp_cond_, C, T, E...>
{
};

} // namespace detail

// mp_quote
template<template<class...> class F> struct mp_quote
{
    // the indirection through mp_defer works around the language inability
    // to expand T... into a fixed parameter list of an alias template

    template<class... T> using fn = typename mp_defer<F, T...>::type;
};

// mp_quote_trait
template<template<class...> class F> struct mp_quote_trait
{
    template<class... T> using fn = typename F<T...>::type;
};

// mp_invoke_q

template<class Q, class... T> using mp_invoke_q = typename Q::template fn<T...>;

// mp_not_fn<P>
template<template<class...> class P> struct mp_not_fn
{
    template<class... T> using fn = mp_not< mp_invoke_q<mp_quote<P>, T...> >;
};

template<class Q> using mp_not_fn_q = mp_not_fn<Q::template fn>;

// mp_compose
namespace detail
{

template<class L, class Q> using mp_compose_helper = mp_list< mp_apply_q<Q, L> >;

} // namespace detail

template<template<class...> class... F> struct mp_compose
{
    template<class... T> using fn = mp_front< mp_fold<mp_list<mp_quote<F>...>, mp_list<T...>, detail::mp_compose_helper> >;
};

template<class... Q> struct mp_compose_q
{
    template<class... T> using fn = mp_front< mp_fold<mp_list<Q...>, mp_list<T...>, detail::mp_compose_helper> >;
};

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_UTILITY_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_APPEND_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_APPEND_HPP_INCLUDED

//  Copyright 2015-2017 Peter Dimov.
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_append<L...>

namespace detail
{

// append_type_lists

template<class... L> struct mp_append_impl;

template<class L1 = mp_list<>, class L2 = mp_list<>, class L3 = mp_list<>, class L4 = mp_list<>, class L5 = mp_list<>, class L6 = mp_list<>, class L7 = mp_list<>, class L8 = mp_list<>, class L9 = mp_list<>, class L10 = mp_list<>, class L11 = mp_list<>> struct append_11_impl
{
};

template<
    template<class...> class L1, class... T1,
    template<class...> class L2, class... T2,
    template<class...> class L3, class... T3,
    template<class...> class L4, class... T4,
    template<class...> class L5, class... T5,
    template<class...> class L6, class... T6,
    template<class...> class L7, class... T7,
    template<class...> class L8, class... T8,
    template<class...> class L9, class... T9,
    template<class...> class L10, class... T10,
    template<class...> class L11, class... T11>

struct append_11_impl<L1<T1...>, L2<T2...>, L3<T3...>, L4<T4...>, L5<T5...>, L6<T6...>, L7<T7...>, L8<T8...>, L9<T9...>, L10<T10...>, L11<T11...>>
{
    using type = L1<T1..., T2..., T3..., T4..., T5..., T6..., T7..., T8..., T9..., T10..., T11...>;
};

template<

    class L00 = mp_list<>, class L01 = mp_list<>, class L02 = mp_list<>, class L03 = mp_list<>, class L04 = mp_list<>, class L05 = mp_list<>, class L06 = mp_list<>, class L07 = mp_list<>, class L08 = mp_list<>, class L09 = mp_list<>, class L0A = mp_list<>,
    class L10 = mp_list<>, class L11 = mp_list<>, class L12 = mp_list<>, class L13 = mp_list<>, class L14 = mp_list<>, class L15 = mp_list<>, class L16 = mp_list<>, class L17 = mp_list<>, class L18 = mp_list<>, class L19 = mp_list<>,
    class L20 = mp_list<>, class L21 = mp_list<>, class L22 = mp_list<>, class L23 = mp_list<>, class L24 = mp_list<>, class L25 = mp_list<>, class L26 = mp_list<>, class L27 = mp_list<>, class L28 = mp_list<>, class L29 = mp_list<>,
    class L30 = mp_list<>, class L31 = mp_list<>, class L32 = mp_list<>, class L33 = mp_list<>, class L34 = mp_list<>, class L35 = mp_list<>, class L36 = mp_list<>, class L37 = mp_list<>, class L38 = mp_list<>, class L39 = mp_list<>,
    class L40 = mp_list<>, class L41 = mp_list<>, class L42 = mp_list<>, class L43 = mp_list<>, class L44 = mp_list<>, class L45 = mp_list<>, class L46 = mp_list<>, class L47 = mp_list<>, class L48 = mp_list<>, class L49 = mp_list<>,
    class L50 = mp_list<>, class L51 = mp_list<>, class L52 = mp_list<>, class L53 = mp_list<>, class L54 = mp_list<>, class L55 = mp_list<>, class L56 = mp_list<>, class L57 = mp_list<>, class L58 = mp_list<>, class L59 = mp_list<>,
    class L60 = mp_list<>, class L61 = mp_list<>, class L62 = mp_list<>, class L63 = mp_list<>, class L64 = mp_list<>, class L65 = mp_list<>, class L66 = mp_list<>, class L67 = mp_list<>, class L68 = mp_list<>, class L69 = mp_list<>,
    class L70 = mp_list<>, class L71 = mp_list<>, class L72 = mp_list<>, class L73 = mp_list<>, class L74 = mp_list<>, class L75 = mp_list<>, class L76 = mp_list<>, class L77 = mp_list<>, class L78 = mp_list<>, class L79 = mp_list<>,
    class L80 = mp_list<>, class L81 = mp_list<>, class L82 = mp_list<>, class L83 = mp_list<>, class L84 = mp_list<>, class L85 = mp_list<>, class L86 = mp_list<>, class L87 = mp_list<>, class L88 = mp_list<>, class L89 = mp_list<>,
    class L90 = mp_list<>, class L91 = mp_list<>, class L92 = mp_list<>, class L93 = mp_list<>, class L94 = mp_list<>, class L95 = mp_list<>, class L96 = mp_list<>, class L97 = mp_list<>, class L98 = mp_list<>, class L99 = mp_list<>,
    class LA0 = mp_list<>, class LA1 = mp_list<>, class LA2 = mp_list<>, class LA3 = mp_list<>, class LA4 = mp_list<>, class LA5 = mp_list<>, class LA6 = mp_list<>, class LA7 = mp_list<>, class LA8 = mp_list<>, class LA9 = mp_list<>

> struct append_111_impl
{
    using type = typename append_11_impl<

        typename append_11_impl<L00, L01, L02, L03, L04, L05, L06, L07, L08, L09, L0A>::type,
        typename append_11_impl<mp_list<>, L10, L11, L12, L13, L14, L15, L16, L17, L18, L19>::type,
        typename append_11_impl<mp_list<>, L20, L21, L22, L23, L24, L25, L26, L27, L28, L29>::type,
        typename append_11_impl<mp_list<>, L30, L31, L32, L33, L34, L35, L36, L37, L38, L39>::type,
        typename append_11_impl<mp_list<>, L40, L41, L42, L43, L44, L45, L46, L47, L48, L49>::type,
        typename append_11_impl<mp_list<>, L50, L51, L52, L53, L54, L55, L56, L57, L58, L59>::type,
        typename append_11_impl<mp_list<>, L60, L61, L62, L63, L64, L65, L66, L67, L68, L69>::type,
        typename append_11_impl<mp_list<>, L70, L71, L72, L73, L74, L75, L76, L77, L78, L79>::type,
        typename append_11_impl<mp_list<>, L80, L81, L82, L83, L84, L85, L86, L87, L88, L89>::type,
        typename append_11_impl<mp_list<>, L90, L91, L92, L93, L94, L95, L96, L97, L98, L99>::type,
        typename append_11_impl<mp_list<>, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8, LA9>::type

    >::type;
};

template<

    class L00, class L01, class L02, class L03, class L04, class L05, class L06, class L07, class L08, class L09, class L0A,
    class L10, class L11, class L12, class L13, class L14, class L15, class L16, class L17, class L18, class L19,
    class L20, class L21, class L22, class L23, class L24, class L25, class L26, class L27, class L28, class L29,
    class L30, class L31, class L32, class L33, class L34, class L35, class L36, class L37, class L38, class L39,
    class L40, class L41, class L42, class L43, class L44, class L45, class L46, class L47, class L48, class L49,
    class L50, class L51, class L52, class L53, class L54, class L55, class L56, class L57, class L58, class L59,
    class L60, class L61, class L62, class L63, class L64, class L65, class L66, class L67, class L68, class L69,
    class L70, class L71, class L72, class L73, class L74, class L75, class L76, class L77, class L78, class L79,
    class L80, class L81, class L82, class L83, class L84, class L85, class L86, class L87, class L88, class L89,
    class L90, class L91, class L92, class L93, class L94, class L95, class L96, class L97, class L98, class L99,
    class LA0, class LA1, class LA2, class LA3, class LA4, class LA5, class LA6, class LA7, class LA8, class LA9,
    class... Lr

> struct append_inf_impl
{
    using prefix = typename append_111_impl<

        L00, L01, L02, L03, L04, L05, L06, L07, L08, L09, L0A,
        L10, L11, L12, L13, L14, L15, L16, L17, L18, L19,
        L20, L21, L22, L23, L24, L25, L26, L27, L28, L29,
        L30, L31, L32, L33, L34, L35, L36, L37, L38, L39,
        L40, L41, L42, L43, L44, L45, L46, L47, L48, L49,
        L50, L51, L52, L53, L54, L55, L56, L57, L58, L59,
        L60, L61, L62, L63, L64, L65, L66, L67, L68, L69,
        L70, L71, L72, L73, L74, L75, L76, L77, L78, L79,
        L80, L81, L82, L83, L84, L85, L86, L87, L88, L89,
        L90, L91, L92, L93, L94, L95, L96, L97, L98, L99,
        LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8, LA9

    >::type;

    using type = typename mp_append_impl<prefix, Lr...>::type;
};

template<class... L> struct mp_append_impl:
    mp_cond<
        mp_bool<(sizeof...(L) > 111)>, mp_quote<append_inf_impl>,
        mp_bool<(sizeof...(L) > 11)>, mp_quote<append_111_impl>,
        mp_true, mp_quote<append_11_impl>
    >::template fn<L...>
{
};

struct append_type_lists
{
    template<class... L> using fn = typename mp_append_impl<L...>::type;
};

// append_value_lists

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<class... L> struct append_value_impl;

template<class L1 = mp_list_v<>, class L2 = mp_list_v<>, class L3 = mp_list_v<>, class L4 = mp_list_v<>, class L5 = mp_list_v<>, class L6 = mp_list_v<>, class L7 = mp_list_v<>, class L8 = mp_list_v<>, class L9 = mp_list_v<>, class L10 = mp_list_v<>, class L11 = mp_list_v<>> struct append_value_11_impl
{
};

template<
    template<auto...> class L1, auto... T1,
    template<auto...> class L2, auto... T2,
    template<auto...> class L3, auto... T3,
    template<auto...> class L4, auto... T4,
    template<auto...> class L5, auto... T5,
    template<auto...> class L6, auto... T6,
    template<auto...> class L7, auto... T7,
    template<auto...> class L8, auto... T8,
    template<auto...> class L9, auto... T9,
    template<auto...> class L10, auto... T10,
    template<auto...> class L11, auto... T11>

struct append_value_11_impl<L1<T1...>, L2<T2...>, L3<T3...>, L4<T4...>, L5<T5...>, L6<T6...>, L7<T7...>, L8<T8...>, L9<T9...>, L10<T10...>, L11<T11...>>
{
    using type = L1<T1..., T2..., T3..., T4..., T5..., T6..., T7..., T8..., T9..., T10..., T11...>;
};

template<

    class L00 = mp_list_v<>, class L01 = mp_list_v<>, class L02 = mp_list_v<>, class L03 = mp_list_v<>, class L04 = mp_list_v<>, class L05 = mp_list_v<>, class L06 = mp_list_v<>, class L07 = mp_list_v<>, class L08 = mp_list_v<>, class L09 = mp_list_v<>, class L0A = mp_list_v<>,
    class L10 = mp_list_v<>, class L11 = mp_list_v<>, class L12 = mp_list_v<>, class L13 = mp_list_v<>, class L14 = mp_list_v<>, class L15 = mp_list_v<>, class L16 = mp_list_v<>, class L17 = mp_list_v<>, class L18 = mp_list_v<>, class L19 = mp_list_v<>,
    class L20 = mp_list_v<>, class L21 = mp_list_v<>, class L22 = mp_list_v<>, class L23 = mp_list_v<>, class L24 = mp_list_v<>, class L25 = mp_list_v<>, class L26 = mp_list_v<>, class L27 = mp_list_v<>, class L28 = mp_list_v<>, class L29 = mp_list_v<>,
    class L30 = mp_list_v<>, class L31 = mp_list_v<>, class L32 = mp_list_v<>, class L33 = mp_list_v<>, class L34 = mp_list_v<>, class L35 = mp_list_v<>, class L36 = mp_list_v<>, class L37 = mp_list_v<>, class L38 = mp_list_v<>, class L39 = mp_list_v<>,
    class L40 = mp_list_v<>, class L41 = mp_list_v<>, class L42 = mp_list_v<>, class L43 = mp_list_v<>, class L44 = mp_list_v<>, class L45 = mp_list_v<>, class L46 = mp_list_v<>, class L47 = mp_list_v<>, class L48 = mp_list_v<>, class L49 = mp_list_v<>,
    class L50 = mp_list_v<>, class L51 = mp_list_v<>, class L52 = mp_list_v<>, class L53 = mp_list_v<>, class L54 = mp_list_v<>, class L55 = mp_list_v<>, class L56 = mp_list_v<>, class L57 = mp_list_v<>, class L58 = mp_list_v<>, class L59 = mp_list_v<>,
    class L60 = mp_list_v<>, class L61 = mp_list_v<>, class L62 = mp_list_v<>, class L63 = mp_list_v<>, class L64 = mp_list_v<>, class L65 = mp_list_v<>, class L66 = mp_list_v<>, class L67 = mp_list_v<>, class L68 = mp_list_v<>, class L69 = mp_list_v<>,
    class L70 = mp_list_v<>, class L71 = mp_list_v<>, class L72 = mp_list_v<>, class L73 = mp_list_v<>, class L74 = mp_list_v<>, class L75 = mp_list_v<>, class L76 = mp_list_v<>, class L77 = mp_list_v<>, class L78 = mp_list_v<>, class L79 = mp_list_v<>,
    class L80 = mp_list_v<>, class L81 = mp_list_v<>, class L82 = mp_list_v<>, class L83 = mp_list_v<>, class L84 = mp_list_v<>, class L85 = mp_list_v<>, class L86 = mp_list_v<>, class L87 = mp_list_v<>, class L88 = mp_list_v<>, class L89 = mp_list_v<>,
    class L90 = mp_list_v<>, class L91 = mp_list_v<>, class L92 = mp_list_v<>, class L93 = mp_list_v<>, class L94 = mp_list_v<>, class L95 = mp_list_v<>, class L96 = mp_list_v<>, class L97 = mp_list_v<>, class L98 = mp_list_v<>, class L99 = mp_list_v<>,
    class LA0 = mp_list_v<>, class LA1 = mp_list_v<>, class LA2 = mp_list_v<>, class LA3 = mp_list_v<>, class LA4 = mp_list_v<>, class LA5 = mp_list_v<>, class LA6 = mp_list_v<>, class LA7 = mp_list_v<>, class LA8 = mp_list_v<>, class LA9 = mp_list_v<>

> struct append_value_111_impl
{
    using type = typename append_value_11_impl<

        typename append_value_11_impl<L00, L01, L02, L03, L04, L05, L06, L07, L08, L09, L0A>::type,
        typename append_value_11_impl<mp_list_v<>, L10, L11, L12, L13, L14, L15, L16, L17, L18, L19>::type,
        typename append_value_11_impl<mp_list_v<>, L20, L21, L22, L23, L24, L25, L26, L27, L28, L29>::type,
        typename append_value_11_impl<mp_list_v<>, L30, L31, L32, L33, L34, L35, L36, L37, L38, L39>::type,
        typename append_value_11_impl<mp_list_v<>, L40, L41, L42, L43, L44, L45, L46, L47, L48, L49>::type,
        typename append_value_11_impl<mp_list_v<>, L50, L51, L52, L53, L54, L55, L56, L57, L58, L59>::type,
        typename append_value_11_impl<mp_list_v<>, L60, L61, L62, L63, L64, L65, L66, L67, L68, L69>::type,
        typename append_value_11_impl<mp_list_v<>, L70, L71, L72, L73, L74, L75, L76, L77, L78, L79>::type,
        typename append_value_11_impl<mp_list_v<>, L80, L81, L82, L83, L84, L85, L86, L87, L88, L89>::type,
        typename append_value_11_impl<mp_list_v<>, L90, L91, L92, L93, L94, L95, L96, L97, L98, L99>::type,
        typename append_value_11_impl<mp_list_v<>, LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8, LA9>::type

    >::type;
};

template<

    class L00, class L01, class L02, class L03, class L04, class L05, class L06, class L07, class L08, class L09, class L0A,
    class L10, class L11, class L12, class L13, class L14, class L15, class L16, class L17, class L18, class L19,
    class L20, class L21, class L22, class L23, class L24, class L25, class L26, class L27, class L28, class L29,
    class L30, class L31, class L32, class L33, class L34, class L35, class L36, class L37, class L38, class L39,
    class L40, class L41, class L42, class L43, class L44, class L45, class L46, class L47, class L48, class L49,
    class L50, class L51, class L52, class L53, class L54, class L55, class L56, class L57, class L58, class L59,
    class L60, class L61, class L62, class L63, class L64, class L65, class L66, class L67, class L68, class L69,
    class L70, class L71, class L72, class L73, class L74, class L75, class L76, class L77, class L78, class L79,
    class L80, class L81, class L82, class L83, class L84, class L85, class L86, class L87, class L88, class L89,
    class L90, class L91, class L92, class L93, class L94, class L95, class L96, class L97, class L98, class L99,
    class LA0, class LA1, class LA2, class LA3, class LA4, class LA5, class LA6, class LA7, class LA8, class LA9,
    class... Lr

> struct append_value_inf_impl
{
    using prefix = typename append_value_111_impl<

        L00, L01, L02, L03, L04, L05, L06, L07, L08, L09, L0A,
        L10, L11, L12, L13, L14, L15, L16, L17, L18, L19,
        L20, L21, L22, L23, L24, L25, L26, L27, L28, L29,
        L30, L31, L32, L33, L34, L35, L36, L37, L38, L39,
        L40, L41, L42, L43, L44, L45, L46, L47, L48, L49,
        L50, L51, L52, L53, L54, L55, L56, L57, L58, L59,
        L60, L61, L62, L63, L64, L65, L66, L67, L68, L69,
        L70, L71, L72, L73, L74, L75, L76, L77, L78, L79,
        L80, L81, L82, L83, L84, L85, L86, L87, L88, L89,
        L90, L91, L92, L93, L94, L95, L96, L97, L98, L99,
        LA0, LA1, LA2, LA3, LA4, LA5, LA6, LA7, LA8, LA9

    >::type;

    using type = typename append_value_impl<prefix, Lr...>::type;
};

template<class... L> struct append_value_impl:
    mp_cond<
        mp_bool<(sizeof...(L) > 111)>, mp_quote<append_value_inf_impl>,
        mp_bool<(sizeof...(L) > 11)>, mp_quote<append_value_111_impl>,
        mp_true, mp_quote<append_value_11_impl>
    >::template fn<L...>
{
};

struct append_value_lists
{
    template<class... L> using fn = typename append_value_impl<L...>::type;
};

#endif // #if defined(BOOST_MP11_HAS_TEMPLATE_AUTO)

} // namespace detail

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<class... L> using mp_append = typename mp_if_c<(sizeof...(L) > 0 && sizeof...(L) == mp_count_if<mp_list<L...>, mp_is_value_list>::value), detail::append_value_lists, detail::append_type_lists>::template fn<L...>;

#else

template<class... L> using mp_append = detail::append_type_lists::fn<L...>;

#endif

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_DETAIL_MP_APPEND_HPP_INCLUDED
#ifndef BOOST_MP11_LIST_HPP_INCLUDED
#define BOOST_MP11_LIST_HPP_INCLUDED

//  Copyright 2015-2023 Peter Dimov.
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

#if defined(_MSC_VER) || defined(__GNUC__)
# pragma push_macro( "I" )
# undef I
#endif

namespace boost
{
namespace mp11
{

// mp_list<T...>
//   in detail/mp_list.hpp

// mp_list_c<T, I...>
template<class T, T... I> using mp_list_c = mp_list<std::integral_constant<T, I>...>;

// mp_list_v<A...>
//   in detail/mp_list_v.hpp

// mp_is_list<L>
//   in detail/mp_is_list.hpp

// mp_is_value_list<L>
//   in detail/mp_is_value_list.hpp

// mp_size<L>
namespace detail
{

template<class L> struct mp_size_impl
{
// An error "no type named 'type'" here means that the argument to mp_size is not a list
};

template<template<class...> class L, class... T> struct mp_size_impl<L<T...>>
{
    using type = mp_size_t<sizeof...(T)>;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto... A> struct mp_size_impl<L<A...>>
{
    using type = mp_size_t<sizeof...(A)>;
};

#endif

} // namespace detail

template<class L> using mp_size = typename detail::mp_size_impl<L>::type;

// mp_empty<L>
template<class L> using mp_empty = mp_bool< mp_size<L>::value == 0 >;

// mp_assign<L1, L2>
namespace detail
{

template<class L1, class L2> struct mp_assign_impl
{
// An error "no type named 'type'" here means that the arguments to mp_assign aren't lists
};

template<template<class...> class L1, class... T, template<class...> class L2, class... U> struct mp_assign_impl<L1<T...>, L2<U...>>
{
    using type = L1<U...>;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L1, auto... A, template<class...> class L2, class... U> struct mp_assign_impl<L1<A...>, L2<U...>>
{
    using type = L1<U::value...>;
};

template<template<class...> class L1, class... T, template<auto...> class L2, auto... B> struct mp_assign_impl<L1<T...>, L2<B...>>
{
    using type = L1<mp_value<B>...>;
};

template<template<auto...> class L1, auto... A, template<auto...> class L2, auto... B> struct mp_assign_impl<L1<A...>, L2<B...>>
{
    using type = L1<B...>;
};

#endif

} // namespace detail

template<class L1, class L2> using mp_assign = typename detail::mp_assign_impl<L1, L2>::type;

// mp_clear<L>
template<class L> using mp_clear = mp_assign<L, mp_list<>>;

// mp_front<L>
//   in detail/mp_front.hpp

// mp_pop_front<L>
namespace detail
{

template<class L> struct mp_pop_front_impl
{
// An error "no type named 'type'" here means that the argument to mp_pop_front
// is either not a list, or is an empty list
};

template<template<class...> class L, class T1, class... T> struct mp_pop_front_impl<L<T1, T...>>
{
    using type = L<T...>;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto A1, auto... A> struct mp_pop_front_impl<L<A1, A...>>
{
    using type = L<A...>;
};

#endif

} // namespace detail

template<class L> using mp_pop_front = typename detail::mp_pop_front_impl<L>::type;

// mp_first<L>
template<class L> using mp_first = mp_front<L>;

// mp_rest<L>
template<class L> using mp_rest = mp_pop_front<L>;

// mp_second<L>
namespace detail
{

template<class L> struct mp_second_impl
{
// An error "no type named 'type'" here means that the argument to mp_second
// is either not a list, or has fewer than two elements
};

template<template<class...> class L, class T1, class T2, class... T> struct mp_second_impl<L<T1, T2, T...>>
{
    using type = T2;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto A1, auto A2, auto... A> struct mp_second_impl<L<A1, A2, A...>>
{
    using type = mp_value<A2>;
};

#endif

} // namespace detail

template<class L> using mp_second = typename detail::mp_second_impl<L>::type;

// mp_third<L>
namespace detail
{

template<class L> struct mp_third_impl
{
// An error "no type named 'type'" here means that the argument to mp_third
// is either not a list, or has fewer than three elements
};

template<template<class...> class L, class T1, class T2, class T3, class... T> struct mp_third_impl<L<T1, T2, T3, T...>>
{
    using type = T3;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto A1, auto A2, auto A3, auto... A> struct mp_third_impl<L<A1, A2, A3, A...>>
{
    using type = mp_value<A3>;
};

#endif

} // namespace detail

template<class L> using mp_third = typename detail::mp_third_impl<L>::type;

// mp_push_front<L, T...>
namespace detail
{

template<class L, class... T> struct mp_push_front_impl
{
// An error "no type named 'type'" here means that the first argument to mp_push_front is not a list
};

template<template<class...> class L, class... U, class... T> struct mp_push_front_impl<L<U...>, T...>
{
    using type = L<T..., U...>;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto... A, class... T> struct mp_push_front_impl<L<A...>, T...>
{
    using type = L<T::value..., A...>;
};

#endif

} // namespace detail

template<class L, class... T> using mp_push_front = typename detail::mp_push_front_impl<L, T...>::type;

// mp_push_back<L, T...>
namespace detail
{

template<class L, class... T> struct mp_push_back_impl
{
// An error "no type named 'type'" here means that the first argument to mp_push_back is not a list
};

template<template<class...> class L, class... U, class... T> struct mp_push_back_impl<L<U...>, T...>
{
    using type = L<U..., T...>;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto... A, class... T> struct mp_push_back_impl<L<A...>, T...>
{
    using type = L<A..., T::value...>;
};

#endif

} // namespace detail

template<class L, class... T> using mp_push_back = typename detail::mp_push_back_impl<L, T...>::type;

// mp_rename<L, B>
// mp_apply<F, L>
// mp_apply_q<Q, L>
//   in detail/mp_rename.hpp

// mp_rename_v<L, B>
#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

namespace detail
{

template<class L, template<auto...> class B> struct mp_rename_v_impl
{
// An error "no type named 'type'" here means that the first argument to mp_rename_v is not a list
};

template<template<class...> class L, class... T, template<auto...> class B> struct mp_rename_v_impl<L<T...>, B>
{
    using type = B<T::value...>;
};

template<template<auto...> class L, auto... A, template<auto...> class B> struct mp_rename_v_impl<L<A...>, B>
{
    using type = B<A...>;
};

} // namespace detail

template<class L, template<auto...> class B> using mp_rename_v = typename detail::mp_rename_v_impl<L, B>::type;

#endif

// mp_replace_front<L, T>
namespace detail
{

template<class L, class T> struct mp_replace_front_impl
{
// An error "no type named 'type'" here means that the first argument to mp_replace_front
// is either not a list, or is an empty list
};

template<template<class...> class L, class U1, class... U, class T> struct mp_replace_front_impl<L<U1, U...>, T>
{
    using type = L<T, U...>;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto A1, auto... A, class T> struct mp_replace_front_impl<L<A1, A...>, T>
{
    using type = L<T::value, A...>;
};

#endif

} // namespace detail

template<class L, class T> using mp_replace_front = typename detail::mp_replace_front_impl<L, T>::type;

// mp_replace_first<L, T>
template<class L, class T> using mp_replace_first = typename detail::mp_replace_front_impl<L, T>::type;

// mp_replace_second<L, T>
namespace detail
{

template<class L, class T> struct mp_replace_second_impl
{
// An error "no type named 'type'" here means that the first argument to mp_replace_second
// is either not a list, or has fewer than two elements
};

template<template<class...> class L, class U1, class U2, class... U, class T> struct mp_replace_second_impl<L<U1, U2, U...>, T>
{
    using type = L<U1, T, U...>;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto A1, auto A2, auto... A, class T> struct mp_replace_second_impl<L<A1, A2, A...>, T>
{
    using type = L<A1, T::value, A...>;
};

#endif

} // namespace detail

template<class L, class T> using mp_replace_second = typename detail::mp_replace_second_impl<L, T>::type;

// mp_replace_third<L, T>
namespace detail
{

template<class L, class T> struct mp_replace_third_impl
{
// An error "no type named 'type'" here means that the first argument to mp_replace_third
// is either not a list, or has fewer than three elements
};

template<template<class...> class L, class U1, class U2, class U3, class... U, class T> struct mp_replace_third_impl<L<U1, U2, U3, U...>, T>
{
    using type = L<U1, U2, T, U...>;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto A1, auto A2, auto A3, auto... A, class T> struct mp_replace_third_impl<L<A1, A2, A3, A...>, T>
{
    using type = L<A1, A2, T::value, A...>;
};

#endif

} // namespace detail

template<class L, class T> using mp_replace_third = typename detail::mp_replace_third_impl<L, T>::type;

// mp_transform_front<L, F>
namespace detail
{

template<class L, template<class...> class F> struct mp_transform_front_impl
{
// An error "no type named 'type'" here means that the first argument to mp_transform_front
// is either not a list, or is an empty list
};

template<template<class...> class L, class U1, class... U, template<class...> class F> struct mp_transform_front_impl<L<U1, U...>, F>
{
    using type = L<F<U1>, U...>;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto A1, auto... A, template<class...> class F> struct mp_transform_front_impl<L<A1, A...>, F>
{
    using type = L<F<mp_value<A1>>::value, A...>;
};

#endif

} // namespace detail

template<class L, template<class...> class F> using mp_transform_front = typename detail::mp_transform_front_impl<L, F>::type;
template<class L, class Q> using mp_transform_front_q = mp_transform_front<L, Q::template fn>;

// mp_transform_first<L, F>
template<class L, template<class...> class F> using mp_transform_first = typename detail::mp_transform_front_impl<L, F>::type;
template<class L, class Q> using mp_transform_first_q = mp_transform_first<L, Q::template fn>;

// mp_transform_second<L, F>
namespace detail
{

template<class L, template<class...> class F> struct mp_transform_second_impl
{
// An error "no type named 'type'" here means that the first argument to mp_transform_second
// is either not a list, or has fewer than two elements
};

template<template<class...> class L, class U1, class U2, class... U, template<class...> class F> struct mp_transform_second_impl<L<U1, U2, U...>, F>
{
    using type = L<U1, F<U2>, U...>;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto A1, auto A2, auto... A, template<class...> class F> struct mp_transform_second_impl<L<A1, A2, A...>, F>
{
    using type = L<A1, F<mp_value<A2>>::value, A...>;
};

#endif

} // namespace detail

template<class L, template<class...> class F> using mp_transform_second = typename detail::mp_transform_second_impl<L, F>::type;
template<class L, class Q> using mp_transform_second_q = mp_transform_second<L, Q::template fn>;

// mp_transform_third<L, F>
namespace detail
{

template<class L, template<class...> class F> struct mp_transform_third_impl
{
// An error "no type named 'type'" here means that the first argument to mp_transform_third
// is either not a list, or has fewer than three elements
};

template<template<class...> class L, class U1, class U2, class U3, class... U, template<class...> class F> struct mp_transform_third_impl<L<U1, U2, U3, U...>, F>
{
    using type = L<U1, U2, F<U3>, U...>;
};

#ifdef BOOST_MP11_HAS_TEMPLATE_AUTO

template<template<auto...> class L, auto A1, auto A2, auto A3, auto... A, template<class...> class F> struct mp_transform_third_impl<L<A1, A2, A3, A...>, F>
{
    using type = L<A1, A2, F<mp_value<A3>>::value, A...>;
};

#endif

} // namespace detail

template<class L, template<class...> class F> using mp_transform_third = typename detail::mp_transform_third_impl<L, F>::type;
template<class L, class Q> using mp_transform_third_q = mp_transform_third<L, Q::template fn>;

} // namespace mp11
} // namespace boost

#if defined(_MSC_VER) || defined(__GNUC__)
# pragma pop_macro( "I" )
#endif

#endif // #ifndef BOOST_MP11_LIST_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_MIN_ELEMENT_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_MIN_ELEMENT_HPP_INCLUDED

//  Copyright 2015-2017 Peter Dimov.
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_min_element<L, P>
namespace detail
{

template<template<class...> class P> struct select_min
{
    template<class T1, class T2> using fn = mp_if<P<T1, T2>, T1, T2>;
};

} // namespace detail

template<class L, template<class...> class P> using mp_min_element = mp_fold_q<mp_rest<L>, mp_first<L>, detail::select_min<P>>;
template<class L, class Q> using mp_min_element_q = mp_min_element<L, Q::template fn>;

// mp_max_element<L, P>
namespace detail
{

template<template<class...> class P> struct select_max
{
    template<class T1, class T2> using fn = mp_if<P<T2, T1>, T1, T2>;
};

} // namespace detail

template<class L, template<class...> class P> using mp_max_element = mp_fold_q<mp_rest<L>, mp_first<L>, detail::select_max<P>>;
template<class L, class Q> using mp_max_element_q = mp_max_element<L, Q::template fn>;

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_DETAIL_MP_MIN_ELEMENT_HPP_INCLUDED
#ifndef BOOST_MP11_DETAIL_MP_VOID_HPP_INCLUDED
#define BOOST_MP11_DETAIL_MP_VOID_HPP_INCLUDED

//  Copyright 2015-2017 Peter Dimov.
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_void<T...>
namespace detail
{

template<class... T> struct mp_void_impl
{
    using type = void;
};

} // namespace detail

template<class... T> using mp_void = typename detail::mp_void_impl<T...>::type;

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_DETAIL_MP_VOID_HPP_INCLUDED
#ifndef BOOST_MP11_FUNCTION_HPP_INCLUDED
#define BOOST_MP11_FUNCTION_HPP_INCLUDED

// Copyright 2015-2019 Peter Dimov.
//
// Distributed under the Boost Software License, Version 1.0.
//
// See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace mp11
{

// mp_void<T...>
//   in detail/mp_void.hpp

// mp_and<T...>

namespace detail
{

template<class L, class E = void> struct mp_and_impl
{
    using type = mp_false;
};

template<class... T> struct mp_and_impl< mp_list<T...>, mp_void<mp_if<T, void>...> >
{
    using type = mp_true;
};

} // namespace detail

template<class... T> using mp_and = typename detail::mp_and_impl<mp_list<T...>>::type;

// mp_all<T...>
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=86355

template<class... T> using mp_all = mp_bool< mp_count< mp_list<mp_to_bool<T>...>, mp_false >::value == 0 >;

// mp_or<T...>
namespace detail
{

template<class... T> struct mp_or_impl;

} // namespace detail

template<class... T> using mp_or = mp_to_bool< typename detail::mp_or_impl<T...>::type >;

namespace detail
{

template<> struct mp_or_impl<>
{
    using type = mp_false;
};

template<class T> struct mp_or_impl<T>
{
    using type = T;
};

template<class T1, class... T> struct mp_or_impl<T1, T...>
{
    using type = mp_eval_if< T1, T1, mp_or, T... >;
};

} // namespace detail

// mp_any<T...>
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=86356

template<class... T> using mp_any = mp_bool< mp_count< mp_list<mp_to_bool<T>...>, mp_true >::value != 0 >;

// mp_same<T...>
namespace detail
{

template<class... T> struct mp_same_impl;

template<> struct mp_same_impl<>
{
    using type = mp_true;
};

template<class T1, class... T> struct mp_same_impl<T1, T...>
{
    using type = mp_bool< mp_count<mp_list<T...>, T1>::value == sizeof...(T) >;
};

} // namespace detail

template<class... T> using mp_same = typename detail::mp_same_impl<T...>::type;

// mp_similar<T...>
namespace detail
{

template<class... T> struct mp_similar_impl;

template<> struct mp_similar_impl<>
{
    using type = mp_true;
};

template<class T> struct mp_similar_impl<T>
{
    using type = mp_true;
};

template<class T> struct mp_similar_impl<T, T>
{
    using type = mp_true;
};

template<class T1, class T2> struct mp_similar_impl<T1, T2>
{
    using type = mp_false;
};

template<template<class...> class L, class... T1, class... T2> struct mp_similar_impl<L<T1...>, L<T2...>>
{
    using type = mp_true;
};

template<template<class...> class L, class... T> struct mp_similar_impl<L<T...>, L<T...>>
{
    using type = mp_true;
};

template<class T1, class T2, class T3, class... T> struct mp_similar_impl<T1, T2, T3, T...>
{
    using type = mp_all< typename mp_similar_impl<T1, T2>::type, typename mp_similar_impl<T1, T3>::type, typename mp_similar_impl<T1, T>::type... >;
};

} // namespace detail

template<class... T> using mp_similar = typename detail::mp_similar_impl<T...>::type;

#if BOOST_MP11_GCC
# pragma GCC diagnostic push
# pragma GCC diagnostic ignored "-Wsign-compare"
#endif

// mp_less<T1, T2>
template<class T1, class T2> using mp_less = mp_bool<(T1::value < 0 && T2::value >= 0) || ((T1::value < T2::value) && !(T1::value >= 0 && T2::value < 0))>;

#if BOOST_MP11_GCC
# pragma GCC diagnostic pop
#endif

// mp_min<T...>
template<class T1, class... T> using mp_min = mp_min_element<mp_list<T1, T...>, mp_less>;

// mp_max<T...>
template<class T1, class... T> using mp_max = mp_max_element<mp_list<T1, T...>, mp_less>;

} // namespace mp11
} // namespace boost

#endif // #ifndef BOOST_MP11_FUNCTION_HPP_INCLUDED
#ifndef BOOST_MP11_TUPLE_HPP_INCLUDED
#define BOOST_MP11_TUPLE_HPP_INCLUDED

//  Copyright 2015-2020 Peter Dimov.
//
//  Distributed under the Boost Software License, Version 1.0.
//
//  See accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt

#if BOOST_MP11_MSVC
# pragma warning( push )
# pragma warning( disable: 4100 ) // unreferenced formal parameter 'tp'
#endif

namespace boost
{
namespace mp11
{

// tuple_apply
namespace detail
{

using std::get;

template<class F, class Tp, std::size_t... J> BOOST_MP11_CONSTEXPR auto tuple_apply_impl( F && f, Tp && tp, integer_sequence<std::size_t, J...> )
    -> decltype( std::forward<F>(f)( get<J>(std::forward<Tp>(tp))... ) )
{
    return std::forward<F>(f)( get<J>(std::forward<Tp>(tp))... );
}

} // namespace detail

template<class F, class Tp,
    class Seq = make_index_sequence<std::tuple_size<typename std::remove_reference<Tp>::type>::value>>
BOOST_MP11_CONSTEXPR auto tuple_apply( F && f, Tp && tp )
    -> decltype( detail::tuple_apply_impl( std::forward<F>(f), std::forward<Tp>(tp), Seq() ) )
{
    return detail::tuple_apply_impl( std::forward<F>(f), std::forward<Tp>(tp), Seq() );
}

// construct_from_tuple
namespace detail
{

template<class T, class Tp, std::size_t... J> BOOST_MP11_CONSTEXPR T construct_from_tuple_impl( Tp && tp, integer_sequence<std::size_t, J...> )
{
    return T( get<J>(std::forward<Tp>(tp))... );
}

} // namespace detail

template<class T, class Tp,
    class Seq = make_index_sequence<std::tuple_size<typename std::remove_reference<Tp>::type>::value>>
BOOST_MP11_CONSTEXPR T construct_from_tuple( Tp && tp )
{
    return detail::construct_from_tuple_impl<T>( std::forward<Tp>(tp), Seq() );
}

// tuple_for_each
namespace detail
{

template<class Tp, std::size_t... J, class F> BOOST_MP11_CONSTEXPR F tuple_for_each_impl( Tp && tp, integer_sequence<std::size_t, J...>, F && f )
{
    using A = int[sizeof...(J)];
    return (void)A{ ((void)f(get<J>(std::forward<Tp>(tp))), 0)... }, std::forward<F>(f);
}

template<class Tp, class F> BOOST_MP11_CONSTEXPR F tuple_for_each_impl( Tp && /*tp*/, integer_sequence<std::size_t>, F && f )
{
    return std::forward<F>(f);
}

} // namespace detail

template<class Tp, class F> BOOST_MP11_CONSTEXPR F tuple_for_each( Tp && tp, F && f )
{
    using seq = make_index_sequence<std::tuple_size<typename std::remove_reference<Tp>::type>::value>;
    return detail::tuple_for_each_impl( std::forward<Tp>(tp), seq(), std::forward<F>(f) );
}

// tuple_transform

namespace detail
{

// std::forward_as_tuple is not constexpr in C++11 or libstdc++ 5.x
template<class... T> BOOST_MP11_CONSTEXPR auto tp_forward_r( T&&... t ) -> std::tuple<T&&...>
{
    return std::tuple<T&&...>( std::forward<T>( t )... );
}

template<class... T> BOOST_MP11_CONSTEXPR auto tp_forward_v( T&&... t ) -> std::tuple<T...>
{
    return std::tuple<T...>( std::forward<T>( t )... );
}

template<std::size_t J, class... Tp>
BOOST_MP11_CONSTEXPR auto tp_extract( Tp&&... tp )
    -> decltype( tp_forward_r( get<J>( std::forward<Tp>( tp ) )... ) )
{
    return tp_forward_r( get<J>( std::forward<Tp>( tp ) )... );
}

template<class F, class... Tp, std::size_t... J>
BOOST_MP11_CONSTEXPR auto tuple_transform_impl( integer_sequence<std::size_t, J...>, F const& f, Tp&&... tp )
    -> decltype( tp_forward_v( tuple_apply( f, tp_extract<J>( std::forward<Tp>(tp)... ) )... ) )
{
    return tp_forward_v( tuple_apply( f, tp_extract<J>( std::forward<Tp>(tp)... ) )... );
}

} // namespace detail

template<class F, class... Tp,
    class Z = mp_list<mp_size_t<std::tuple_size<typename std::remove_reference<Tp>::type>::value>...>,
    class E = mp_if<mp_apply<mp_same, Z>, mp_front<Z>>,
    class Seq = make_index_sequence<E::value>>
BOOST_MP11_CONSTEXPR auto tuple_transform( F const& f, Tp&&... tp )
    -> decltype( detail::tuple_transform_impl( Seq(), f, std::forward<Tp>(tp)... ) )
{
    return detail::tuple_transform_impl( Seq(), f, std::forward<Tp>(tp)... );
}

} // namespace mp11
} // namespace boost

#if BOOST_MP11_MSVC
# pragma warning( pop )
#endif

#endif // #ifndef BOOST_TUPLE_HPP_INCLUDED
#ifndef BOOST_CORE_DETAIL_SP_THREAD_PAUSE_HPP_INCLUDED
#define BOOST_CORE_DETAIL_SP_THREAD_PAUSE_HPP_INCLUDED

// MS compatible compilers support #pragma once

#if defined(_MSC_VER) && (_MSC_VER >= 1020)
# pragma once
#endif

// boost/core/detail/sp_thread_pause.hpp
//
// inline void bost::core::sp_thread_pause();
//
//   Emits a "pause" instruction.
//
// Copyright 2008, 2020, 2023 Peter Dimov
// Distributed under the Boost Software License, Version 1.0
// https://www.boost.org/LICENSE_1_0.txt

#ifdef __has_builtin
# if __has_builtin(__builtin_ia32_pause) && !defined(__INTEL_COMPILER)
#  define BOOST_CORE_HAS_BUILTIN_IA32_PAUSE
# endif
#endif

#ifdef BOOST_CORE_HAS_BUILTIN_IA32_PAUSE

# define BOOST_CORE_SP_PAUSE() __builtin_ia32_pause()

#elif defined(_MSC_VER) && ( defined(_M_IX86) || defined(_M_X64) )

# include <intrin.h>
# define BOOST_CORE_SP_PAUSE() _mm_pause()

#elif defined(_MSC_VER) && ( defined(_M_ARM) || defined(_M_ARM64) )

# include <intrin.h>
# define BOOST_CORE_SP_PAUSE() __yield()

#elif defined(__GNUC__) && ( defined(__i386__) || defined(__x86_64__) )

# define BOOST_CORE_SP_PAUSE() __asm__ __volatile__( "rep; nop" : : : "memory" )

#elif defined(__GNUC__) && ( (defined(__ARM_ARCH) && __ARM_ARCH >= 8) || defined(__ARM_ARCH_8A__) || defined(__aarch64__) )

# define BOOST_CORE_SP_PAUSE() __asm__ __volatile__( "yield" : : : "memory" )

#else

# define BOOST_CORE_SP_PAUSE() ((void)0)

#endif

namespace boost
{
namespace core
{

BOOST_FORCEINLINE void sp_thread_pause() noexcept
{
    BOOST_CORE_SP_PAUSE();
}

} // namespace core
} // namespace boost

#undef BOOST_CORE_SP_PAUSE

#endif // #ifndef BOOST_CORE_DETAIL_SP_THREAD_PAUSE_HPP_INCLUDED
#ifndef BOOST_CORE_DETAIL_SP_WIN32_SLEEP_HPP_INCLUDED
#define BOOST_CORE_DETAIL_SP_WIN32_SLEEP_HPP_INCLUDED

// MS compatible compilers support #pragma once

#if defined(_MSC_VER) && (_MSC_VER >= 1020)
# pragma once
#endif

// boost/core/detail/sp_win32_sleep.hpp
//
// Declares the Win32 Sleep() function.
//
// Copyright 2008, 2020 Peter Dimov
// Distributed under the Boost Software License, Version 1.0
// https://www.boost.org/LICENSE_1_0.txt

#    if defined(_WIN32) || defined(__WIN32__) || defined(__CYGWIN__)

#ifdef  BOOST_USE_WINDOWS_H
# include <windows.h>
#endif

namespace boost
{
namespace core
{
namespace detail
{

#ifndef  BOOST_USE_WINDOWS_H

#if defined(__clang__) && defined(__x86_64__)
// clang x64 warns that __stdcall is ignored
# define BOOST_CORE_SP_STDCALL
#else
# define BOOST_CORE_SP_STDCALL __stdcall
#endif

#ifdef __LP64__ // Cygwin 64
  extern "C" __declspec(dllimport) void BOOST_CORE_SP_STDCALL Sleep( unsigned int ms );
#else
  extern "C" __declspec(dllimport) void BOOST_CORE_SP_STDCALL Sleep( unsigned long ms );
#endif

extern "C" __declspec(dllimport) int BOOST_CORE_SP_STDCALL SwitchToThread();

#undef BOOST_CORE_SP_STDCALL

#endif // !defined( BOOST_USE_WINDOWS_H )

} // namespace detail
} // namespace core
} // namespace boost

#endif

#endif // #ifndef BOOST_CORE_DETAIL_SP_WIN32_SLEEP_HPP_INCLUDED
#ifndef BOOST_CORE_DETAIL_SP_THREAD_YIELD_HPP_INCLUDED
#define BOOST_CORE_DETAIL_SP_THREAD_YIELD_HPP_INCLUDED

// MS compatible compilers support #pragma once

#if defined(_MSC_VER) && (_MSC_VER >= 1020)
# pragma once
#endif

// boost/core/detail/sp_thread_yield.hpp
//
// inline void bost::core::sp_thread_yield();
//
//   Gives up the remainder of the time slice,
//   as if by calling sched_yield().
//
// Copyright 2008, 2020 Peter Dimov
// Distributed under the Boost Software License, Version 1.0
// https://www.boost.org/LICENSE_1_0.txt

#if defined( _WIN32 ) || defined( __WIN32__ ) || defined( __CYGWIN__ )

#ifdef BOOST_SP_REPORT_IMPLEMENTATION
  BOOST_PRAGMA_MESSAGE("Using SwitchToThread() in sp_thread_yield")
#endif

namespace boost
{
namespace core
{
namespace detail
{

inline void sp_thread_yield() noexcept
{
    SwitchToThread();
}

} // namespace detail

using boost::core::detail::sp_thread_yield;

} // namespace core
} // namespace boost

#elif defined(BOOST_HAS_SCHED_YIELD)

#ifdef BOOST_SP_REPORT_IMPLEMENTATION
  BOOST_PRAGMA_MESSAGE("Using sched_yield() in sp_thread_yield")
#endif

#ifndef _AIX
# include <sched.h>
#else
  // AIX's sched.h defines ::var which sometimes conflicts with Lambda's var
  extern "C" int sched_yield(void);
#endif

namespace boost
{
namespace core
{

inline void sp_thread_yield() noexcept
{
    sched_yield();
}

} // namespace core
} // namespace boost

#else

#ifdef BOOST_SP_REPORT_IMPLEMENTATION
  BOOST_PRAGMA_MESSAGE("Using sp_thread_pause() in sp_thread_yield")
#endif

namespace boost
{
namespace core
{

inline void sp_thread_yield() noexcept
{
    sp_thread_pause();
}

} // namespace core
} // namespace boost

#endif

#endif // #ifndef BOOST_CORE_DETAIL_SP_THREAD_YIELD_HPP_INCLUDED
#ifndef BOOST_CORE_DETAIL_SP_THREAD_SLEEP_HPP_INCLUDED
#define BOOST_CORE_DETAIL_SP_THREAD_SLEEP_HPP_INCLUDED

// MS compatible compilers support #pragma once

#if defined(_MSC_VER) && (_MSC_VER >= 1020)
# pragma once
#endif

// boost/core/detail/sp_thread_sleep.hpp
//
// inline void bost::core::sp_thread_sleep();
//
//   Cease execution for a while to yield to other threads,
//   as if by calling nanosleep() with an appropriate interval.
//
// Copyright 2008, 2020, 2023 Peter Dimov
// Distributed under the Boost Software License, Version 1.0
// https://www.boost.org/LICENSE_1_0.txt

#if defined( _WIN32 ) || defined( __WIN32__ ) || defined( __CYGWIN__ )

#ifdef BOOST_SP_REPORT_IMPLEMENTATION
  BOOST_PRAGMA_MESSAGE("Using Sleep(1) in sp_thread_sleep")
#endif

namespace boost
{
namespace core
{
namespace detail
{

inline void sp_thread_sleep() noexcept
{
    Sleep( 1 );
}

} // namespace detail

using boost::core::detail::sp_thread_sleep;

} // namespace core
} // namespace boost

#elif defined(BOOST_HAS_NANOSLEEP)

#ifdef BOOST_SP_REPORT_IMPLEMENTATION
  BOOST_PRAGMA_MESSAGE("Using nanosleep() in sp_thread_sleep")
#endif

#include <time.h>

#if defined(BOOST_HAS_PTHREADS) && !defined(__ANDROID__)
# include <pthread.h>
#endif

namespace boost
{
namespace core
{

inline void sp_thread_sleep() noexcept
{
#if defined(BOOST_HAS_PTHREADS) && !defined(__ANDROID__) && !defined(__OHOS__)

    int oldst;
    pthread_setcancelstate( PTHREAD_CANCEL_DISABLE, &oldst );

#endif

    // g++ -Wextra warns on {} or {0}
    struct timespec rqtp = { 0, 0 };

    // POSIX says that timespec has tv_sec and tv_nsec
    // But it doesn't guarantee order or placement

    rqtp.tv_sec = 0;
    rqtp.tv_nsec = 1000;

    nanosleep( &rqtp, 0 );

#if defined(BOOST_HAS_PTHREADS) && !defined(__ANDROID__) && !defined(__OHOS__)

    pthread_setcancelstate( oldst, &oldst );

#endif

}

} // namespace core
} // namespace boost

#else

#ifdef BOOST_SP_REPORT_IMPLEMENTATION
  BOOST_PRAGMA_MESSAGE("Using sp_thread_yield() in sp_thread_sleep")
#endif

namespace boost
{
namespace core
{

inline void sp_thread_sleep() noexcept
{
    sp_thread_yield();
}

} // namespace core
} // namespace boost

#endif

#endif // #ifndef BOOST_CORE_DETAIL_SP_THREAD_SLEEP_HPP_INCLUDED
#ifndef BOOST_CORE_YIELD_PRIMITIVES_HPP_INCLUDED
#define BOOST_CORE_YIELD_PRIMITIVES_HPP_INCLUDED

// Copyright 2023 Peter Dimov
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

#endif // #ifndef BOOST_CORE_YIELD_PRIMITIVES_HPP_INCLUDED
#ifndef BOOST_UNORDERED_DETAIL_FOA_RW_SPINLOCK_HPP_INCLUDED
#define BOOST_UNORDERED_DETAIL_FOA_RW_SPINLOCK_HPP_INCLUDED

// Copyright 2023 Peter Dimov
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

namespace boost{
namespace unordered{
namespace detail{
namespace foa{

class rw_spinlock
{
private:

    // bit 31: locked exclusive
    // bit 30: writer pending
    // bit 29..0: reader lock count

    static constexpr std::uint32_t locked_exclusive_mask = 1u << 31; // 0x8000'0000
    static constexpr std::uint32_t writer_pending_mask = 1u << 30; // 0x4000'0000
    static constexpr std::uint32_t reader_lock_count_mask = writer_pending_mask - 1; // 0x3FFF'FFFF

    std::atomic<std::uint32_t> state_ = {};

private:

    // Effects: Provides a hint to the implementation that the current thread
    //          has been unable to make progress for k+1 iterations.

    static void yield( unsigned k ) noexcept
    {
        unsigned const sleep_every = 1024; // see below

        k %= sleep_every;

        if( k < 5 )
        {
            // Intel recommendation from the Optimization Reference Manual
            // Exponentially increase number of PAUSE instructions each
            // iteration until reaching a maximum which is approximately
            // one timeslice long (2^4 == 16 in our case)

            unsigned const pause_count = 1u << k;

            for( unsigned i = 0; i < pause_count; ++i )
            {
                boost::core::sp_thread_pause();
            }
        }
        else if( k < sleep_every - 1 )
        {
            // Once the maximum number of PAUSE instructions is reached,
            // we switch to yielding the timeslice immediately

            boost::core::sp_thread_yield();
        }
        else
        {
            // After `sleep_every` iterations of no progress, we sleep,
            // to avoid a deadlock if a lower priority thread has the lock

            boost::core::sp_thread_sleep();
        }
    }

public:

    bool try_lock_shared() noexcept
    {
        std::uint32_t st = state_.load( std::memory_order_relaxed );

        if( st >= reader_lock_count_mask )
        {
            // either bit 31 set, bit 30 set, or reader count is max
            return false;
        }

        std::uint32_t newst = st + 1;
        return state_.compare_exchange_strong( st, newst, std::memory_order_acquire, std::memory_order_relaxed );
    }

    void lock_shared() noexcept
    {
        for( unsigned k = 0; ; ++k )
        {
            std::uint32_t st = state_.load( std::memory_order_relaxed );

            if( st < reader_lock_count_mask )
            {
                std::uint32_t newst = st + 1;
                if( state_.compare_exchange_weak( st, newst, std::memory_order_acquire, std::memory_order_relaxed ) ) return;
            }

            yield( k );
        }
    }

    void unlock_shared() noexcept
    {
        // pre: locked shared, not locked exclusive

        state_.fetch_sub( 1, std::memory_order_release );

        // if the writer pending bit is set, there's a writer waiting
        // let it acquire the lock; it will clear the bit on unlock
    }

    bool try_lock() noexcept
    {
        std::uint32_t st = state_.load( std::memory_order_relaxed );

        if( st & locked_exclusive_mask )
        {
            // locked exclusive
            return false;
        }

        if( st & reader_lock_count_mask )
        {
            // locked shared
            return false;
        }

        std::uint32_t newst = locked_exclusive_mask;
        return state_.compare_exchange_strong( st, newst, std::memory_order_acquire, std::memory_order_relaxed );
    }

    void lock() noexcept
    {
        for( unsigned k = 0; ; ++k )
        {
            std::uint32_t st = state_.load( std::memory_order_relaxed );

            if( st & locked_exclusive_mask )
            {
                // locked exclusive, spin
            }
            else if( ( st & reader_lock_count_mask ) == 0 )
            {
                // not locked exclusive, not locked shared, try to lock

                std::uint32_t newst = locked_exclusive_mask;
                if( state_.compare_exchange_weak( st, newst, std::memory_order_acquire, std::memory_order_relaxed ) ) return;
            }
            else if( st & writer_pending_mask )
            {
                // writer pending bit already set, nothing to do
            }
            else
            {
                // locked shared, set writer pending bit

                std::uint32_t newst = st | writer_pending_mask;
                state_.compare_exchange_weak( st, newst, std::memory_order_relaxed, std::memory_order_relaxed );
            }

            yield( k );
        }
    }

    void unlock() noexcept
    {
        // pre: locked exclusive, not locked shared
        state_.store( 0, std::memory_order_release );
    }
};

}
}
}
}

#endif // BOOST_UNORDERED_DETAIL_FOA_RW_SPINLOCK_HPP_INCLUDED
/* Copyright 2024 Joaquin M Lopez Munoz.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifndef BOOST_UNORDERED_DETAIL_FOA_CUMULATIVE_STATS_HPP
#define BOOST_UNORDERED_DETAIL_FOA_CUMULATIVE_STATS_HPP

#include <array>

#ifdef BOOST_HAS_THREADS
#include <mutex>
#endif

namespace boost{
namespace unordered{
namespace detail{
namespace foa{

/* Cumulative one-pass calculation of the average, variance and deviation of
 * running sequences.
 */

struct sequence_stats_data
{
  double m=0.0;
  double m_prior=0.0;
  double s=0.0;
};

struct welfords_algorithm
{
  template<typename T>
  int operator()(T&& x,sequence_stats_data& d)const noexcept
  {
    static_assert(
      noexcept(static_cast<double>(x)),
      "Argument conversion to double must not throw.");

    d.m_prior=d.m;
    d.m+=(static_cast<double>(x)-d.m)/static_cast<double>(n);
    d.s+=(n!=1)*
      (static_cast<double>(x)-d.m_prior)*(static_cast<double>(x)-d.m);

    return 0;
  }

  std::size_t n;
};

struct sequence_stats_summary
{
  double average;
  double variance;
  double deviation;
};

/* Stats calculated jointly for N same-sized sequences to save the space
 * for count.
 */

template<std::size_t N>
class cumulative_stats
{
public:
  struct summary
  {
    std::size_t                          count;
    std::array<sequence_stats_summary,N> sequence_summary;
  };

  void reset()noexcept{*this=cumulative_stats();}

  template<typename... Ts>
  void add(Ts&&... xs)noexcept
  {
    static_assert(
      sizeof...(Ts)==N,"A sample must be provided for each sequence.");

    if(BOOST_UNLIKELY(++n==0)){
      reset();
      n=1;
    }
    mp11::tuple_transform(
      welfords_algorithm{n},
      std::forward_as_tuple(std::forward<Ts>(xs)...),
      data);
  }

  summary get_summary()const noexcept
  {
    summary res;
    res.count=n;
    for(std::size_t i=0;i<N;++i){
      double average=data[i].m,
             variance=n!=0?data[i].s/static_cast<double>(n):0.0,
             deviation=std::sqrt(variance);
      res.sequence_summary[i]={average,variance,deviation};
    }
    return res;
  }

private:
  std::size_t                       n=0;
  std::array<sequence_stats_data,N> data;
};

#ifdef BOOST_HAS_THREADS

template<std::size_t N>
class concurrent_cumulative_stats:cumulative_stats<N>
{
  using super=cumulative_stats<N>;
  using lock_guard=std::lock_guard<rw_spinlock>;

public:
  using summary=typename super::summary;

  concurrent_cumulative_stats()noexcept:super{}{}
  concurrent_cumulative_stats(const concurrent_cumulative_stats& x)noexcept:
    concurrent_cumulative_stats{x,lock_guard{x.mut}}{}

  concurrent_cumulative_stats&
  operator=(const concurrent_cumulative_stats& x)noexcept
  {
    auto x1=x;
    lock_guard lck{mut};
    static_cast<super&>(*this)=x1;
    return *this;
  }

  void reset()noexcept
  {
    lock_guard lck{mut};
    super::reset();
  }

  template<typename... Ts>
  void add(Ts&&... xs)noexcept
  {
    lock_guard lck{mut};
    super::add(std::forward<Ts>(xs)...);
  }

  summary get_summary()const noexcept
  {
    lock_guard lck{mut};
    return super::get_summary();
  }

private:
  concurrent_cumulative_stats(const super& x,lock_guard&&):super{x}{}

  mutable rw_spinlock mut;
};

#else

template<std::size_t N>
using concurrent_cumulative_stats=cumulative_stats<N>;

#endif

}
}
}
}

#endif
/* Copyright 2023 Joaquin M Lopez Munoz.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifdef BOOST_GCC
#ifndef BOOST_UNORDERED_DETAIL_RESTORE_WSHADOW
 /* GCC's -Wshadow triggers at scenarios like this:
 *
 *   struct foo{};
 *   template<typename Base>
 *   struct derived:Base
 *   {
 *     void f(){int foo;}
 *   };
 *
 *   derived<foo>x;
 *   x.f(); // declaration of "foo" in derived::f shadows base type "foo"
 *
 * This makes shadowing warnings unavoidable in general when a class template
 * derives from user-provided classes, as is the case with foa::table_core
 * deriving from empty_value.
 */

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wshadow"
#else
#pragma GCC diagnostic pop
#endif
#endif
/* Copyright 2023 Joaquin M Lopez Munoz.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#define BOOST_UNORDERED_DETAIL_RESTORE_WSHADOW
#undef BOOST_UNORDERED_DETAIL_RESTORE_WSHADOW
/* Common base for Boost.Unordered open-addressing tables.
 *
 * Copyright 2022-2024 Joaquin M Lopez Munoz.
 * Copyright 2023 Christian Mazakas.
 * Copyright 2024 Braden Ganetsky.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifndef BOOST_UNORDERED_DETAIL_FOA_CORE_HPP
#define BOOST_UNORDERED_DETAIL_FOA_CORE_HPP

#include <new>

#ifndef BOOST_UNORDERED_DISABLE_SSE2
#if defined(BOOST_UNORDERED_ENABLE_SSE2)|| \
    defined(__SSE2__)|| \
    defined(_M_X64)||(defined(_M_IX86_FP)&&_M_IX86_FP>=2)
#define BOOST_UNORDERED_SSE2
#endif
#endif

#ifndef BOOST_UNORDERED_DISABLE_NEON
#if defined(BOOST_UNORDERED_ENABLE_NEON)||\
    (defined(__ARM_NEON)&&!defined(__ARM_BIG_ENDIAN))
#define BOOST_UNORDERED_LITTLE_ENDIAN_NEON
#endif
#endif

#ifdef BOOST_UNORDERED_SSE2
#include <emmintrin.h>
#elif defined(BOOST_UNORDERED_LITTLE_ENDIAN_NEON)
#include <arm_neon.h>
#endif

#ifdef __has_builtin
#define BOOST_UNORDERED_HAS_BUILTIN(x) __has_builtin(x)
#else
#define BOOST_UNORDERED_HAS_BUILTIN(x) 0
#endif

#ifndef NDEBUG
#define BOOST_UNORDERED_ASSUME(cond) BOOST_ASSERT(cond)
#elif BOOST_UNORDERED_HAS_BUILTIN(__builtin_assume)
#define BOOST_UNORDERED_ASSUME(cond) __builtin_assume(cond)
#elif defined(__GNUC__) || BOOST_UNORDERED_HAS_BUILTIN(__builtin_unreachable)
#define BOOST_UNORDERED_ASSUME(cond)    \
  do{                                   \
    if(!(cond))__builtin_unreachable(); \
  }while(0)
#elif defined(_MSC_VER)
#define BOOST_UNORDERED_ASSUME(cond) __assume(cond)
#else
#define BOOST_UNORDERED_ASSUME(cond)  \
  do{                                 \
    static_cast<void>(false&&(cond)); \
  }while(0)
#endif

/* We use BOOST_UNORDERED_PREFETCH[_ELEMENTS] macros rather than proper
 * functions because of https://gcc.gnu.org/bugzilla/show_bug.cgi?id=109985
 */

#if defined(BOOST_GCC)||defined(BOOST_CLANG)
#define BOOST_UNORDERED_PREFETCH(p) __builtin_prefetch((const char*)(p))
#elif defined(BOOST_UNORDERED_SSE2)
#define BOOST_UNORDERED_PREFETCH(p) _mm_prefetch((const char*)(p),_MM_HINT_T0)
#else
#define BOOST_UNORDERED_PREFETCH(p) ((void)(p))
#endif

/* We have experimentally confirmed that ARM architectures get a higher
 * speedup when around the first half of the element slots in a group are
 * prefetched, whereas for Intel just the first cache line is best.
 * Please report back if you find better tunings for some particular
 * architectures.
 */

#if BOOST_ARCH_ARM
/* Cache line size can't be known at compile time, so we settle on
 * the very frequent value of 64B.
 */

#define BOOST_UNORDERED_PREFETCH_ELEMENTS(p,N)                          \
  do{                                                                   \
    auto           BOOST_UNORDERED_P=(p);                               \
    constexpr int  cache_line=64;                                       \
    const char    *p0=reinterpret_cast<const char*>(BOOST_UNORDERED_P), \
                  *p1=p0+sizeof(*BOOST_UNORDERED_P)*(N)/2;              \
    for(;p0<p1;p0+=cache_line)BOOST_UNORDERED_PREFETCH(p0);             \
  }while(0)
#else
#define BOOST_UNORDERED_PREFETCH_ELEMENTS(p,N) BOOST_UNORDERED_PREFETCH(p)
#endif

#ifdef __has_feature
#define BOOST_UNORDERED_HAS_FEATURE(x) __has_feature(x)
#else
#define BOOST_UNORDERED_HAS_FEATURE(x) 0
#endif

#if BOOST_UNORDERED_HAS_FEATURE(thread_sanitizer)|| \
    defined(__SANITIZE_THREAD__)
#define BOOST_UNORDERED_THREAD_SANITIZER
#endif

#define BOOST_UNORDERED_STATIC_ASSERT_HASH_PRED(Hash, Pred)                    \
  static_assert(boost::unordered::detail::is_nothrow_swappable<Hash>::value,   \
    "Template parameter Hash is required to be nothrow Swappable.");           \
  static_assert(boost::unordered::detail::is_nothrow_swappable<Pred>::value,   \
    "Template parameter Pred is required to be nothrow Swappable");

namespace boost{
namespace unordered{
namespace detail{
namespace foa{

static constexpr std::size_t default_bucket_count=0;

/* foa::table_core is the common base of foa::table and foa::concurrent_table,
 * which in their turn serve as the foundational core of
 * boost::unordered_(flat|node)_(map|set) and boost::concurrent_flat_(map|set),
 * respectively. Its main internal design aspects are:
 *
 *   - Element slots are logically split into groups of size N=15. The number
 *     of groups is always a power of two, so the number of allocated slots
       is of the form (N*2^n)-1 (final slot reserved for a sentinel mark).
 *   - Positioning is done at the group level rather than the slot level, that
 *     is, for any given element its hash value is used to locate a group and
 *     insertion is performed on the first available element of that group;
 *     if the group is full (overflow), further groups are tried using
 *     quadratic probing.
 *   - Each group has an associated 16B metadata word holding reduced hash
 *     values and overflow information. Reduced hash values are used to
 *     accelerate lookup within the group by using 128-bit SIMD or 64-bit word
 *     operations.
 */

/* group15 controls metadata information of a group of N=15 element slots.
 * The 16B metadata word is organized as follows (LSB depicted rightmost):
 *
 *   +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *   |ofw|h14|h13|h13|h11|h10|h09|h08|h07|h06|h05|h04|h03|h02|h01|h00|
 *   +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
 *
 * hi is 0 if the i-th element slot is avalaible, 1 to mark a sentinel and,
 * when the slot is occupied, a value in the range [2,255] obtained from the
 * element's original hash value.
 * ofw is the so-called overflow byte. If insertion of an element with hash
 * value h is tried on a full group, then the (h%8)-th bit of the overflow
 * byte is set to 1 and a further group is probed. Having an overflow byte
 * brings two advantages:
 *
 *   - There's no need to reserve a special value of hi to mark tombstone
 *     slots; each reduced hash value keeps then log2(254)=7.99 bits of the
 *     original hash (alternative approaches reserve one full bit to mark
 *     if the slot is available/deleted, so their reduced hash values are 7 bit
 *     strong only).
 *   - When doing an unsuccessful lookup (i.e. the element is not present in
 *     the table), probing stops at the first non-overflowed group. Having 8
 *     bits for signalling overflow makes it very likely that we stop at the
 *     current group (this happens when no element with the same (h%8) value
 *     has overflowed in the group), saving us an additional group check even
 *     under high-load/high-erase conditions. It is critical that hash
 *     reduction is invariant under modulo 8 (see maybe_caused_overflow).
 *
 * When looking for an element with hash value h, match(h) returns a bitmask
 * signalling which slots have the same reduced hash value. If available,
 * match uses SSE2 or (little endian) Neon 128-bit SIMD operations. On non-SIMD
 * scenarios, the logical layout described above is physically mapped to two
 * 64-bit words with *bit interleaving*, i.e. the least significant 16 bits of
 * the first 64-bit word contain the least significant bits of each byte in the
 * "logical" 128-bit word, and so forth. With this layout, match can be
 * implemented with 4 ANDs, 3 shifts, 2 XORs, 1 OR and 1 NOT.
 *
 * IntegralWrapper<Integral> is used to implement group15's underlying
 * metadata: it behaves as a plain integral for foa::table or introduces
 * atomic ops for foa::concurrent_table. If IntegralWrapper<...> is trivially
 * constructible, so is group15, in which case it can be initialized via memset
 * etc. Where needed, group15::initialize resets the metadata to the all
 * zeros (default state).
 */

#ifdef BOOST_UNORDERED_SSE2

template<template<typename> class IntegralWrapper>
struct group15
{
  static constexpr std::size_t N=15;
  static constexpr bool        regular_layout=true;

  struct dummy_group_type
  {
    alignas(16) unsigned char storage[N+1]={0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0};
  };

  inline void initialize()
  {
    _mm_store_si128(
      reinterpret_cast<__m128i*>(m),_mm_setzero_si128());
  }

  inline void set(std::size_t pos,std::size_t hash)
  {
    BOOST_ASSERT(pos<N);
    at(pos)=reduced_hash(hash);
  }

  inline void set_sentinel()
  {
    at(N-1)=sentinel_;
  }

  inline bool is_sentinel(std::size_t pos)const
  {
    BOOST_ASSERT(pos<N);
    return at(pos)==sentinel_;
  }

  static inline bool is_sentinel(unsigned char* pc)noexcept
  {
    return *pc==sentinel_;
  }

  inline void reset(std::size_t pos)
  {
    BOOST_ASSERT(pos<N);
    at(pos)=available_;
  }

  static inline void reset(unsigned char* pc)
  {
    *reinterpret_cast<slot_type*>(pc)=available_;
  }

  inline int match(std::size_t hash)const
  {
    return _mm_movemask_epi8(
      _mm_cmpeq_epi8(load_metadata(),_mm_set1_epi32(match_word(hash))))&0x7FFF;
  }

  inline bool is_not_overflowed(std::size_t hash)const
  {
    static constexpr unsigned char shift[]={1,2,4,8,16,32,64,128};

    return !(overflow()&shift[hash%8]);
  }

  inline void mark_overflow(std::size_t hash)
  {
    overflow()|=static_cast<unsigned char>(1<<(hash%8));
  }

  static inline bool maybe_caused_overflow(unsigned char* pc)
  {
    std::size_t pos=reinterpret_cast<uintptr_t>(pc)%sizeof(group15);
    group15    *pg=reinterpret_cast<group15*>(pc-pos);
    return !pg->is_not_overflowed(*pc);
  }

  inline int match_available()const
  {
    return _mm_movemask_epi8(
      _mm_cmpeq_epi8(load_metadata(),_mm_setzero_si128()))&0x7FFF;
  }

  inline bool is_occupied(std::size_t pos)const
  {
    BOOST_ASSERT(pos<N);
    return at(pos)!=available_;
  }

  static inline bool is_occupied(unsigned char* pc)noexcept
  {
    return *reinterpret_cast<slot_type*>(pc)!=available_;
  }

  inline int match_occupied()const
  {
    return (~match_available())&0x7FFF;
  }

private:
  using slot_type=IntegralWrapper<unsigned char>;
  BOOST_UNORDERED_STATIC_ASSERT(sizeof(slot_type)==1);

  static constexpr unsigned char available_=0,
                                 sentinel_=1;

  inline __m128i load_metadata()const
  {
#ifdef BOOST_UNORDERED_THREAD_SANITIZER
    /* ThreadSanitizer complains on 1-byte atomic writes combined with
     * 16-byte atomic reads.
     */

    return _mm_set_epi8(
      (char)m[15],(char)m[14],(char)m[13],(char)m[12],
      (char)m[11],(char)m[10],(char)m[ 9],(char)m[ 8],
      (char)m[ 7],(char)m[ 6],(char)m[ 5],(char)m[ 4],
      (char)m[ 3],(char)m[ 2],(char)m[ 1],(char)m[ 0]);
#else
    return _mm_load_si128(reinterpret_cast<const __m128i*>(m));
#endif
  }

  inline static int match_word(std::size_t hash)
  {
    static constexpr std::uint32_t word[]=
    {
      0x08080808u,0x09090909u,0x02020202u,0x03030303u,0x04040404u,0x05050505u,
      0x06060606u,0x07070707u,0x08080808u,0x09090909u,0x0A0A0A0Au,0x0B0B0B0Bu,
      0x0C0C0C0Cu,0x0D0D0D0Du,0x0E0E0E0Eu,0x0F0F0F0Fu,0x10101010u,0x11111111u,
      0x12121212u,0x13131313u,0x14141414u,0x15151515u,0x16161616u,0x17171717u,
      0x18181818u,0x19191919u,0x1A1A1A1Au,0x1B1B1B1Bu,0x1C1C1C1Cu,0x1D1D1D1Du,
      0x1E1E1E1Eu,0x1F1F1F1Fu,0x20202020u,0x21212121u,0x22222222u,0x23232323u,
      0x24242424u,0x25252525u,0x26262626u,0x27272727u,0x28282828u,0x29292929u,
      0x2A2A2A2Au,0x2B2B2B2Bu,0x2C2C2C2Cu,0x2D2D2D2Du,0x2E2E2E2Eu,0x2F2F2F2Fu,
      0x30303030u,0x31313131u,0x32323232u,0x33333333u,0x34343434u,0x35353535u,
      0x36363636u,0x37373737u,0x38383838u,0x39393939u,0x3A3A3A3Au,0x3B3B3B3Bu,
      0x3C3C3C3Cu,0x3D3D3D3Du,0x3E3E3E3Eu,0x3F3F3F3Fu,0x40404040u,0x41414141u,
      0x42424242u,0x43434343u,0x44444444u,0x45454545u,0x46464646u,0x47474747u,
      0x48484848u,0x49494949u,0x4A4A4A4Au,0x4B4B4B4Bu,0x4C4C4C4Cu,0x4D4D4D4Du,
      0x4E4E4E4Eu,0x4F4F4F4Fu,0x50505050u,0x51515151u,0x52525252u,0x53535353u,
      0x54545454u,0x55555555u,0x56565656u,0x57575757u,0x58585858u,0x59595959u,
      0x5A5A5A5Au,0x5B5B5B5Bu,0x5C5C5C5Cu,0x5D5D5D5Du,0x5E5E5E5Eu,0x5F5F5F5Fu,
      0x60606060u,0x61616161u,0x62626262u,0x63636363u,0x64646464u,0x65656565u,
      0x66666666u,0x67676767u,0x68686868u,0x69696969u,0x6A6A6A6Au,0x6B6B6B6Bu,
      0x6C6C6C6Cu,0x6D6D6D6Du,0x6E6E6E6Eu,0x6F6F6F6Fu,0x70707070u,0x71717171u,
      0x72727272u,0x73737373u,0x74747474u,0x75757575u,0x76767676u,0x77777777u,
      0x78787878u,0x79797979u,0x7A7A7A7Au,0x7B7B7B7Bu,0x7C7C7C7Cu,0x7D7D7D7Du,
      0x7E7E7E7Eu,0x7F7F7F7Fu,0x80808080u,0x81818181u,0x82828282u,0x83838383u,
      0x84848484u,0x85858585u,0x86868686u,0x87878787u,0x88888888u,0x89898989u,
      0x8A8A8A8Au,0x8B8B8B8Bu,0x8C8C8C8Cu,0x8D8D8D8Du,0x8E8E8E8Eu,0x8F8F8F8Fu,
      0x90909090u,0x91919191u,0x92929292u,0x93939393u,0x94949494u,0x95959595u,
      0x96969696u,0x97979797u,0x98989898u,0x99999999u,0x9A9A9A9Au,0x9B9B9B9Bu,
      0x9C9C9C9Cu,0x9D9D9D9Du,0x9E9E9E9Eu,0x9F9F9F9Fu,0xA0A0A0A0u,0xA1A1A1A1u,
      0xA2A2A2A2u,0xA3A3A3A3u,0xA4A4A4A4u,0xA5A5A5A5u,0xA6A6A6A6u,0xA7A7A7A7u,
      0xA8A8A8A8u,0xA9A9A9A9u,0xAAAAAAAAu,0xABABABABu,0xACACACACu,0xADADADADu,
      0xAEAEAEAEu,0xAFAFAFAFu,0xB0B0B0B0u,0xB1B1B1B1u,0xB2B2B2B2u,0xB3B3B3B3u,
      0xB4B4B4B4u,0xB5B5B5B5u,0xB6B6B6B6u,0xB7B7B7B7u,0xB8B8B8B8u,0xB9B9B9B9u,
      0xBABABABAu,0xBBBBBBBBu,0xBCBCBCBCu,0xBDBDBDBDu,0xBEBEBEBEu,0xBFBFBFBFu,
      0xC0C0C0C0u,0xC1C1C1C1u,0xC2C2C2C2u,0xC3C3C3C3u,0xC4C4C4C4u,0xC5C5C5C5u,
      0xC6C6C6C6u,0xC7C7C7C7u,0xC8C8C8C8u,0xC9C9C9C9u,0xCACACACAu,0xCBCBCBCBu,
      0xCCCCCCCCu,0xCDCDCDCDu,0xCECECECEu,0xCFCFCFCFu,0xD0D0D0D0u,0xD1D1D1D1u,
      0xD2D2D2D2u,0xD3D3D3D3u,0xD4D4D4D4u,0xD5D5D5D5u,0xD6D6D6D6u,0xD7D7D7D7u,
      0xD8D8D8D8u,0xD9D9D9D9u,0xDADADADAu,0xDBDBDBDBu,0xDCDCDCDCu,0xDDDDDDDDu,
      0xDEDEDEDEu,0xDFDFDFDFu,0xE0E0E0E0u,0xE1E1E1E1u,0xE2E2E2E2u,0xE3E3E3E3u,
      0xE4E4E4E4u,0xE5E5E5E5u,0xE6E6E6E6u,0xE7E7E7E7u,0xE8E8E8E8u,0xE9E9E9E9u,
      0xEAEAEAEAu,0xEBEBEBEBu,0xECECECECu,0xEDEDEDEDu,0xEEEEEEEEu,0xEFEFEFEFu,
      0xF0F0F0F0u,0xF1F1F1F1u,0xF2F2F2F2u,0xF3F3F3F3u,0xF4F4F4F4u,0xF5F5F5F5u,
      0xF6F6F6F6u,0xF7F7F7F7u,0xF8F8F8F8u,0xF9F9F9F9u,0xFAFAFAFAu,0xFBFBFBFBu,
      0xFCFCFCFCu,0xFDFDFDFDu,0xFEFEFEFEu,0xFFFFFFFFu,
    };

    return (int)word[narrow_cast<unsigned char>(hash)];
  }

  inline static unsigned char reduced_hash(std::size_t hash)
  {
    return narrow_cast<unsigned char>(match_word(hash));
  }

  inline slot_type& at(std::size_t pos)
  {
    return m[pos];
  }

  inline const slot_type& at(std::size_t pos)const
  {
    return m[pos];
  }

  inline slot_type& overflow()
  {
    return at(N);
  }

  inline const slot_type& overflow()const
  {
    return at(N);
  }

  alignas(16) slot_type m[16];
};

#elif defined(BOOST_UNORDERED_LITTLE_ENDIAN_NEON)

template<template<typename> class IntegralWrapper>
struct group15
{
  static constexpr std::size_t N=15;
  static constexpr bool        regular_layout=true;

  struct dummy_group_type
  {
    alignas(16) unsigned char storage[N+1]={0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0};
  };

  inline void initialize()
  {
    vst1q_u8(reinterpret_cast<uint8_t*>(m),vdupq_n_u8(0));
  }

  inline void set(std::size_t pos,std::size_t hash)
  {
    BOOST_ASSERT(pos<N);
    at(pos)=reduced_hash(hash);
  }

  inline void set_sentinel()
  {
    at(N-1)=sentinel_;
  }

  inline bool is_sentinel(std::size_t pos)const
  {
    BOOST_ASSERT(pos<N);
    return pos==N-1&&at(N-1)==sentinel_;
  }

  static inline bool is_sentinel(unsigned char* pc)noexcept
  {
    return *reinterpret_cast<slot_type*>(pc)==sentinel_;
  }

  inline void reset(std::size_t pos)
  {
    BOOST_ASSERT(pos<N);
    at(pos)=available_;
  }

  static inline void reset(unsigned char* pc)
  {
    *reinterpret_cast<slot_type*>(pc)=available_;
  }

  inline int match(std::size_t hash)const
  {
    return simde_mm_movemask_epi8(vceqq_u8(
      load_metadata(),vdupq_n_u8(reduced_hash(hash))))&0x7FFF;
  }

  inline bool is_not_overflowed(std::size_t hash)const
  {
    static constexpr unsigned char shift[]={1,2,4,8,16,32,64,128};

    return !(overflow()&shift[hash%8]);
  }

  inline void mark_overflow(std::size_t hash)
  {
    overflow()|=static_cast<unsigned char>(1<<(hash%8));
  }

  static inline bool maybe_caused_overflow(unsigned char* pc)
  {
    std::size_t pos=reinterpret_cast<uintptr_t>(pc)%sizeof(group15);
    group15    *pg=reinterpret_cast<group15*>(pc-pos);
    return !pg->is_not_overflowed(*pc);
  };

  inline int match_available()const
  {
    return simde_mm_movemask_epi8(vceqq_u8(
      load_metadata(),vdupq_n_u8(0)))&0x7FFF;
  }

  inline bool is_occupied(std::size_t pos)const
  {
    BOOST_ASSERT(pos<N);
    return at(pos)!=available_;
  }

  static inline bool is_occupied(unsigned char* pc)noexcept
  {
    return *reinterpret_cast<slot_type*>(pc)!=available_;
  }

  inline int match_occupied()const
  {
    return simde_mm_movemask_epi8(vcgtq_u8(
      load_metadata(),vdupq_n_u8(0)))&0x7FFF;
  }

private:
  using slot_type=IntegralWrapper<unsigned char>;
  BOOST_UNORDERED_STATIC_ASSERT(sizeof(slot_type)==1);

  static constexpr unsigned char available_=0,
                                 sentinel_=1;

  inline uint8x16_t load_metadata()const
  {
#ifdef BOOST_UNORDERED_THREAD_SANITIZER
    /* ThreadSanitizer complains on 1-byte atomic writes combined with
     * 16-byte atomic reads.
     */

    alignas(16) uint8_t data[16]={
      m[ 0],m[ 1],m[ 2],m[ 3],m[ 4],m[ 5],m[ 6],m[ 7],
      m[ 8],m[ 9],m[10],m[11],m[12],m[13],m[14],m[15]};
    return vld1q_u8(data);
#else
    return vld1q_u8(reinterpret_cast<const uint8_t*>(m));
#endif
  }

  inline static unsigned char reduced_hash(std::size_t hash)
  {
    static constexpr unsigned char table[]={
      8,9,2,3,4,5,6,7,8,9,10,11,12,13,14,15,
      16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,
      32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,
      48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,
      64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,
      80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,
      96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,
      112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,
      128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,
      144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,
      160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,
      176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,
      192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,
      208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,
      224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,
      240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,
    };

    return table[(unsigned char)hash];
  }

  /* Copied from
   * https://github.com/simd-everywhere/simde/blob/master/simde/x86/
   * sse2.h#L3763
   */

  static inline int simde_mm_movemask_epi8(uint8x16_t a)
  {
    static constexpr uint8_t md[16]={
      1 << 0, 1 << 1, 1 << 2, 1 << 3,
      1 << 4, 1 << 5, 1 << 6, 1 << 7,
      1 << 0, 1 << 1, 1 << 2, 1 << 3,
      1 << 4, 1 << 5, 1 << 6, 1 << 7,
    };

    uint8x16_t  masked=vandq_u8(vld1q_u8(md),a);
    uint8x8x2_t tmp=vzip_u8(vget_low_u8(masked),vget_high_u8(masked));
    uint16x8_t  x=vreinterpretq_u16_u8(vcombine_u8(tmp.val[0],tmp.val[1]));

#ifdef __ARM_ARCH_ISA_A64
    return vaddvq_u16(x);
#else
    uint64x2_t t64=vpaddlq_u32(vpaddlq_u16(x));
    return int(vgetq_lane_u64(t64,0))+int(vgetq_lane_u64(t64,1));
#endif
  }

  inline slot_type& at(std::size_t pos)
  {
    return m[pos];
  }

  inline const slot_type& at(std::size_t pos)const
  {
    return m[pos];
  }

  inline slot_type& overflow()
  {
    return at(N);
  }

  inline const slot_type& overflow()const
  {
    return at(N);
  }

  alignas(16) slot_type m[16];
};

#else /* non-SIMD */

template<template<typename> class IntegralWrapper>
struct group15
{
  static constexpr std::size_t N=15;
  static constexpr bool        regular_layout=false;

  struct dummy_group_type
  {
    alignas(16) std::uint64_t m[2]=
      {0x0000000000004000ull,0x0000000000000000ull};
  };

  inline void initialize(){m[0]=0;m[1]=0;}

  inline void set(std::size_t pos,std::size_t hash)
  {
    BOOST_ASSERT(pos<N);
    set_impl(pos,reduced_hash(hash));
  }

  inline void set_sentinel()
  {
    set_impl(N-1,sentinel_);
  }

  inline bool is_sentinel(std::size_t pos)const
  {
    BOOST_ASSERT(pos<N);
    return
      pos==N-1&&
      (m[0] & std::uint64_t(0x4000400040004000ull))==
        std::uint64_t(0x4000ull)&&
      (m[1] & std::uint64_t(0x4000400040004000ull))==0;
  }

  inline void reset(std::size_t pos)
  {
    BOOST_ASSERT(pos<N);
    set_impl(pos,available_);
  }

  static inline void reset(unsigned char* pc)
  {
    std::size_t pos=reinterpret_cast<uintptr_t>(pc)%sizeof(group15);
    pc-=pos;
    reinterpret_cast<group15*>(pc)->reset(pos);
  }

  inline int match(std::size_t hash)const
  {
    return match_impl(reduced_hash(hash));
  }

  inline bool is_not_overflowed(std::size_t hash)const
  {
    return !(reinterpret_cast<const std::uint16_t*>(m)[hash%8] & 0x8000u);
  }

  inline void mark_overflow(std::size_t hash)
  {
    reinterpret_cast<std::uint16_t*>(m)[hash%8]|=0x8000u;
  }

  static inline bool maybe_caused_overflow(unsigned char* pc)
  {
    std::size_t     pos=reinterpret_cast<uintptr_t>(pc)%sizeof(group15);
    group15        *pg=reinterpret_cast<group15*>(pc-pos);
    std::uint64_t x=((pg->m[0])>>pos)&0x000100010001ull;
    std::uint32_t y=narrow_cast<std::uint32_t>(x|(x>>15)|(x>>30));
    return !pg->is_not_overflowed(y);
  };

  inline int match_available()const
  {
    std::uint64_t x=~(m[0]|m[1]);
    std::uint32_t y=static_cast<std::uint32_t>(x&(x>>32));
    y&=y>>16;
    return y&0x7FFF;
  }

  inline bool is_occupied(std::size_t pos)const
  {
    BOOST_ASSERT(pos<N);
    std::uint64_t x=m[0]|m[1];
    return (x&(0x0001000100010001ull<<pos))!=0;
  }

  inline int match_occupied()const
  {
    std::uint64_t x=m[0]|m[1];
    std::uint32_t y=narrow_cast<std::uint32_t>(x|(x>>32));
    y|=y>>16;
    return y&0x7FFF;
  }

private:
  using word_type=IntegralWrapper<uint64_t>;
  BOOST_UNORDERED_STATIC_ASSERT(sizeof(word_type)==8);

  static constexpr unsigned char available_=0,
                                 sentinel_=1;

  inline static unsigned char reduced_hash(std::size_t hash)
  {
    static constexpr unsigned char table[]={
      8,9,2,3,4,5,6,7,8,9,10,11,12,13,14,15,
      16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,
      32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,
      48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,
      64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,
      80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,
      96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,
      112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,
      128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,
      144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,
      160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,
      176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,
      192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,
      208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,
      224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,
      240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,
    };

    return table[narrow_cast<unsigned char>(hash)];
  }

  inline void set_impl(std::size_t pos,std::size_t n)
  {
    BOOST_ASSERT(n<256);
    set_impl(m[0],pos,n&0xFu);
    set_impl(m[1],pos,n>>4);
  }

  static inline void set_impl(word_type& x,std::size_t pos,std::size_t n)
  {
    static constexpr std::uint64_t mask[]=
    {
      0x0000000000000000ull,0x0000000000000001ull,0x0000000000010000ull,
      0x0000000000010001ull,0x0000000100000000ull,0x0000000100000001ull,
      0x0000000100010000ull,0x0000000100010001ull,0x0001000000000000ull,
      0x0001000000000001ull,0x0001000000010000ull,0x0001000000010001ull,
      0x0001000100000000ull,0x0001000100000001ull,0x0001000100010000ull,
      0x0001000100010001ull,
    };
    static constexpr std::uint64_t imask[]=
    {
      0x0001000100010001ull,0x0001000100010000ull,0x0001000100000001ull,
      0x0001000100000000ull,0x0001000000010001ull,0x0001000000010000ull,
      0x0001000000000001ull,0x0001000000000000ull,0x0000000100010001ull,
      0x0000000100010000ull,0x0000000100000001ull,0x0000000100000000ull,
      0x0000000000010001ull,0x0000000000010000ull,0x0000000000000001ull,
      0x0000000000000000ull,
    };

    BOOST_ASSERT(pos<16&&n<16);
    x|=   mask[n]<<pos;
    x&=~(imask[n]<<pos);
  }

  inline int match_impl(std::size_t n)const
  {
    static constexpr std::uint64_t mask[]=
    {
      0x0000000000000000ull,0x000000000000ffffull,0x00000000ffff0000ull,
      0x00000000ffffffffull,0x0000ffff00000000ull,0x0000ffff0000ffffull,
      0x0000ffffffff0000ull,0x0000ffffffffffffull,0xffff000000000000ull,
      0xffff00000000ffffull,0xffff0000ffff0000ull,0xffff0000ffffffffull,
      0xffffffff00000000ull,0xffffffff0000ffffull,0xffffffffffff0000ull,
      0xffffffffffffffffull,
    };

    BOOST_ASSERT(n<256);
    std::uint64_t x=m[0]^mask[n&0xFu];
                    x=~((m[1]^mask[n>>4])|x);
    std::uint32_t y=static_cast<std::uint32_t>(x&(x>>32));
                    y&=y>>16;
    return          y&0x7FFF;
  }

  alignas(16) word_type m[2];
};

#endif

/* foa::table_core uses a size policy to obtain the permissible sizes of the
 * group array (and, by implication, the element array) and to do the
 * hash->group mapping.
 *
 *   - size_index(n) returns an unspecified "index" number used in other policy
 *     operations.
 *   - size(size_index_) returns the number of groups for the given index. It
 *     is guaranteed that size(size_index(n)) >= n.
 *   - min_size() is the minimum number of groups permissible, i.e.
 *     size(size_index(0)).
 *   - position(hash,size_index_) maps hash to a position in the range
 *     [0,size(size_index_)).
 *
 * The reason we're introducing the intermediate index value for calculating
 * sizes and positions is that it allows us to optimize the implementation of
 * position, which is in the hot path of lookup and insertion operations:
 * pow2_size_policy, the actual size policy used by foa::table, returns 2^n
 * (n>0) as permissible sizes and returns the n most significant bits
 * of the hash value as the position in the group array; using a size index
 * defined as i = (bits in std::size_t) - n, we have an unbeatable
 * implementation of position(hash) as hash>>i.
 * There's a twofold reason for choosing the high bits of hash for positioning:
 *   - Multiplication-based mixing tends to yield better entropy in the high
 *     part of its result.
 *   - group15 reduced-hash values take the *low* bits of hash, and we want
 *     these values and positioning to be as uncorrelated as possible.
 */

struct pow2_size_policy
{
  static inline std::size_t size_index(std::size_t n)
  {
    // TODO: min size is 2, see if we can bring it down to 1 without loss
    // of performance

    return sizeof(std::size_t)*CHAR_BIT-
      (n<=2?1:((std::size_t)(std::bit_width(n-1))));
  }

  static inline std::size_t size(std::size_t size_index_)
  {
     return std::size_t(1)<<(sizeof(std::size_t)*CHAR_BIT-size_index_);
  }

  static constexpr std::size_t min_size(){return 2;}

  static inline std::size_t position(std::size_t hash,std::size_t size_index_)
  {
    return hash>>size_index_;
  }
};

/* size index of a group array for a given *element* capacity */

template<typename Group,typename SizePolicy>
static inline std::size_t size_index_for(std::size_t n)
{
  /* n/N+1 == ceil((n+1)/N) (extra +1 for the sentinel) */
  return SizePolicy::size_index(n/Group::N+1);
}

/* Quadratic prober over a power-of-two range using triangular numbers.
 * mask in next(mask) must be the range size minus one (and since size is 2^n,
 * mask has exactly its n first bits set to 1).
 */

struct pow2_quadratic_prober
{
  pow2_quadratic_prober(std::size_t pos_):pos{pos_}{}

  inline std::size_t get()const{return pos;}
  inline std::size_t length()const{return step+1;}

  /* next returns false when the whole array has been traversed, which ends
   * probing (in practice, full-table probing will only happen with very small
   * arrays).
   */

  inline bool next(std::size_t mask)
  {
    step+=1;
    pos=(pos+step)&mask;
    return step<=mask;
  }

private:
  std::size_t pos,step=0;
};

/* Mixing policies: no_mix is the identity function, and mulx_mix
 * uses the mulx function from <boost/unordered/detail/mulx.hpp>.
 *
 * foa::table_core mixes hash results with mulx_mix unless the hash is marked
 * as avalanching, i.e. of good quality
 * (see <boost/unordered/hash_traits.hpp>).
 */

struct no_mix
{
  template<typename Hash,typename T>
  static inline std::size_t mix(const Hash& h,const T& x)
  {
    return h(x);
  }
};

struct mulx_mix
{
  template<typename Hash,typename T>
  static inline std::size_t mix(const Hash& h,const T& x)
  {
    return mulx(h(x));
  }
};

/* std::countr_zero has a potentially costly check for
 * the case x==0.
 */

inline unsigned int unchecked_countr_zero(int x)
{
#ifdef BOOST_MSVC
  unsigned long r;
  _BitScanForward(&r,(unsigned long)x);
  return (unsigned int)r;
#else
  BOOST_UNORDERED_ASSUME(x!=0);
  return (unsigned int)std::countr_zero((unsigned int)x);
#endif
}

/* table_arrays controls allocation, initialization and deallocation of
 * paired arrays of groups and element slots. Only one chunk of memory is
 * allocated to place both arrays: this is not done for efficiency reasons,
 * but in order to be able to properly align the group array without storing
 * additional offset information --the alignment required (16B) is usually
 * greater than alignof(std::max_align_t) and thus not guaranteed by
 * allocators.
 */

template<typename Group,std::size_t Size>
Group* dummy_groups()
{
  /* Dummy storage initialized as if in an empty container (actually, each
   * of its groups is initialized like a separate empty container).
   * We make table_arrays::groups point to this when capacity()==0, so that
   * we are not allocating any dynamic memory and yet lookup can be implemented
   * without checking for groups==nullptr. This space won't ever be used for
   * insertion as the container's capacity is precisely zero.
   */

  static constexpr typename Group::dummy_group_type
  storage[Size]={typename Group::dummy_group_type(),};

  return reinterpret_cast<Group*>(
    const_cast<typename Group::dummy_group_type*>(storage));
}

template<
  typename Ptr,typename Ptr2,
  typename std::enable_if<!std::is_same<Ptr,Ptr2>::value>::type* = nullptr
>
Ptr to_pointer(Ptr2 p)
{
  if(!p){return nullptr;}
  return std::pointer_traits<Ptr>::pointer_to(*p);
}

template<typename Ptr>
Ptr to_pointer(Ptr p)
{
  return p;
}

template<typename Arrays,typename Allocator>
struct arrays_holder
{
  arrays_holder(const Arrays& arrays,const Allocator& al):
    arrays_{arrays},al_{al}
  {}

  /* not defined but VS in pre-C++17 mode needs to see it for RVO */
  arrays_holder(arrays_holder const&);
  arrays_holder& operator=(arrays_holder const&)=delete;

  ~arrays_holder()
  {
    if(!released_){
      arrays_.delete_(typename Arrays::allocator_type(al_),arrays_);
    }
  }

  const Arrays& release()
  {
    released_=true;
    return arrays_;
  }

private:
  Arrays    arrays_;
  Allocator al_;
  bool      released_=false;
};

template<typename Value,typename Group,typename SizePolicy,typename Allocator>
struct table_arrays
{
  using allocator_type=typename std::allocator_traits<Allocator>::template rebind_alloc<Value>;

  using value_type=Value;
  using group_type=Group;
  static constexpr auto N=group_type::N;
  using size_policy=SizePolicy;
  using value_type_pointer=
    typename std::allocator_traits<allocator_type>::pointer;
  using group_type_pointer=
    typename std::pointer_traits<value_type_pointer>::template
      rebind<group_type>;
  using group_type_pointer_traits=std::pointer_traits<group_type_pointer>;

  // For natvis purposes
  using char_pointer=
    typename std::pointer_traits<value_type_pointer>::template
      rebind<unsigned char>;

  table_arrays(
    std::size_t gsi,std::size_t gsm,
    group_type_pointer pg,value_type_pointer pe):
    groups_size_index{gsi},groups_size_mask{gsm},groups_{pg},elements_{pe}{}

  value_type* elements()const noexcept{return std::to_address(elements_);}
  group_type* groups()const noexcept{return std::to_address(groups_);}

  static void set_arrays(table_arrays& arrays,allocator_type al,std::size_t n)
  {
    return set_arrays(
      arrays,al,n,std::is_same<group_type*,group_type_pointer>{});
  }

  static void set_arrays(
    table_arrays& arrays,allocator_type al,std::size_t,
    std::false_type /* always allocate */)
  {
    using storage_traits=std::allocator_traits<allocator_type>;
    auto groups_size_index=arrays.groups_size_index;
    auto groups_size=size_policy::size(groups_size_index);

    auto sal=allocator_type(al);
    arrays.elements_=storage_traits::allocate(sal,buffer_size(groups_size));

    /* Align arrays.groups to sizeof(group_type). table_iterator critically
      * depends on such alignment for its increment operation.
      */

    auto p=reinterpret_cast<unsigned char*>(arrays.elements()+groups_size*N-1);
    p+=(uintptr_t(sizeof(group_type))-
        reinterpret_cast<uintptr_t>(p))%sizeof(group_type);
    arrays.groups_=
      group_type_pointer_traits::pointer_to(*reinterpret_cast<group_type*>(p));

    initialize_groups(
      arrays.groups(),groups_size,
      is_trivially_default_constructible<group_type>{});
    arrays.groups()[groups_size-1].set_sentinel();
  }

  static void set_arrays(
    table_arrays& arrays,allocator_type al,std::size_t n,
    std::true_type /* optimize for n==0*/)
  {
    if(!n){
      arrays.groups_=dummy_groups<group_type,size_policy::min_size()>();
    }
    else{
      set_arrays(arrays,al,n,std::false_type{});
    }
  }

  static table_arrays new_(allocator_type al,std::size_t n)
  {
    auto         groups_size_index=size_index_for<group_type,size_policy>(n);
    auto         groups_size=size_policy::size(groups_size_index);
    table_arrays arrays{groups_size_index,groups_size-1,nullptr,nullptr};

    set_arrays(arrays,al,n);
    return arrays;
  }

  static void delete_(allocator_type al,table_arrays& arrays)noexcept
  {
    using storage_traits=std::allocator_traits<allocator_type>;

    auto sal=allocator_type(al);
    if(arrays.elements()){
      storage_traits::deallocate(
        sal,arrays.elements_,buffer_size(arrays.groups_size_mask+1));
    }
  }

  /* combined space for elements and groups measured in sizeof(value_type)s */

  static std::size_t buffer_size(std::size_t groups_size)
  {
    auto buffer_bytes=
      /* space for elements (we subtract 1 because of the sentinel) */
      sizeof(value_type)*(groups_size*N-1)+
      /* space for groups + padding for group alignment */
      sizeof(group_type)*(groups_size+1)-1;

    /* ceil(buffer_bytes/sizeof(value_type)) */
    return (buffer_bytes+sizeof(value_type)-1)/sizeof(value_type);
  }

  static void initialize_groups(
    group_type* pg,std::size_t size,std::true_type /* memset */)
  {
    /* memset faster/not slower than manual, assumes all zeros is group_type's
     * default layout.
     * reinterpret_cast: GCC may complain about group_type not being trivially
     * copy-assignable when we're relying on trivial copy constructibility.
     */

    std::memset(
      reinterpret_cast<unsigned char*>(pg),0,sizeof(group_type)*size);
  }

  static void initialize_groups(
    group_type* pg,std::size_t size,std::false_type /* manual */)
  {
    while(size--!=0)::new (pg++) group_type();
  }

  std::size_t        groups_size_index;
  std::size_t        groups_size_mask;
  group_type_pointer groups_;
  value_type_pointer elements_;
};

#ifdef BOOST_UNORDERED_ENABLE_STATS
/* stats support */

struct table_core_cumulative_stats
{
  concurrent_cumulative_stats<1> insertion;
  concurrent_cumulative_stats<2> successful_lookup,
                                 unsuccessful_lookup;
};

struct table_core_insertion_stats
{
  std::size_t            count;
  sequence_stats_summary probe_length;
};

struct table_core_lookup_stats
{
  std::size_t            count;
  sequence_stats_summary probe_length;
  sequence_stats_summary num_comparisons;
};

struct table_core_stats
{
  table_core_insertion_stats insertion;
  table_core_lookup_stats    successful_lookup,
                             unsuccessful_lookup;
};

#define BOOST_UNORDERED_ADD_STATS(stats,args) stats.add args
#define BOOST_UNORDERED_SWAP_STATS(stats1,stats2) std::swap(stats1,stats2)
#define BOOST_UNORDERED_COPY_STATS(stats1,stats2) stats1=stats2
#define BOOST_UNORDERED_RESET_STATS_OF(x) x.reset_stats()
#define BOOST_UNORDERED_STATS_COUNTER(name) std::size_t name=0
#define BOOST_UNORDERED_INCREMENT_STATS_COUNTER(name) ++name

#else

#define BOOST_UNORDERED_ADD_STATS(stats,args) ((void)0)
#define BOOST_UNORDERED_SWAP_STATS(stats1,stats2) ((void)0)
#define BOOST_UNORDERED_COPY_STATS(stats1,stats2) ((void)0)
#define BOOST_UNORDERED_RESET_STATS_OF(x) ((void)0)
#define BOOST_UNORDERED_STATS_COUNTER(name) ((void)0)
#define BOOST_UNORDERED_INCREMENT_STATS_COUNTER(name) ((void)0)

#endif

struct if_constexpr_void_else{void operator()()const{}};

template<bool B,typename F,typename G=if_constexpr_void_else>
void if_constexpr(F f,G g={})
{
  std::get<B?0:1>(std::forward_as_tuple(f,g))();
}

template<bool B,typename T,typename std::enable_if<B>::type* =nullptr>
void copy_assign_if(T& x,const T& y){x=y;}

template<bool B,typename T,typename std::enable_if<!B>::type* =nullptr>
void copy_assign_if(T&,const T&){}

template<bool B,typename T,typename std::enable_if<B>::type* =nullptr>
void move_assign_if(T& x,T& y){x=std::move(y);}

template<bool B,typename T,typename std::enable_if<!B>::type* =nullptr>
void move_assign_if(T&,T&){}

template<bool B,typename T,typename std::enable_if<B>::type* =nullptr>
void swap_if(T& x,T& y){using std::swap; swap(x,y);}

template<bool B,typename T,typename std::enable_if<!B>::type* =nullptr>
void swap_if(T&,T&){}

template<typename Allocator>
struct is_std_allocator:std::false_type{};

template<typename T>
struct is_std_allocator<std::allocator<T>>:std::true_type{};

/* std::allocator::construct marked as deprecated */
#ifdef _LIBCPP_SUPPRESS_DEPRECATED_PUSH
_LIBCPP_SUPPRESS_DEPRECATED_PUSH
#elif defined(_STL_DISABLE_DEPRECATED_WARNING)
_STL_DISABLE_DEPRECATED_WARNING
#elif defined(_MSC_VER)
#pragma warning(push)
#pragma warning(disable:4996)
#endif

template<typename Allocator,typename Ptr,typename... Args>
struct alloc_has_construct
{
private:
  template<typename Allocator2>
  static decltype(
    std::declval<Allocator2&>().construct(
      std::declval<Ptr>(),std::declval<Args&&>()...),
    std::true_type{}
  ) check(int);

  template<typename> static std::false_type check(...);

public:
  static constexpr bool value=decltype(check<Allocator>(0))::value;
};

#ifdef _LIBCPP_SUPPRESS_DEPRECATED_POP
_LIBCPP_SUPPRESS_DEPRECATED_POP
#elif defined(_STL_RESTORE_DEPRECATED_WARNING)
_STL_RESTORE_DEPRECATED_WARNING
#elif defined(_MSC_VER)
#pragma warning(pop)
#endif

/* We expose the hard-coded max load factor so that tests can use it without
 * needing to pull it from an instantiated class template such as the table
 * class.
 */
static constexpr float mlf=0.875f;

template<typename Group,typename Element>
struct table_locator
{
  table_locator()=default;
  table_locator(Group* pg_,unsigned int n_,Element* p_):pg{pg_},n{n_},p{p_}{}

  explicit operator bool()const noexcept{return p!=nullptr;}

  Group        *pg=nullptr;
  unsigned int  n=0;
  Element      *p=nullptr;
};

struct try_emplace_args_t{};

template<typename TypePolicy,typename Allocator,typename... Args>
class alloc_cted_insert_type
{
  using emplace_type=typename std::conditional<
    std::is_constructible<typename TypePolicy::init_type,Args...>::value,
    typename TypePolicy::init_type,
    typename TypePolicy::value_type
  >::type;

  using insert_type=typename std::conditional<
    std::is_constructible<typename TypePolicy::value_type,emplace_type>::value,
    emplace_type,typename TypePolicy::element_type
  >::type;

  using alloc_cted = allocator_constructed<Allocator, insert_type, TypePolicy>;
  alloc_cted val;

public:
  alloc_cted_insert_type(const Allocator& al_,Args&&... args):val{al_,std::forward<Args>(args)...}
  {
  }

  insert_type& value(){return val.value();}
};

template<typename TypePolicy,typename Allocator,typename... Args>
alloc_cted_insert_type<TypePolicy,Allocator,Args...>
alloc_make_insert_type(const Allocator& al,Args&&... args)
{
  return {al,std::forward<Args>(args)...};
}

template <typename TypePolicy, typename Allocator, typename KFwdRef,
  typename = void>
class alloc_cted_or_fwded_key_type
{
  using key_type = typename TypePolicy::key_type;
  allocator_constructed<Allocator, key_type, TypePolicy> val;

public:
  alloc_cted_or_fwded_key_type(const Allocator& al_, KFwdRef k)
      : val(al_, std::forward<KFwdRef>(k))
  {
  }

  key_type&& move_or_fwd() { return std::move(val.value()); }
};

template <typename TypePolicy, typename Allocator, typename KFwdRef>
class alloc_cted_or_fwded_key_type<TypePolicy, Allocator, KFwdRef,
  typename std::enable_if<
    is_similar<KFwdRef, typename TypePolicy::key_type>::value>::type>
{
  // This specialization acts as a forwarding-reference wrapper
  BOOST_UNORDERED_STATIC_ASSERT(std::is_reference<KFwdRef>::value);
  KFwdRef ref;

public:
  alloc_cted_or_fwded_key_type(const Allocator&, KFwdRef k)
      : ref(std::forward<KFwdRef>(k))
  {
  }

  KFwdRef move_or_fwd() { return std::forward<KFwdRef>(ref); }
};

template <typename Container>
using is_map =
  std::integral_constant<bool, !std::is_same<typename Container::key_type,
                                 typename Container::value_type>::value>;

template <typename Container, typename K>
using is_emplace_kv_able = std::integral_constant<bool,
  is_map<Container>::value &&
    (is_similar<K, typename Container::key_type>::value ||
      is_complete_and_move_constructible<typename Container::key_type>::value)>;

/* table_core. The TypePolicy template parameter is used to generate
 * instantiations suitable for either maps or sets, and introduces non-standard
 * init_type and element_type:
 *
 *   - TypePolicy::key_type and TypePolicy::value_type have the obvious
 *     meaning. TypePolicy::mapped_type is expected to be provided as well
 *     when key_type and value_type are not the same.
 *
 *   - TypePolicy::init_type is the type implicitly converted to when
 *     writing x.insert({...}). For maps, this is std::pair<Key,T> rather
 *     than std::pair<const Key,T> so that, for instance, x.insert({"hello",0})
 *     produces a cheaply moveable std::string&& ("hello") rather than
 *     a copyable const std::string&&. foa::table::insert is extended to accept
 *     both init_type and value_type references.
 *
 *   - TypePolicy::construct and TypePolicy::destroy are used for the
 *     construction and destruction of the internal types: value_type,
 *     init_type, element_type, and key_type.
 *
 *   - TypePolicy::move is used to provide move semantics for the internal
 *     types used by the container during rehashing and emplace. These types
 *     are init_type, value_type and emplace_type. During insertion, a
 *     stack-local type will be created based on the constructibility of the
 *     value_type and the supplied arguments. TypePolicy::move is used here
 *     for transfer of ownership. Similarly, TypePolicy::move is also used
 *     during rehashing when elements are moved to the new table.
 *
 *   - TypePolicy::extract returns a const reference to the key part of
 *     a value of type value_type, init_type, element_type or
 *     decltype(TypePolicy::move(...)).
 *
 *   - TypePolicy::element_type is the type that table_arrays uses when
 *     allocating buckets, which allows us to have flat and node container.
 *     For flat containers, element_type is value_type. For node
 *     containers, it is a strong typedef to value_type*.
 *
 *   - TypePolicy::value_from returns a mutable reference to value_type from
 *     a given element_type. This is used when elements of the table themselves
 *     need to be moved, such as during move construction/assignment when
 *     allocators are unequal and there is no propagation. For all other cases,
 *     the element_type itself is moved.
 */

#ifdef BOOST_MSVC
#pragma warning(push)
#pragma warning(disable:4714)
#endif

template<
  typename TypePolicy,typename Group,template<typename...> class Arrays,
  typename SizeControl,typename Hash,typename Pred,typename Allocator
>
class

#if defined(_MSC_VER)&&_MSC_FULL_VER>=190023918
__declspec(empty_bases)
#endif

table_core:empty_value<Hash,0>,empty_value<Pred,1>,empty_value<Allocator,2>
{
public:
  using type_policy=TypePolicy;
  using group_type=Group;
  static constexpr auto N=group_type::N;
  using size_policy=pow2_size_policy;
  using prober=pow2_quadratic_prober;
  using mix_policy=typename std::conditional<
    hash_is_avalanching<Hash>::value,
    no_mix,
    mulx_mix
  >::type;
  using alloc_traits=std::allocator_traits<Allocator>;
  using element_type=typename type_policy::element_type;
  using arrays_type=Arrays<element_type,group_type,size_policy,Allocator>;
  using size_ctrl_type=SizeControl;
  static constexpr auto uses_fancy_pointers=!std::is_same<
    typename alloc_traits::pointer,
    typename alloc_traits::value_type*
  >::value;

  using key_type=typename type_policy::key_type;
  using init_type=typename type_policy::init_type;
  using value_type=typename type_policy::value_type;
  using hasher=Hash;
  using key_equal=Pred;
  using allocator_type=Allocator;
  using pointer=value_type*;
  using const_pointer=const value_type*;
  using reference=value_type&;
  using const_reference=const value_type&;
  using size_type=std::size_t;
  using difference_type=std::ptrdiff_t;
  using locator=table_locator<group_type,element_type>;
  using arrays_holder_type=arrays_holder<arrays_type,Allocator>;

#ifdef BOOST_UNORDERED_ENABLE_STATS
  using cumulative_stats=table_core_cumulative_stats;
  using stats=table_core_stats;
#endif

#ifdef BOOST_GCC
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif

  table_core(
    std::size_t n=default_bucket_count,const Hash& h_=Hash(),
    const Pred& pred_=Pred(),const Allocator& al_=Allocator()):
    hash_base{empty_init,h_},pred_base{empty_init,pred_},
    allocator_base{empty_init,al_},arrays(new_arrays(n)),
    size_ctrl{initial_max_load(),0}
    {}

#ifdef BOOST_GCC
#pragma GCC diagnostic pop
#endif

  /* genericize on an ArraysFn so that we can do things like delay an
   * allocation for the group_access data required by cfoa after the move
   * constructors of Hash, Pred have been invoked
   */
  template<typename ArraysFn>
  table_core(
    Hash&& h_,Pred&& pred_,Allocator&& al_,
    ArraysFn arrays_fn,const size_ctrl_type& size_ctrl_):
    hash_base{empty_init,std::move(h_)},
    pred_base{empty_init,std::move(pred_)},
    allocator_base{empty_init,std::move(al_)},
    arrays(arrays_fn()),size_ctrl(size_ctrl_)
  {}

  table_core(const table_core& x):
    table_core{x,alloc_traits::select_on_container_copy_construction(x.al())}{}

  template<typename ArraysFn>
  table_core(table_core&& x,arrays_holder_type&& ah,ArraysFn arrays_fn):
    table_core(
      std::move(x.h()),std::move(x.pred()),std::move(x.al()),
      arrays_fn,x.size_ctrl)
  {
    x.arrays=ah.release();
    x.size_ctrl.ml=x.initial_max_load();
    x.size_ctrl.size=0;
    BOOST_UNORDERED_SWAP_STATS(cstats,x.cstats);
  }

  table_core(table_core&& x)
    noexcept(
      std::is_nothrow_move_constructible<Hash>::value&&
      std::is_nothrow_move_constructible<Pred>::value&&
      std::is_nothrow_move_constructible<Allocator>::value&&
      !uses_fancy_pointers):
    table_core{
      std::move(x),x.make_empty_arrays(),[&x]{return x.arrays;}}
  {}

  table_core(const table_core& x,const Allocator& al_):
    table_core{std::size_t(std::ceil(float(x.size())/mlf)),x.h(),x.pred(),al_}
  {
    copy_elements_from(x);
  }

  table_core(table_core&& x,const Allocator& al_):
    table_core{std::move(x.h()),std::move(x.pred()),al_}
  {
    if(al()==x.al()){
      using std::swap;
      swap(arrays,x.arrays);
      swap(size_ctrl,x.size_ctrl);
      BOOST_UNORDERED_SWAP_STATS(cstats,x.cstats);
    }
    else{
      reserve(x.size());
      clear_on_exit c{x};
      (void)c;
      BOOST_UNORDERED_RESET_STATS_OF(x);

      /* This works because subsequent x.clear() does not depend on the
       * elements' values.
       */
      x.for_all_elements([this](element_type* p){
        unchecked_insert(type_policy::move(type_policy::value_from(*p)));
      });
    }
  }

  ~table_core()noexcept
  {
    for_all_elements([this](element_type* p){
      destroy_element(p);
    });
    delete_arrays(arrays);
  }

  std::size_t initial_max_load()const
  {
    static constexpr std::size_t small_capacity=2*N-1;

    auto capacity_=capacity();
    if(capacity_<=small_capacity){
      return capacity_;
    }
    else{
      return (std::size_t)(mlf*(float)(capacity_));
    }
  }

  arrays_holder_type make_empty_arrays()const
  {
    return make_arrays(0);
  }

  table_core& operator=(const table_core& x)
  {
    BOOST_UNORDERED_STATIC_ASSERT_HASH_PRED(Hash, Pred)

    static constexpr auto pocca=
      alloc_traits::propagate_on_container_copy_assignment::value;

    if(this!=std::addressof(x)){
      /* If copy construction here winds up throwing, the container is still
       * left intact so we perform these operations first.
       */
      hasher    tmp_h=x.h();
      key_equal tmp_p=x.pred();

      clear();

      /* Because we've asserted at compile-time that Hash and Pred are nothrow
       * swappable, we can safely mutate our source container and maintain
       * consistency between the Hash, Pred compatibility.
       */
      using std::swap;
      swap(h(),tmp_h);
      swap(pred(),tmp_p);

      if_constexpr<pocca>([&,this]{
        if(al()!=x.al()){
          auto ah=x.make_arrays(std::size_t(std::ceil(float(x.size())/mlf)));
          delete_arrays(arrays);
          arrays=ah.release();
          size_ctrl.ml=initial_max_load();
        }
        copy_assign_if<pocca>(al(),x.al());
      });
      /* noshrink: favor memory reuse over tightness */
      noshrink_reserve(x.size());
      copy_elements_from(x);
    }
    return *this;
  }

#ifdef BOOST_MSVC
#pragma warning(push)
#pragma warning(disable:4127)
#endif

  table_core& operator=(table_core&& x)
    noexcept(
      (alloc_traits::propagate_on_container_move_assignment::value||
      alloc_traits::is_always_equal::value)&&!uses_fancy_pointers)
  {
    BOOST_UNORDERED_STATIC_ASSERT_HASH_PRED(Hash, Pred)

    static constexpr auto pocma=
      alloc_traits::propagate_on_container_move_assignment::value;

    if(this!=std::addressof(x)){
      /* Given ambiguity in implementation strategies briefly discussed here:
       * https://www.open-std.org/jtc1/sc22/wg21/docs/lwg-active.html#2227
       *
       * we opt into requiring nothrow swappability and eschew the move
       * operations associated with Hash, Pred.
       *
       * To this end, we ensure that the user never has to consider the
       * moved-from state of their Hash, Pred objects
       */

      using std::swap;

      clear();

      if(pocma||al()==x.al()){
        auto ah=x.make_empty_arrays();
        swap(h(),x.h());
        swap(pred(),x.pred());
        delete_arrays(arrays);
        move_assign_if<pocma>(al(),x.al());
        arrays=x.arrays;
        size_ctrl.ml=std::size_t(x.size_ctrl.ml);
        size_ctrl.size=std::size_t(x.size_ctrl.size);
        BOOST_UNORDERED_COPY_STATS(cstats,x.cstats);
        x.arrays=ah.release();
        x.size_ctrl.ml=x.initial_max_load();
        x.size_ctrl.size=0;
        BOOST_UNORDERED_RESET_STATS_OF(x);
      }
      else{
        swap(h(),x.h());
        swap(pred(),x.pred());

        /* noshrink: favor memory reuse over tightness */
        noshrink_reserve(x.size());
        clear_on_exit c{x};
        (void)c;
        BOOST_UNORDERED_RESET_STATS_OF(x);

        /* This works because subsequent x.clear() does not depend on the
         * elements' values.
         */
        x.for_all_elements([this](element_type* p){
          unchecked_insert(type_policy::move(type_policy::value_from(*p)));
        });
      }
    }
    return *this;
  }

#ifdef BOOST_MSVC
#pragma warning(pop)
#endif

  allocator_type get_allocator()const noexcept{return al();}

  bool        empty()const noexcept{return size()==0;}
  std::size_t size()const noexcept{return size_ctrl.size;}
  std::size_t max_size()const noexcept{return SIZE_MAX;}

  BOOST_FORCEINLINE
  void erase(group_type* pg,unsigned int pos,element_type* p)noexcept
  {
    destroy_element(p);
    recover_slot(pg,pos);
  }

  BOOST_FORCEINLINE
  void erase(unsigned char* pc,element_type* p)noexcept
  {
    destroy_element(p);
    recover_slot(pc);
  }

  template<typename Key>
  BOOST_FORCEINLINE locator find(const Key& x)const
  {
    auto hash=hash_for(x);
    return find(x,position_for(hash),hash);
  }

#ifdef BOOST_MSVC
/* warning: forcing value to bool 'true' or 'false' in bool(pred()...) */
#pragma warning(push)
#pragma warning(disable:4800)
#endif

  template<typename Key>
  BOOST_FORCEINLINE locator find(
    const Key& x,std::size_t pos0,std::size_t hash)const
  {
    BOOST_UNORDERED_STATS_COUNTER(num_cmps);
    prober pb(pos0);
    do{
      auto pos=pb.get();
      auto pg=arrays.groups()+pos;
      auto mask=pg->match(hash);
      if(mask){
        auto elements=arrays.elements();
        BOOST_UNORDERED_ASSUME(elements!=nullptr);
        auto p=elements+pos*N;
        BOOST_UNORDERED_PREFETCH_ELEMENTS(p,N);
        do{
          BOOST_UNORDERED_INCREMENT_STATS_COUNTER(num_cmps);
          auto n=unchecked_countr_zero(mask);
          if(BOOST_LIKELY(bool(pred()(x,key_from(p[n]))))){
            BOOST_UNORDERED_ADD_STATS(
              cstats.successful_lookup,(pb.length(),num_cmps));
            return {pg,n,p+n};
          }
          mask&=mask-1;
        }while(mask);
      }
      if(BOOST_LIKELY(pg->is_not_overflowed(hash))){
        BOOST_UNORDERED_ADD_STATS(
          cstats.unsuccessful_lookup,(pb.length(),num_cmps));
        return {};
      }
    }
    while(BOOST_LIKELY(pb.next(arrays.groups_size_mask)));
    BOOST_UNORDERED_ADD_STATS(
      cstats.unsuccessful_lookup,(pb.length(),num_cmps));
    return {};
  }

#ifdef BOOST_MSVC
#pragma warning(pop)
#endif

  void swap(table_core& x)
    noexcept(
      alloc_traits::propagate_on_container_swap::value||
      alloc_traits::is_always_equal::value)
  {
    BOOST_UNORDERED_STATIC_ASSERT_HASH_PRED(Hash, Pred)

    static constexpr auto pocs=
      alloc_traits::propagate_on_container_swap::value;

    using std::swap;
    if_constexpr<pocs>([&,this]{
      swap_if<pocs>(al(),x.al());
    },
    [&,this]{
      BOOST_ASSERT(al()==x.al());
      (void)this;
    });

    swap(h(),x.h());
    swap(pred(),x.pred());
    swap(arrays,x.arrays);
    swap(size_ctrl,x.size_ctrl);
  }

  void clear()noexcept
  {
    auto p=arrays.elements();
    if(p){
      for(auto pg=arrays.groups(),last=pg+arrays.groups_size_mask+1;
          pg!=last;++pg,p+=N){
        auto mask=match_really_occupied(pg,last);
        while(mask){
          destroy_element(p+unchecked_countr_zero(mask));
          mask&=mask-1;
        }
        /* we wipe the entire metadata to reset the overflow byte as well */
        pg->initialize();
      }
      arrays.groups()[arrays.groups_size_mask].set_sentinel();
      size_ctrl.ml=initial_max_load();
      size_ctrl.size=0;
    }
  }

  hasher hash_function()const{return h();}
  key_equal key_eq()const{return pred();}

  std::size_t capacity()const noexcept
  {
    return arrays.elements()?(arrays.groups_size_mask+1)*N-1:0;
  }

  float load_factor()const noexcept
  {
    if(capacity()==0)return 0;
    else             return float(size())/float(capacity());
  }

  float max_load_factor()const noexcept{return mlf;}

  std::size_t max_load()const noexcept{return size_ctrl.ml;}

  void rehash(std::size_t n)
  {
    auto m=size_t(std::ceil(float(size())/mlf));
    if(m>n)n=m;
    if(n)n=capacity_for(n);

    if(n!=capacity())unchecked_rehash(n);
  }

  void reserve(std::size_t n)
  {
    rehash(std::size_t(std::ceil(float(n)/mlf)));
  }

#ifdef BOOST_UNORDERED_ENABLE_STATS
  stats get_stats()const
  {
    auto insertion=cstats.insertion.get_summary();
    auto successful_lookup=cstats.successful_lookup.get_summary();
    auto unsuccessful_lookup=cstats.unsuccessful_lookup.get_summary();
    return{
      {
        insertion.count,
        insertion.sequence_summary[0]
      },
      {
        successful_lookup.count,
        successful_lookup.sequence_summary[0],
        successful_lookup.sequence_summary[1]
      },
      {
        unsuccessful_lookup.count,
        unsuccessful_lookup.sequence_summary[0],
        unsuccessful_lookup.sequence_summary[1]
      },
    };
  }

  void reset_stats()noexcept
  {
    cstats.insertion.reset();
    cstats.successful_lookup.reset();
    cstats.unsuccessful_lookup.reset();
  }
#endif

  friend bool operator==(const table_core& x,const table_core& y)
  {
    return
      x.size()==y.size()&&
      x.for_all_elements_while([&](element_type* p){
        auto loc=y.find(key_from(*p));
        return loc&&
          const_cast<const value_type&>(type_policy::value_from(*p))==
          const_cast<const value_type&>(type_policy::value_from(*loc.p));
      });
  }

  friend bool operator!=(const table_core& x,const table_core& y)
  {
    return !(x==y);
  }

  struct clear_on_exit
  {
    ~clear_on_exit(){x.clear();}
    table_core& x;
  };

  Hash&            h(){return hash_base::get();}
  const Hash&      h()const{return hash_base::get();}
  Pred&            pred(){return pred_base::get();}
  const Pred&      pred()const{return pred_base::get();}
  Allocator&       al(){return allocator_base::get();}
  const Allocator& al()const{return allocator_base::get();}

  template<typename... Args>
  void construct_element(element_type* p,Args&&... args)
  {
    type_policy::construct(al(),p,std::forward<Args>(args)...);
  }

  template<typename... Args>
  void construct_element(element_type* p,try_emplace_args_t,Args&&... args)
  {
    construct_element_from_try_emplace_args(
      p,
      std::integral_constant<bool,std::is_same<key_type,value_type>::value>{},
      std::forward<Args>(args)...);
  }

  void destroy_element(element_type* p)noexcept
  {
    type_policy::destroy(al(),p);
  }

  struct destroy_element_on_exit
  {
    ~destroy_element_on_exit(){this_->destroy_element(p);}
    table_core   *this_;
    element_type *p;
  };

  template<typename T>
  static inline auto key_from(const T& x)
    ->decltype(type_policy::extract(x))
  {
    return type_policy::extract(x);
  }

  template<typename Key,typename... Args>
  static inline const Key& key_from(
    try_emplace_args_t,const Key& x,const Args&...)
  {
    return x;
  }

  template<typename Key>
  inline std::size_t hash_for(const Key& x)const
  {
    return mix_policy::mix(h(),x);
  }

  inline std::size_t position_for(std::size_t hash)const
  {
    return position_for(hash,arrays);
  }

  static inline std::size_t position_for(
    std::size_t hash,const arrays_type& arrays_)
  {
    return size_policy::position(hash,arrays_.groups_size_index);
  }

  static inline int match_really_occupied(group_type* pg,group_type* last)
  {
    /* excluding the sentinel */
    return pg->match_occupied()&~(int(pg==last-1)<<(N-1));
  }

  template<typename... Args>
  locator unchecked_emplace_at(
    std::size_t pos0,std::size_t hash,Args&&... args)
  {
    auto res=nosize_unchecked_emplace_at(
      arrays,pos0,hash,std::forward<Args>(args)...);
    ++size_ctrl.size;
    return res;
  }

  BOOST_NOINLINE void unchecked_rehash_for_growth()
  {
    auto new_arrays_=new_arrays_for_growth();
    unchecked_rehash(new_arrays_);
  }

  template<typename... Args>
  BOOST_NOINLINE locator
  unchecked_emplace_with_rehash(std::size_t hash,Args&&... args)
  {
    auto    new_arrays_=new_arrays_for_growth();
    locator it;
    BOOST_TRY{
      /* strong exception guarantee -> try insertion before rehash */
      it=nosize_unchecked_emplace_at(
        new_arrays_,position_for(hash,new_arrays_),
        hash,std::forward<Args>(args)...);
    }
    BOOST_CATCH(...){
      delete_arrays(new_arrays_);
      BOOST_RETHROW
    }
    BOOST_CATCH_END

    /* new_arrays_ lifetime taken care of by unchecked_rehash */
    unchecked_rehash(new_arrays_);
    ++size_ctrl.size;
    return it;
  }

  void noshrink_reserve(std::size_t n)
  {
    /* used only on assignment after element clearance */
    BOOST_ASSERT(empty());

    if(n){
      n=std::size_t(std::ceil(float(n)/mlf));
      n=capacity_for(n);

      if(n>capacity()){
        auto new_arrays_=new_arrays(n);
        delete_arrays(arrays);
        arrays=new_arrays_;
        size_ctrl.ml=initial_max_load();
      }
    }
  }

  template<typename F>
  void for_all_elements(F f)const
  {
    for_all_elements(arrays,f);
  }

  template<typename F>
  static auto for_all_elements(const arrays_type& arrays_,F f)
    ->decltype(f(nullptr),void())
  {
    for_all_elements_while(arrays_,[&](element_type* p){f(p);return true;});
  }

  template<typename F>
  static auto for_all_elements(const arrays_type& arrays_,F f)
    ->decltype(f(nullptr,0,nullptr),void())
  {
    for_all_elements_while(
      arrays_,[&](group_type* pg,unsigned int n,element_type* p)
        {f(pg,n,p);return true;});
  }

  template<typename F>
  bool for_all_elements_while(F f)const
  {
    return for_all_elements_while(arrays,f);
  }

  template<typename F>
  static auto for_all_elements_while(const arrays_type& arrays_,F f)
    ->decltype(f(nullptr),bool())
  {
    return for_all_elements_while(
      arrays_,[&](group_type*,unsigned int,element_type* p){return f(p);});
  }

  template<typename F>
  static auto for_all_elements_while(const arrays_type& arrays_,F f)
    ->decltype(f(nullptr,0,nullptr),bool())
  {
    auto p=arrays_.elements();
    if(p){
      for(auto pg=arrays_.groups(),last=pg+arrays_.groups_size_mask+1;
          pg!=last;++pg,p+=N){
        auto mask=match_really_occupied(pg,last);
        while(mask){
          auto n=unchecked_countr_zero(mask);
          if(!f(pg,n,p+n))return false;
          mask&=mask-1;
        }
      }
    }
    return true;
  }

  arrays_type              arrays;
  size_ctrl_type           size_ctrl;

#ifdef BOOST_UNORDERED_ENABLE_STATS
  mutable cumulative_stats cstats;
#endif

private:
  template<
    typename,typename,template<typename...> class,
    typename,typename,typename,typename
  >
  friend class table_core;

  using hash_base=empty_value<Hash,0>;
  using pred_base=empty_value<Pred,1>;
  using allocator_base=empty_value<Allocator,2>;

#ifdef BOOST_GCC
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif

  /* used by allocator-extended move ctor */

  table_core(Hash&& h_,Pred&& pred_,const Allocator& al_):
    hash_base{empty_init,std::move(h_)},
    pred_base{empty_init,std::move(pred_)},
    allocator_base{empty_init,al_},arrays(new_arrays(0)),
    size_ctrl{initial_max_load(),0}
  {
  }

#ifdef BOOST_GCC
#pragma GCC diagnostic pop
#endif

  arrays_type new_arrays(std::size_t n)const
  {
    return arrays_type::new_(typename arrays_type::allocator_type(al()),n);
  }

  arrays_type new_arrays_for_growth()const
  {
    /* Due to the anti-drift mechanism (see recover_slot), the new arrays may
     * be of the same size as the old arrays; in the limit, erasing one
     * element at full load and then inserting could bring us back to the same
     * capacity after a costly rehash. To avoid this, we jump to the next
     * capacity level when the number of erased elements is <= 10% of total
     * elements at full load, which is implemented by requesting additional
     * F*size elements, with F = P * 10% / (1 - P * 10%), where P is the
     * probability of an element having caused overflow; P has been measured as
     * ~0.162 under ideal conditions, yielding F ~ 0.0165 ~ 1/61.
     */
    return new_arrays(std::size_t(
      std::ceil(static_cast<float>(size()+size()/61+1)/mlf)));
  }

  void delete_arrays(arrays_type& arrays_)noexcept
  {
    arrays_type::delete_(typename arrays_type::allocator_type(al()),arrays_);
  }

  arrays_holder_type make_arrays(std::size_t n)const
  {
    return {new_arrays(n),al()};
  }

  template<typename Key,typename... Args>
  void construct_element_from_try_emplace_args(
    element_type* p,std::false_type,Key&& x,Args&&... args)
  {
    type_policy::construct(
      this->al(),p,
      std::piecewise_construct,
      std::forward_as_tuple(std::forward<Key>(x)),
      std::forward_as_tuple(std::forward<Args>(args)...));
  }

  /* This overload allows boost::unordered_flat_set to internally use
   * try_emplace to implement heterogeneous insert (P2363).
   */

  template<typename Key>
  void construct_element_from_try_emplace_args(
    element_type* p,std::true_type,Key&& x)
  {
    type_policy::construct(this->al(),p,std::forward<Key>(x));
  }

  void copy_elements_from(const table_core& x)
  {
    BOOST_ASSERT(empty());
    BOOST_ASSERT(this!=std::addressof(x));
    if(arrays.groups_size_mask==x.arrays.groups_size_mask){
      fast_copy_elements_from(x);
    }
    else{
      x.for_all_elements([this](const element_type* p){
        unchecked_insert(*p);
      });
    }
  }

  void fast_copy_elements_from(const table_core& x)
  {
    if(arrays.elements()&&x.arrays.elements()){
      copy_elements_array_from(x);
      copy_groups_array_from(x);
      size_ctrl.ml=std::size_t(x.size_ctrl.ml);
      size_ctrl.size=std::size_t(x.size_ctrl.size);
    }
  }

  void copy_elements_array_from(const table_core& x)
  {
    copy_elements_array_from(
      x,
      std::integral_constant<
        bool,
        is_trivially_copy_constructible<element_type>::value&&(
          is_std_allocator<Allocator>::value||
          !alloc_has_construct<Allocator,value_type*,const value_type&>::value)
      >{}
    );
  }

  void copy_elements_array_from(
    const table_core& x,std::true_type /* -> memcpy */)
  {
    /* reinterpret_cast: GCC may complain about value_type not being trivially
     * copy-assignable when we're relying on trivial copy constructibility.
     */
    std::memcpy(
      reinterpret_cast<unsigned char*>(arrays.elements()),
      reinterpret_cast<unsigned char*>(x.arrays.elements()),
      x.capacity()*sizeof(value_type));
  }

  void copy_elements_array_from(
    const table_core& x,std::false_type /* -> manual */)
  {
    std::size_t num_constructed=0;
    BOOST_TRY{
      x.for_all_elements([&,this](const element_type* p){
        construct_element(arrays.elements()+(p-x.arrays.elements()),*p);
        ++num_constructed;
      });
    }
    BOOST_CATCH(...){
      if(num_constructed){
        x.for_all_elements_while([&,this](const element_type* p){
          destroy_element(arrays.elements()+(p-x.arrays.elements()));
          return --num_constructed!=0;
        });
      }
      BOOST_RETHROW
    }
    BOOST_CATCH_END
  }

  void copy_groups_array_from(const table_core& x) {
    copy_groups_array_from(x,is_trivially_copy_assignable<group_type>{});
  }

  void copy_groups_array_from(
    const table_core& x, std::true_type /* -> memcpy */)
  {
    std::memcpy(
      arrays.groups(),x.arrays.groups(),
      (arrays.groups_size_mask+1)*sizeof(group_type));
  }

  void copy_groups_array_from(
    const table_core& x, std::false_type /* -> manual */)
  {
    auto pg=arrays.groups();
    auto xpg=x.arrays.groups();
    for(std::size_t i=0;i<arrays.groups_size_mask+1;++i){
      pg[i]=xpg[i];
    }
  }

  void recover_slot(unsigned char* pc)
  {
    /* If this slot potentially caused overflow, we decrease the maximum load
     * so that average probe length won't increase unboundedly in repeated
     * insert/erase cycles (drift).
     */
    size_ctrl.ml-=group_type::maybe_caused_overflow(pc);
    group_type::reset(pc);
    --size_ctrl.size;
  }

  void recover_slot(group_type* pg,std::size_t pos)
  {
    recover_slot(reinterpret_cast<unsigned char*>(pg)+pos);
  }

  static std::size_t capacity_for(std::size_t n)
  {
    return size_policy::size(size_index_for<group_type,size_policy>(n))*N-1;
  }

  BOOST_NOINLINE void unchecked_rehash(std::size_t n)
  {
    auto new_arrays_=new_arrays(n);
    unchecked_rehash(new_arrays_);
  }

  BOOST_NOINLINE void unchecked_rehash(arrays_type& new_arrays_)
  {
    std::size_t num_destroyed=0;
    BOOST_TRY{
      for_all_elements([&,this](element_type* p){
        nosize_transfer_element(p,new_arrays_,num_destroyed);
      });
    }
    BOOST_CATCH(...){
      if(num_destroyed){
        for_all_elements_while(
          [&,this](group_type* pg,unsigned int n,element_type*){
            recover_slot(pg,n);
            return --num_destroyed!=0;
          }
        );
      }
      for_all_elements(new_arrays_,[this](element_type* p){
        destroy_element(p);
      });
      delete_arrays(new_arrays_);
      BOOST_RETHROW
    }
    BOOST_CATCH_END

    /* either all moved and destroyed or all copied */
    BOOST_ASSERT(num_destroyed==size()||num_destroyed==0);
    if(num_destroyed!=size()){
      for_all_elements([this](element_type* p){
        destroy_element(p);
      });
    }
    delete_arrays(arrays);
    arrays=new_arrays_;
    size_ctrl.ml=initial_max_load();
  }

  template<typename Value>
  void unchecked_insert(Value&& x)
  {
    auto hash=hash_for(key_from(x));
    unchecked_emplace_at(position_for(hash),hash,std::forward<Value>(x));
  }

  void nosize_transfer_element(
    element_type* p,const arrays_type& arrays_,std::size_t& num_destroyed)
  {
    nosize_transfer_element(
      p,hash_for(key_from(*p)),arrays_,num_destroyed,
      std::integral_constant<
        bool,
        std::is_nothrow_move_constructible<init_type>::value||
        !std::is_same<element_type,value_type>::value||
        !std::is_copy_constructible<element_type>::value>{});
  }

  void nosize_transfer_element(
    element_type* p,std::size_t hash,const arrays_type& arrays_,
    std::size_t& num_destroyed,std::true_type /* ->move */)
  {
    /* Destroy p even if an an exception is thrown in the middle of move
     * construction, which could leave the source half-moved.
     */
    ++num_destroyed;
    destroy_element_on_exit d{this,p};
    (void)d;
    nosize_unchecked_emplace_at(
      arrays_,position_for(hash,arrays_),hash,type_policy::move(*p));
  }

  void nosize_transfer_element(
    element_type* p,std::size_t hash,const arrays_type& arrays_,
    std::size_t& /*num_destroyed*/,std::false_type /* ->copy */)
  {
    nosize_unchecked_emplace_at(
      arrays_,position_for(hash,arrays_),hash,
      const_cast<const element_type&>(*p));
  }

  template<typename... Args>
  locator nosize_unchecked_emplace_at(
    const arrays_type& arrays_,std::size_t pos0,std::size_t hash,
    Args&&... args)
  {
    for(prober pb(pos0);;pb.next(arrays_.groups_size_mask)){
      auto pos=pb.get();
      auto pg=arrays_.groups()+pos;
      auto mask=pg->match_available();
      if(BOOST_LIKELY(mask!=0)){
        auto n=unchecked_countr_zero(mask);
        auto p=arrays_.elements()+pos*N+n;
        construct_element(p,std::forward<Args>(args)...);
        pg->set(n,hash);
        BOOST_UNORDERED_ADD_STATS(cstats.insertion,(pb.length()));
        return {pg,n,p};
      }
      else pg->mark_overflow(hash);
    }
  }
};

#ifdef BOOST_MSVC
#pragma warning(pop)
#endif

}
}
}
}

#undef BOOST_UNORDERED_STATIC_ASSERT_HASH_PRED
#undef BOOST_UNORDERED_HAS_FEATURE
#undef BOOST_UNORDERED_HAS_BUILTIN
#endif
/* Copyright 2023 Joaquin M Lopez Munoz.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifndef BOOST_UNORDERED_DETAIL_BAD_ARCHIVE_EXCEPTION_HPP
#define BOOST_UNORDERED_DETAIL_BAD_ARCHIVE_EXCEPTION_HPP

namespace boost{
namespace unordered{
namespace detail{

struct bad_archive_exception:std::runtime_error
{
  bad_archive_exception():std::runtime_error("Invalid or corrupted archive"){}
};

}
}
}

#endif
#ifndef BOOST_ASSERT_SOURCE_LOCATION_HPP_INCLUDED
#define BOOST_ASSERT_SOURCE_LOCATION_HPP_INCLUDED

// http://www.boost.org/libs/assert
//
// Copyright 2019, 2021 Peter Dimov
// Distributed under the Boost Software License, Version 1.0.
// http://www.boost.org/LICENSE_1_0.txt

#if defined(__cpp_lib_source_location) && __cpp_lib_source_location >= 201907L
# include <source_location>
#endif

namespace boost
{

struct source_location
{
private:

    char const * file_;
    char const * function_;
    std::uint_least32_t line_;
    std::uint_least32_t column_;

public:

    constexpr source_location() noexcept: file_( "" ), function_( "" ), line_( 0 ), column_( 0 )
    {
    }

    constexpr source_location( char const * file, std::uint_least32_t ln, char const * function, std::uint_least32_t col = 0 ) noexcept: file_( file ), function_( function ), line_( ln ), column_( col )
    {
    }

#if defined(__cpp_lib_source_location) && __cpp_lib_source_location >= 201907L

    constexpr source_location( std::source_location const& loc ) noexcept: file_( loc.file_name() ), function_( loc.function_name() ), line_( loc.line() ), column_( loc.column() )
    {
    }

#endif

    constexpr char const * file_name() const noexcept
    {
        return file_;
    }

    constexpr char const * function_name() const noexcept
    {
        return function_;
    }

    constexpr std::uint_least32_t line() const noexcept
    {
        return line_;
    }

    constexpr std::uint_least32_t column() const noexcept
    {
        return column_;
    }

#ifdef BOOST_MSVC
# pragma warning( push )
# pragma warning( disable: 4996 )
#endif

#if ( defined(_MSC_VER) && _MSC_VER < 1900 ) || ( defined(__MINGW32__) && !defined(__MINGW64_VERSION_MAJOR) )
# define BOOST_ASSERT_SNPRINTF(buffer, format, arg) std::sprintf(buffer, format, arg)
#else
# define BOOST_ASSERT_SNPRINTF(buffer, format, arg) std::snprintf(buffer, sizeof(buffer)/sizeof(buffer[0]), format, arg)
#endif

    std::string to_string() const
    {
        unsigned long ln = line();

        if( ln == 0 )
        {
            return "(unknown source location)";
        }

        std::string r = file_name();

        char buffer[ 16 ];

        BOOST_ASSERT_SNPRINTF( buffer, ":%lu", ln );
        r += buffer;

        unsigned long co = column();

        if( co )
        {
            BOOST_ASSERT_SNPRINTF( buffer, ":%lu", co );
            r += buffer;
        }

        char const* fn = function_name();

        if( *fn != 0 )
        {
            r += " in function '";
            r += fn;
            r += '\'';
        }

        return r;
    }

#undef BOOST_ASSERT_SNPRINTF

#ifdef BOOST_MSVC
# pragma warning( pop )
#endif

    inline friend bool operator==( source_location const& s1, source_location const& s2 ) noexcept
    {
        return std::strcmp( s1.file_, s2.file_ ) == 0 && std::strcmp( s1.function_, s2.function_ ) == 0 && s1.line_ == s2.line_ && s1.column_ == s2.column_;
    }

    inline friend bool operator!=( source_location const& s1, source_location const& s2 ) noexcept
    {
        return !( s1 == s2 );
    }
};

#ifndef BOOST_NO_IOSTREAM

template<class E, class T> std::basic_ostream<E, T> & operator<<( std::basic_ostream<E, T> & os, source_location const & loc )
{
    os << loc.to_string();
    return os;
}

#endif

} // namespace boost

#ifdef BOOST_DISABLE_CURRENT_LOCATION

# define BOOST_CURRENT_LOCATION ::boost::source_location()

#elif defined(BOOST_MSVC) && BOOST_MSVC >= 1935

# define BOOST_CURRENT_LOCATION ::boost::source_location(__builtin_FILE(), __builtin_LINE(), __builtin_FUNCSIG(), __builtin_COLUMN())

#elif defined(BOOST_MSVC) && BOOST_MSVC >= 1926

// std::source_location::current() is available in -std:c++20, but fails with consteval errors before 19.31, and doesn't produce
// the correct result under 19.31, so prefer the built-ins
# define BOOST_CURRENT_LOCATION ::boost::source_location(__builtin_FILE(), __builtin_LINE(), __builtin_FUNCTION(), __builtin_COLUMN())

#elif defined(BOOST_MSVC)

// __LINE__ is not a constant expression under /ZI (edit and continue) for 1925 and before

# define BOOST_CURRENT_LOCATION_IMPL_1(x) BOOST_CURRENT_LOCATION_IMPL_2(x)
# define BOOST_CURRENT_LOCATION_IMPL_2(x) (x##0 / 10)

# define BOOST_CURRENT_LOCATION ::boost::source_location(__FILE__, BOOST_CURRENT_LOCATION_IMPL_1(__LINE__), "")

#elif defined(__cpp_lib_source_location) && __cpp_lib_source_location >= 201907L && !defined(__NVCC__)

// Under nvcc, __builtin_source_location is not constexpr
// https://github.com/boostorg/assert/issues/32

# define BOOST_CURRENT_LOCATION ::boost::source_location(::std::source_location::current())

#elif defined(BOOST_CLANG) && BOOST_CLANG_VERSION >= 90000

# define BOOST_CURRENT_LOCATION ::boost::source_location(__builtin_FILE(), __builtin_LINE(), __builtin_FUNCTION(), __builtin_COLUMN())

#elif defined(BOOST_GCC) && BOOST_GCC >= 80000

// The built-ins are available in 4.8+, but are not constant expressions until 7
// In addition, reproducible builds require -ffile-prefix-map, which is GCC 8
// https://github.com/boostorg/assert/issues/38

# define BOOST_CURRENT_LOCATION ::boost::source_location(__builtin_FILE(), __builtin_LINE(), __builtin_FUNCTION())

#elif defined(BOOST_GCC) && BOOST_GCC >= 50000

// __PRETTY_FUNCTION__ is allowed outside functions under GCC, but 4.x suffers from codegen bugs
# define BOOST_CURRENT_LOCATION ::boost::source_location(__FILE__, __LINE__, __PRETTY_FUNCTION__)

#else

// __func__ macros aren't allowed outside functions, but BOOST_CURRENT_LOCATION is
# define BOOST_CURRENT_LOCATION ::boost::source_location(__FILE__, __LINE__, "")

#endif

#endif // #ifndef BOOST_ASSERT_SOURCE_LOCATION_HPP_INCLUDED
//Copyright (c) 2006-2009 Emil Dotchevski and Reverge Studios, Inc.

//Distributed under the Boost Software License, Version 1.0. (See accompanying
//file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_EXCEPTION_274DA366004E11DCB1DDFE2E56D89593
#define BOOST_EXCEPTION_274DA366004E11DCB1DDFE2E56D89593

#ifdef BOOST_EXCEPTION_MINI_BOOST
#include  <memory>
namespace boost { namespace exception_detail { using std::shared_ptr; } }
#else
namespace boost { template <class T> class shared_ptr; }
namespace boost { namespace exception_detail { using boost::shared_ptr; } }
#endif

#ifndef BOOST_EXCEPTION_ENABLE_WARNINGS
#if defined(__GNUC__) && __GNUC__*100+__GNUC_MINOR__>301
#pragma GCC system_header
#endif
#ifdef __clang__
#pragma clang system_header
#endif
#ifdef _MSC_VER
#pragma warning(push,1)
#pragma warning(disable: 4265)
#endif
#endif

namespace
boost
    {
    namespace
    exception_detail
        {
        template <class T>
        class
        refcount_ptr
            {
            public:

            refcount_ptr():
                px_(0)
                {
                }

            ~refcount_ptr()
                {
                release();
                }

            refcount_ptr( refcount_ptr const & x ):
                px_(x.px_)
                {
                add_ref();
                }

            refcount_ptr &
            operator=( refcount_ptr const & x )
                {
                adopt(x.px_);
                return *this;
                }

            void
            adopt( T * px )
                {
                release();
                px_=px;
                add_ref();
                }

            T *
            get() const
                {
                return px_;
                }

            private:

            T * px_;

            void
            add_ref()
                {
                if( px_ )
                    px_->add_ref();
                }

            void
            release()
                {
                if( px_ && px_->release() )
                    px_=0;
                }
            };
        }

    ////////////////////////////////////////////////////////////////////////

    template <class Tag,class T>
    class error_info;

    typedef error_info<struct throw_function_,char const *> throw_function;
    typedef error_info<struct throw_file_,char const *> throw_file;
    typedef error_info<struct throw_line_,int> throw_line;
    typedef error_info<struct throw_column_,int> throw_column;

    template <>
    class
    error_info<throw_function_,char const *>
        {
        public:
        typedef char const * value_type;
        value_type v_;
        explicit
        error_info( value_type v ):
            v_(v)
            {
            }
        };

    template <>
    class
    error_info<throw_file_,char const *>
        {
        public:
        typedef char const * value_type;
        value_type v_;
        explicit
        error_info( value_type v ):
            v_(v)
            {
            }
        };

    template <>
    class
    error_info<throw_line_,int>
        {
        public:
        typedef int value_type;
        value_type v_;
        explicit
        error_info( value_type v ):
            v_(v)
            {
            }
        };

    template <>
    class
    error_info<throw_column_,int>
        {
        public:
        typedef int value_type;
        value_type v_;
        explicit
        error_info( value_type v ):
            v_(v)
            {
            }
        };

    class
    BOOST_SYMBOL_VISIBLE
    exception;

    namespace
    exception_detail
        {
        class error_info_base;
        struct type_info_;

        struct
        error_info_container
            {
            virtual char const * diagnostic_information( char const * ) const = 0;
            virtual shared_ptr<error_info_base> get( type_info_ const & ) const = 0;
            virtual void set( shared_ptr<error_info_base> const &, type_info_ const & ) = 0;
            virtual void add_ref() const = 0;
            virtual bool release() const = 0;
            virtual refcount_ptr<exception_detail::error_info_container> clone() const = 0;

            protected:

            ~error_info_container() noexcept
                {
                }
            };

        template <class>
        struct get_info;

        template <>
        struct get_info<throw_function>;

        template <>
        struct get_info<throw_file>;

        template <>
        struct get_info<throw_line>;

        template <>
        struct get_info<throw_column>;

        template <class>
        struct set_info_rv;

        template <>
        struct set_info_rv<throw_function>;

        template <>
        struct set_info_rv<throw_file>;

        template <>
        struct set_info_rv<throw_line>;

        template <>
        struct set_info_rv<throw_column>;

        char const * get_diagnostic_information( exception const &, char const * );

        void copy_boost_exception( exception *, exception const * );

        template <class E,class Tag,class T>
        E const & set_info( E const &, error_info<Tag,T> const & );

        template <class E>
        E const & set_info( E const &, throw_function const & );

        template <class E>
        E const & set_info( E const &, throw_file const & );

        template <class E>
        E const & set_info( E const &, throw_line const & );

        template <class E>
        E const & set_info( E const &, throw_column const & );

        boost::source_location get_exception_throw_location( exception const & );
        }

    class
    BOOST_SYMBOL_VISIBLE
    exception
        {
        //<N3757>
        public:
        template <class Tag> void set( typename Tag::type const & );
        template <class Tag> typename Tag::type const * get() const;
        //</N3757>

        protected:

        exception():
            throw_function_(0),
            throw_file_(0),
            throw_line_(-1),
            throw_column_(-1)
            {
            }

#ifdef __HP_aCC
        //On HP aCC, this protected copy constructor prevents throwing boost::exception.
        //On all other platforms, the same effect is achieved by the pure virtual destructor.
        exception( exception const & x ) noexcept:
            data_(x.data_),
            throw_function_(x.throw_function_),
            throw_file_(x.throw_file_),
            throw_line_(x.throw_line_),
            throw_column_(x.throw_column_)
            {
            }
#endif

        virtual ~exception() noexcept
#ifndef __HP_aCC
            = 0 //Workaround for HP aCC, =0 incorrectly leads to link errors.
#endif
            ;

#if (defined(__MWERKS__) && __MWERKS__<=0x3207) || (defined(_MSC_VER) && _MSC_VER<=1310)
        public:
#else
        private:

        template <class E>
        friend E const & exception_detail::set_info( E const &, throw_function const & );

        template <class E>
        friend E const & exception_detail::set_info( E const &, throw_file const & );

        template <class E>
        friend E const & exception_detail::set_info( E const &, throw_line const & );

        template <class E>
        friend E const & exception_detail::set_info( E const &, throw_column const & );

        template <class E,class Tag,class T>
        friend E const & exception_detail::set_info( E const &, error_info<Tag,T> const & );

        friend char const * exception_detail::get_diagnostic_information( exception const &, char const * );

        friend boost::source_location exception_detail::get_exception_throw_location( exception const & );

        template <class>
        friend struct exception_detail::get_info;
        friend struct exception_detail::get_info<throw_function>;
        friend struct exception_detail::get_info<throw_file>;
        friend struct exception_detail::get_info<throw_line>;
        friend struct exception_detail::get_info<throw_column>;
        template <class>
        friend struct exception_detail::set_info_rv;
        friend struct exception_detail::set_info_rv<throw_function>;
        friend struct exception_detail::set_info_rv<throw_file>;
        friend struct exception_detail::set_info_rv<throw_line>;
        friend struct exception_detail::set_info_rv<throw_column>;
        friend void exception_detail::copy_boost_exception( exception *, exception const * );
#endif
        mutable exception_detail::refcount_ptr<exception_detail::error_info_container> data_;
        mutable char const * throw_function_;
        mutable char const * throw_file_;
        mutable int throw_line_;
        mutable int throw_column_;
        };

    inline
    exception::
    ~exception() noexcept
        {
        }

    namespace
    exception_detail
        {
        template <class E>
        E const &
        set_info( E const & x, throw_function const & y )
            {
            x.throw_function_=y.v_;
            return x;
            }

        template <class E>
        E const &
        set_info( E const & x, throw_file const & y )
            {
            x.throw_file_=y.v_;
            return x;
            }

        template <class E>
        E const &
        set_info( E const & x, throw_line const & y )
            {
            x.throw_line_=y.v_;
            return x;
            }

        template <class E>
        E const &
        set_info( E const & x, throw_column const & y )
            {
            x.throw_column_=y.v_;
            return x;
            }

        template <>
        struct
        set_info_rv<throw_column>
            {
            template <class E>
            static
            E const &
            set( E const & x, throw_column && y )
                {
                x.throw_column_=y.v_;
                return x;
                }
            };

        inline boost::source_location get_exception_throw_location( exception const & x )
            {
            return boost::source_location(
                x.throw_file_? x.throw_file_: "",
                x.throw_line_ >= 0? x.throw_line_: 0,
                x.throw_function_? x.throw_function_: "",
                x.throw_column_ >= 0? x.throw_column_: 0
                );
            }
        }

    ////////////////////////////////////////////////////////////////////////

    namespace
    exception_detail
        {
        template <class T>
        struct
        BOOST_SYMBOL_VISIBLE
        error_info_injector:
            public T,
            public exception
            {
            explicit
            error_info_injector( T const & x ):
                T(x)
                {
                }

            ~error_info_injector() noexcept
                {
                }
            };

        struct large_size { char c[256]; };
        large_size dispatch_boost_exception( exception const * );

        struct small_size { };
        small_size dispatch_boost_exception( void const * );

        template <class,int>
        struct enable_error_info_helper;

        template <class T>
        struct
        enable_error_info_helper<T,sizeof(large_size)>
            {
            typedef T type;
            };

        template <class T>
        struct
        enable_error_info_helper<T,sizeof(small_size)>
            {
            typedef error_info_injector<T> type;
            };

        template <class T>
        struct
        enable_error_info_return_type
            {
            typedef typename enable_error_info_helper<T,sizeof(exception_detail::dispatch_boost_exception(static_cast<T *>(0)))>::type type;
            };
        }

    template <class T>
    inline
    typename
    exception_detail::enable_error_info_return_type<T>::type
    enable_error_info( T const & x )
        {
        typedef typename exception_detail::enable_error_info_return_type<T>::type rt;
        return rt(x);
        }

    ////////////////////////////////////////////////////////////////////////
#ifdef BOOST_NO_EXCEPTIONS
    BOOST_NORETURN void throw_exception(std::exception const & e); // user defined
#endif

    namespace
    exception_detail
        {
        class
        BOOST_SYMBOL_VISIBLE
        clone_base
            {
            public:

            virtual clone_base const * clone() const = 0;
            virtual void rethrow() const = 0;

            virtual
            ~clone_base() noexcept
                {
                }
            };

        inline
        void
        copy_boost_exception( exception * a, exception const * b )
            {
            refcount_ptr<error_info_container> data;
            if( error_info_container * d=b->data_.get() )
                data = d->clone();
            a->throw_file_ = b->throw_file_;
            a->throw_line_ = b->throw_line_;
            a->throw_function_ = b->throw_function_;
            a->throw_column_ = b->throw_column_;
            a->data_ = data;
            }

        inline
        void
        copy_boost_exception( void *, void const * )
            {
            }

        template <class T>
        class
        BOOST_SYMBOL_VISIBLE
        clone_impl:
            public T,
            public virtual clone_base
            {
            struct clone_tag { };
            clone_impl( clone_impl const & x, clone_tag ):
                T(x)
                {
                copy_boost_exception(this,&x);
                }

            public:

            explicit
            clone_impl( T const & x ):
                T(x)
                {
                copy_boost_exception(this,&x);
                }

            ~clone_impl() noexcept
                {
                }

            private:

            clone_base const *
            clone() const
                {
                return new clone_impl(*this,clone_tag());
                }

            void
            rethrow() const
                {
#ifdef BOOST_NO_EXCEPTIONS
                boost::throw_exception(*this);
#else
                throw*this;
#endif
                }
            };
        }

    template <class T>
    inline
    exception_detail::clone_impl<T>
    enable_current_exception( T const & x )
        {
        return exception_detail::clone_impl<T>(x);
        }
    }

#if defined(_MSC_VER) && !defined(BOOST_EXCEPTION_ENABLE_WARNINGS)
#pragma warning(pop)
#endif

#endif // #ifndef BOOST_EXCEPTION_274DA366004E11DCB1DDFE2E56D89593
#ifndef BOOST_THROW_EXCEPTION_HPP_INCLUDED
#define BOOST_THROW_EXCEPTION_HPP_INCLUDED

// MS compatible compilers support #pragma once

#if defined(_MSC_VER) && (_MSC_VER >= 1020)
# pragma once
#endif

//  boost/throw_exception.hpp
//
//  Copyright (c) 2002, 2018-2022 Peter Dimov
//  Copyright (c) 2008-2009 Emil Dotchevski and Reverge Studios, Inc.
//
//  Distributed under the Boost Software License, Version 1.0. (See
//  accompanying file LICENSE_1_0.txt or copy at
//  http://www.boost.org/LICENSE_1_0.txt)
//
//  http://www.boost.org/libs/throw_exception

namespace boost
{

#ifdef  BOOST_NO_EXCEPTIONS

BOOST_NORETURN void throw_exception( std::exception const & e ); // user defined
BOOST_NORETURN void throw_exception( std::exception const & e, boost::source_location const & loc ); // user defined

#endif

// boost::wrapexcept<E>

namespace detail
{

typedef char (&wrapexcept_s1)[ 1 ];
typedef char (&wrapexcept_s2)[ 2 ];

template<class T> wrapexcept_s1 wrapexcept_is_convertible( T* );
template<class T> wrapexcept_s2 wrapexcept_is_convertible( void* );

template<class E, class B, std::size_t I = sizeof( wrapexcept_is_convertible<B>( static_cast< E* >( nullptr ) ) ) > struct wrapexcept_add_base;

template<class E, class B> struct wrapexcept_add_base<E, B, 1>
{
    struct type {};
};

template<class E, class B> struct wrapexcept_add_base<E, B, 2>
{
    typedef B type;
};

} // namespace detail

template<class E> struct BOOST_SYMBOL_VISIBLE wrapexcept:
    public detail::wrapexcept_add_base<E, boost::exception_detail::clone_base>::type,
    public E,
    public detail::wrapexcept_add_base<E, boost::exception>::type
{
private:

    struct deleter
    {
        wrapexcept * p_;
        ~deleter() { delete p_; }
    };

private:

    void copy_from( void const* )
    {
    }

    void copy_from( boost::exception const* p )
    {
        static_cast<boost::exception&>( *this ) = *p;
    }

public:

    explicit wrapexcept( E const & e ): E( e )
    {
        copy_from( &e );
    }

    explicit wrapexcept( E const & e, boost::source_location const & loc ): E( e )
    {
        copy_from( &e );

        set_info( *this, throw_file( loc.file_name() ) );
        set_info( *this, throw_line( static_cast<int>( loc.line() ) ) );
        set_info( *this, throw_function( loc.function_name() ) );
        set_info( *this, throw_column( static_cast<int>( loc.column() ) ) );
    }

    virtual boost::exception_detail::clone_base const * clone() const override
    {
        wrapexcept * p = new wrapexcept( *this );
        deleter del = { p };

        boost::exception_detail::copy_boost_exception( p, this );

        del.p_ = nullptr;
        return p;
    }

    virtual void rethrow() const override
    {
#ifdef  BOOST_NO_EXCEPTIONS

        boost::throw_exception( *this );

#else

        throw *this;

#endif
    }
};

// All boost exceptions are required to derive from std::exception,
// to ensure compatibility with BOOST_NO_EXCEPTIONS.

inline void throw_exception_assert_compatibility( std::exception const & ) {}

// boost::throw_exception

#ifndef  BOOST_NO_EXCEPTIONS

#ifdef  BOOST_EXCEPTION_DISABLE

template<class E> BOOST_NORETURN void throw_exception( E const & e )
{
    throw_exception_assert_compatibility( e );
    throw e;
}

template<class E> BOOST_NORETURN void throw_exception( E const & e, boost::source_location const & )
{
    throw_exception_assert_compatibility( e );
    throw e;
}

#else // defined( BOOST_EXCEPTION_DISABLE )

template<class E> BOOST_NORETURN void throw_exception( E const & e )
{
    throw_exception_assert_compatibility( e );
    throw wrapexcept<E>( e );
}

template<class E> BOOST_NORETURN void throw_exception( E const & e, boost::source_location const & loc )
{
    throw_exception_assert_compatibility( e );
    throw wrapexcept<E>( e, loc );
}

#endif // defined( BOOST_EXCEPTION_DISABLE )

#endif // !defined( BOOST_NO_EXCEPTIONS )

} // namespace boost

// BOOST_THROW_EXCEPTION

#define BOOST_THROW_EXCEPTION(x) ::boost::throw_exception(x, BOOST_CURRENT_LOCATION)

namespace boost
{

// throw_with_location

namespace detail
{

struct BOOST_SYMBOL_VISIBLE throw_location
{
    boost::source_location location_;

    explicit throw_location( boost::source_location const & loc ): location_( loc )
    {
    }
};

template<class E> class BOOST_SYMBOL_VISIBLE with_throw_location: public E, public throw_location
{
public:

    with_throw_location( E const & e, boost::source_location const & loc ): E( e ), throw_location( loc )
    {
    }

    with_throw_location( E && e, boost::source_location const & loc ): E( std::move( e ) ), throw_location( loc )
    {
    }

};

} // namespace detail

#ifndef BOOST_NO_EXCEPTIONS

#ifndef BOOST_NO_CXX11_HDR_TYPE_TRAITS

template<class E> BOOST_NORETURN void throw_with_location( E && e, boost::source_location const & loc = BOOST_CURRENT_LOCATION )
{
    throw_exception_assert_compatibility( e );
    throw detail::with_throw_location<typename std::decay<E>::type>( std::forward<E>( e ), loc );
}

#else

template<class E> BOOST_NORETURN void throw_with_location( E const & e, boost::source_location const & loc = BOOST_CURRENT_LOCATION )
{
    throw_exception_assert_compatibility( e );
    throw detail::with_throw_location<E>( e, loc );
}

#endif

#else

template<class E> BOOST_NORETURN void throw_with_location( E const & e, boost::source_location const & loc = BOOST_CURRENT_LOCATION )
{
    boost::throw_exception( e, loc );
}

#endif

// get_throw_location

template<class E> boost::source_location get_throw_location( E const & e )
{
#ifdef BOOST_NO_RTTI

    (void)e;
    return boost::source_location();

#else

    if( detail::throw_location const* pl = dynamic_cast< detail::throw_location const* >( &e ) )
    {
        return pl->location_;
    }
    else if( boost::exception const* px = dynamic_cast< boost::exception const* >( &e ) )
    {
        return exception_detail::get_exception_throw_location( *px );
    }
    else
    {
        return boost::source_location();
    }

#endif
}

} // namespace boost

#endif // #ifndef BOOST_THROW_EXCEPTION_HPP_INCLUDED
/* Copyright 2023 Joaquin M Lopez Munoz.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifndef BOOST_UNORDERED_DETAIL_SERIALIZE_TRACKED_ADDRESS_HPP
#define BOOST_UNORDERED_DETAIL_SERIALIZE_TRACKED_ADDRESS_HPP

namespace boost{
namespace unordered{
namespace detail{

/* Tracked address serialization to support iterator serialization as described
 * in serialize_container.hpp. The underlying technique is to reinterpret_cast
 * T pointers to serialization_tracker<T> pointers, which, when dereferenced
 * and serialized, do not emit any serialization payload to the
 * archive, but activate object tracking on the relevant addresses for later
 * use with serialize_tracked_address().
 */

template<typename T>
struct serialization_tracker
{
  /* An attempt to construct a serialization_tracker means a stray address
   * in the archive, that is, one without a previously tracked address.
   */
  serialization_tracker(){throw_exception(bad_archive_exception());}

  template<typename Archive>
  void serialize(Archive&,unsigned int){}
};

template<typename Archive,typename Ptr>
void track_address(Archive& ar,Ptr p)
{
  typedef typename std::pointer_traits<Ptr> ptr_traits;
  typedef typename std::remove_const<
    typename ptr_traits::element_type>::type  element_type;

  if(p){
    ar&core::make_nvp(
      "address",
      *reinterpret_cast<serialization_tracker<element_type>*>(
        const_cast<element_type*>(
          std::to_address(p))));
  }
}

template<typename Archive,typename Ptr>
void serialize_tracked_address(Archive& ar,Ptr& p,std::true_type /* save */)
{
  typedef typename std::pointer_traits<Ptr> ptr_traits;
  typedef typename std::remove_const<
    typename ptr_traits::element_type>::type  element_type;
  typedef serialization_tracker<element_type> tracker;

  tracker* pt=
    const_cast<tracker*>(
      reinterpret_cast<const tracker*>(
        const_cast<const element_type*>(
          std::to_address(p))));
  ar<<core::make_nvp("pointer",pt);
}

template<typename Archive,typename Ptr>
void serialize_tracked_address(Archive& ar,Ptr& p,std::false_type /* load */)
{
  typedef typename std::pointer_traits<Ptr> ptr_traits;
  typedef typename std::remove_const<
    typename ptr_traits::element_type>::type  element_type;
  typedef serialization_tracker<element_type> tracker;

  tracker* pt;
  ar>>core::make_nvp("pointer",pt);
  element_type* pn=const_cast<element_type*>(
    reinterpret_cast<const element_type*>(
      const_cast<const tracker*>(pt)));
  p=pn?ptr_traits::pointer_to(*pn):0;
}

template<typename Archive,typename Ptr>
void serialize_tracked_address(Archive& ar,Ptr& p)
{
  serialize_tracked_address(
    ar,p,
    std::integral_constant<bool,Archive::is_saving::value>());
}

}
}
}

#endif
/* Fast open-addressing hash table.
 *
 * Copyright 2022-2024 Joaquin M Lopez Munoz.
 * Copyright 2023 Christian Mazakas.
 * Copyright 2024 Braden Ganetsky.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifndef BOOST_UNORDERED_DETAIL_FOA_TABLE_HPP
#define BOOST_UNORDERED_DETAIL_FOA_TABLE_HPP

namespace boost{
namespace unordered{
namespace detail{
namespace foa{

/* use plain integrals for group metadata storage */

template<typename Integral>
struct plain_integral
{
  operator Integral()const{return n;}
  void operator=(Integral m){n=m;}

  void operator|=(Integral m){n|=m;}
  void operator&=(Integral m){n&=m;}

  Integral n;
};

struct plain_size_control
{
  std::size_t ml;
  std::size_t size;
};

template<typename,typename,typename,typename>
class table;

/* table_iterator keeps two pointers:
 *
 *   - A pointer p to the element slot.
 *   - A pointer pc to the n-th byte of the associated group metadata, where n
 *     is the position of the element in the group.
 *
 * A simpler solution would have been to keep a pointer p to the element, a
 * pointer pg to the group, and the position n, but that would increase
 * sizeof(table_iterator) by 4/8 bytes. In order to make this compact
 * representation feasible, it is required that group objects are aligned
 * to their size, so that we can recover pg and n as
 *
 *   - n = pc%sizeof(group)
 *   - pg = pc-n
 *
 * (for explanatory purposes pg and pc are treated above as if they were memory
 * addresses rather than pointers).
 *
 * p = nullptr is conventionally used to mark end() iterators.
 */

/* internal conversion from const_iterator to iterator */
struct const_iterator_cast_tag{};

template<typename TypePolicy,typename GroupPtr,bool Const>
class table_iterator
{
  using group_pointer_traits=std::pointer_traits<GroupPtr>;
  using type_policy=TypePolicy;
  using table_element_type=typename type_policy::element_type;
  using group_type=typename group_pointer_traits::element_type;
  using table_element_pointer=
    typename group_pointer_traits::template rebind<table_element_type>;
  using char_pointer=
    typename group_pointer_traits::template rebind<unsigned char>;
  static constexpr auto N=group_type::N;
  static constexpr auto regular_layout=group_type::regular_layout;

public:
  using difference_type=std::ptrdiff_t;
  using value_type=typename type_policy::value_type;
  using pointer=
    typename std::conditional<Const,value_type const*,value_type*>::type;
  using reference=
    typename std::conditional<Const,value_type const&,value_type&>::type;
  using iterator_category=std::forward_iterator_tag;
  using element_type=
    typename std::conditional<Const,value_type const,value_type>::type;

  table_iterator():pc_{nullptr},p_{nullptr}{};
  template<bool Const2,typename std::enable_if<!Const2>::type* =nullptr>
  table_iterator(const table_iterator<TypePolicy,GroupPtr,Const2>& x):
    pc_{x.pc_},p_{x.p_}{}
  table_iterator(
    const_iterator_cast_tag, const table_iterator<TypePolicy,GroupPtr,true>& x):
    pc_{x.pc_},p_{x.p_}{}

  inline reference operator*()const noexcept
    {return type_policy::value_from(*p());}
  inline pointer operator->()const noexcept
    {return std::addressof(type_policy::value_from(*p()));}
  inline table_iterator& operator++()noexcept{increment();return *this;}
  inline table_iterator operator++(int)noexcept
    {auto x=*this;increment();return x;}
  friend inline bool operator==(
    const table_iterator& x,const table_iterator& y)
    {return x.p()==y.p();}
  friend inline bool operator!=(
    const table_iterator& x,const table_iterator& y)
    {return !(x==y);}

private:
  template<typename,typename,bool> friend class table_iterator;
  template<typename> friend class table_erase_return_type;
  template<typename,typename,typename,typename> friend class table;

  table_iterator(group_type* pg,std::size_t n,const table_element_type* ptet):
    pc_{to_pointer<char_pointer>(
      reinterpret_cast<unsigned char*>(const_cast<group_type*>(pg))+n)},
    p_{to_pointer<table_element_pointer>(const_cast<table_element_type*>(ptet))}
  {}

  unsigned char* pc()const noexcept{return std::to_address(pc_);}
  table_element_type* p()const noexcept{return std::to_address(p_);}

  inline void increment()noexcept
  {
    BOOST_ASSERT(p()!=nullptr);
    increment(std::integral_constant<bool,regular_layout>{});
  }

  inline void increment(std::true_type /* regular layout */)noexcept
  {
    using diff_type=
      typename std::pointer_traits<char_pointer>::difference_type;

    for(;;){
      ++p_;
      if(reinterpret_cast<uintptr_t>(pc())%sizeof(group_type)==N-1){
        pc_+=static_cast<diff_type>(sizeof(group_type)-(N-1));
        break;
      }
      ++pc_;
      if(!group_type::is_occupied(pc()))continue;
      if(BOOST_UNLIKELY(group_type::is_sentinel(pc())))p_=nullptr;
      return;
    }

    for(;;){
      int mask=reinterpret_cast<group_type*>(pc())->match_occupied();
      if(mask!=0){
        auto n=unchecked_countr_zero(mask);
        if(BOOST_UNLIKELY(reinterpret_cast<group_type*>(pc())->is_sentinel(n))){
          p_=nullptr;
        }
        else{
          pc_+=static_cast<diff_type>(n);
          p_+=static_cast<diff_type>(n);
        }
        return;
      }
      pc_+=static_cast<diff_type>(sizeof(group_type));
      p_+=static_cast<diff_type>(N);
    }
  }

  inline void increment(std::false_type /* interleaved */)noexcept
  {
    using diff_type=
      typename std::pointer_traits<char_pointer>::difference_type;

    std::size_t n0=reinterpret_cast<uintptr_t>(pc())%sizeof(group_type);
    pc_-=static_cast<diff_type>(n0);

    int mask=(
      reinterpret_cast<group_type*>(pc())->match_occupied()>>(n0+1))<<(n0+1);
    if(!mask){
      do{
        pc_+=sizeof(group_type);
        p_+=N;
      }
      while((mask=reinterpret_cast<group_type*>(pc())->match_occupied())==0);
    }

    auto n=unchecked_countr_zero(mask);
    if(BOOST_UNLIKELY(reinterpret_cast<group_type*>(pc())->is_sentinel(n))){
      p_=nullptr;
    }
    else{
      pc_+=static_cast<diff_type>(n);
      p_-=static_cast<diff_type>(n0);
      p_+=static_cast<diff_type>(n);
    }
  }

  template<typename Archive>
  friend void serialization_track(Archive& ar,const table_iterator& x)
  {
    if(x.p()){
      track_address(ar,x.pc_);
      track_address(ar,x.p_);
    }
  }

  template<typename Archive>
  void serialize(Archive& ar,unsigned int)
  {
    if(!p())pc_=nullptr;
    serialize_tracked_address(ar,pc_);
    serialize_tracked_address(ar,p_);
  }

  char_pointer          pc_=nullptr;
  table_element_pointer  p_=nullptr;
};

/* Returned by table::erase([const_]iterator) to avoid iterator increment
 * if discarded.
 */

template<typename Iterator>
class table_erase_return_type;

template<typename TypePolicy,typename GroupPtr,bool Const>
class table_erase_return_type<table_iterator<TypePolicy,GroupPtr,Const>>
{
  using iterator=table_iterator<TypePolicy,GroupPtr,Const>;
  using const_iterator=table_iterator<TypePolicy,GroupPtr,true>;

public:
  /* can't delete it because VS in pre-C++17 mode needs to see it for RVO */
  table_erase_return_type(const table_erase_return_type&);

  operator iterator()const noexcept
  {
    auto it=pos;
    it.increment();
    return iterator(const_iterator_cast_tag{},it);
  }

  template<
    bool dependent_value=false,
    typename std::enable_if<!Const||dependent_value>::type* =nullptr
  >
  operator const_iterator()const noexcept{return this->operator iterator();}

private:
  template<typename,typename,typename,typename> friend class table;

  table_erase_return_type(const_iterator pos_):pos{pos_}{}
  table_erase_return_type& operator=(const table_erase_return_type&)=delete;

  const_iterator pos;
};

/* foa::table interface departs in a number of ways from that of C++ unordered
 * associative containers because it's not for end-user consumption
 * (boost::unordered_(flat|node)_(map|set) wrappers complete it as
 * appropriate).
 *
 * The table supports two main modes of operation: flat and node-based. In the
 * flat case, buckets directly store elements. For node-based, buckets store
 * pointers to individually heap-allocated elements.
 *
 * For both flat and node-based:
 *
 *   - begin() is not O(1).
 *   - No bucket API.
 *   - Load factor is fixed and can't be set by the user.
 *
 * For flat only:
 *
 *   - value_type must be moveable.
 *   - Pointer stability is not kept under rehashing.
 *   - No extract API.
 *
 * try_emplace, erase and find support heterogeneous lookup by default,
 * that is, without checking for any ::is_transparent typedefs --the
 * checking is done by boost::unordered_(flat|node)_(map|set).
 */

template<typename,typename,typename,typename>
class concurrent_table;

template <typename TypePolicy,typename Hash,typename Pred,typename Allocator>
using table_core_impl=
  table_core<TypePolicy,group15<plain_integral>,table_arrays,
  plain_size_control,Hash,Pred,Allocator>;

#ifdef BOOST_MSVC
#pragma warning(push)
#pragma warning(disable:4714)
#endif

template<typename TypePolicy,typename Hash,typename Pred,typename Allocator>
class table:table_core_impl<TypePolicy,Hash,Pred,Allocator>
{
  using super=table_core_impl<TypePolicy,Hash,Pred,Allocator>;
  using type_policy=typename super::type_policy;
  using group_type=typename super::group_type;
  using super::N;
  using prober=typename super::prober;
  using arrays_type=typename super::arrays_type;
  using size_ctrl_type=typename super::size_ctrl_type;
  using locator=typename super::locator;
  using compatible_concurrent_table=
    concurrent_table<TypePolicy,Hash,Pred,Allocator>;
  using group_type_pointer=typename std::pointer_traits<
    typename std::allocator_traits<Allocator>::pointer
  >::template rebind<group_type>;
  friend compatible_concurrent_table;

public:
  using key_type=typename super::key_type;
  using init_type=typename super::init_type;
  using value_type=typename super::value_type;
  using element_type=typename super::element_type;

private:
  static constexpr bool has_mutable_iterator=
    !std::is_same<key_type,value_type>::value;
public:
  using hasher=typename super::hasher;
  using key_equal=typename super::key_equal;
  using allocator_type=typename super::allocator_type;
  using pointer=typename super::pointer;
  using const_pointer=typename super::const_pointer;
  using reference=typename super::reference;
  using const_reference=typename super::const_reference;
  using size_type=typename super::size_type;
  using difference_type=typename super::difference_type;
  using const_iterator=table_iterator<type_policy,group_type_pointer,true>;
  using iterator=typename std::conditional<
    has_mutable_iterator,
    table_iterator<type_policy,group_type_pointer,false>,
    const_iterator>::type;
  using erase_return_type=table_erase_return_type<iterator>;

#ifdef BOOST_UNORDERED_ENABLE_STATS
  using stats=typename super::stats;
#endif

  table(
    std::size_t n=default_bucket_count,const Hash& h_=Hash(),
    const Pred& pred_=Pred(),const Allocator& al_=Allocator()):
    super{n,h_,pred_,al_}
    {}

  table(const table& x)=default;
  table(table&& x)=default;
  table(const table& x,const Allocator& al_):super{x,al_}{}
  table(table&& x,const Allocator& al_):super{std::move(x),al_}{}
  table(compatible_concurrent_table&& x):
    table(std::move(x),x.exclusive_access()){}
  ~table()=default;

  table& operator=(const table& x)=default;
  table& operator=(table&& x)=default;

  using super::get_allocator;

  iterator begin()noexcept
  {
    iterator it{this->arrays.groups(),0,this->arrays.elements()};
    if(this->arrays.elements()&&
       !(this->arrays.groups()[0].match_occupied()&0x1))++it;
    return it;
  }

  const_iterator begin()const noexcept
                   {return const_cast<table*>(this)->begin();}
  iterator       end()noexcept{return {};}
  const_iterator end()const noexcept{return const_cast<table*>(this)->end();}
  const_iterator cbegin()const noexcept{return begin();}
  const_iterator cend()const noexcept{return end();}

  using super::empty;
  using super::size;
  using super::max_size;

  template<typename... Args>
  BOOST_FORCEINLINE std::pair<iterator,bool> emplace(Args&&... args)
  {
    alloc_cted_insert_type<type_policy,Allocator,Args...> x(
      this->al(),std::forward<Args>(args)...);
    return emplace_impl(type_policy::move(x.value()));
  }

  /* Optimization for value_type and init_type, to avoid constructing twice */
  template <typename T>
  BOOST_FORCEINLINE typename std::enable_if<
    detail::is_similar_to_any<T, value_type, init_type>::value,
    std::pair<iterator, bool> >::type
  emplace(T&& x)
  {
    return emplace_impl(std::forward<T>(x));
  }

  /* Optimizations for maps for (k,v) to avoid eagerly constructing value */
  template <typename K, typename V>
  BOOST_FORCEINLINE
    typename std::enable_if<is_emplace_kv_able<table, K>::value,
      std::pair<iterator, bool> >::type
    emplace(K&& k, V&& v)
  {
    alloc_cted_or_fwded_key_type<type_policy, Allocator, K&&> x(
      this->al(), std::forward<K>(k));
    return emplace_impl(
      try_emplace_args_t{}, x.move_or_fwd(), std::forward<V>(v));
  }

  template<typename Key,typename... Args>
  BOOST_FORCEINLINE std::pair<iterator,bool> try_emplace(
    Key&& x,Args&&... args)
  {
    return emplace_impl(
      try_emplace_args_t{},std::forward<Key>(x),std::forward<Args>(args)...);
  }

  BOOST_FORCEINLINE std::pair<iterator,bool>
  insert(const init_type& x){return emplace_impl(x);}

  BOOST_FORCEINLINE std::pair<iterator,bool>
  insert(init_type&& x){return emplace_impl(std::move(x));}

  /* template<typename=void> tilts call ambiguities in favor of init_type */

  template<typename=void>
  BOOST_FORCEINLINE std::pair<iterator,bool>
  insert(const value_type& x){return emplace_impl(x);}

  template<typename=void>
  BOOST_FORCEINLINE std::pair<iterator,bool>
  insert(value_type&& x){return emplace_impl(std::move(x));}

  template<typename T=element_type>
  BOOST_FORCEINLINE
  typename std::enable_if<
    !std::is_same<T,value_type>::value,
    std::pair<iterator,bool>
  >::type
  insert(element_type&& x){return emplace_impl(std::move(x));}

  template<
    bool dependent_value=false,
    typename std::enable_if<
      has_mutable_iterator||dependent_value>::type* =nullptr
  >
  erase_return_type erase(iterator pos)noexcept
  {return erase(const_iterator(pos));}

  BOOST_FORCEINLINE
  erase_return_type erase(const_iterator pos)noexcept
  {
    super::erase(pos.pc(),pos.p());
    return {pos};
  }

  template<typename Key>
  BOOST_FORCEINLINE
  auto erase(Key&& x) -> typename std::enable_if<
    !std::is_convertible<Key,iterator>::value&&
    !std::is_convertible<Key,const_iterator>::value, std::size_t>::type
  {
    auto it=find(x);
    if(it!=end()){
      erase(it);
      return 1;
    }
    else return 0;
  }

  void swap(table& x)
    noexcept(noexcept(std::declval<super&>().swap(std::declval<super&>())))
  {
    super::swap(x);
  }

  using super::clear;

  element_type extract(const_iterator pos)
  {
    BOOST_ASSERT(pos!=end());
    erase_on_exit e{*this,pos};
    (void)e;
    return std::move(*pos.p());
  }

  // TODO: should we accept different allocator too?
  template<typename Hash2,typename Pred2>
  void merge(table<TypePolicy,Hash2,Pred2,Allocator>& x)
  {
    x.for_all_elements([&,this](group_type* pg,unsigned int n,element_type* p){
      erase_on_exit e{x,{pg,n,p}};
      if(!emplace_impl(type_policy::move(*p)).second)e.rollback();
    });
  }

  template<typename Hash2,typename Pred2>
  void merge(table<TypePolicy,Hash2,Pred2,Allocator>&& x){merge(x);}

  using super::hash_function;
  using super::key_eq;

  template<typename Key>
  BOOST_FORCEINLINE iterator find(const Key& x)
  {
    return make_iterator(super::find(x));
  }

  template<typename Key>
  BOOST_FORCEINLINE const_iterator find(const Key& x)const
  {
    return const_cast<table*>(this)->find(x);
  }

  using super::capacity;
  using super::load_factor;
  using super::max_load_factor;
  using super::max_load;
  using super::rehash;
  using super::reserve;

#ifdef BOOST_UNORDERED_ENABLE_STATS
  using super::get_stats;
  using super::reset_stats;
#endif

  template<typename Predicate>
  friend std::size_t erase_if(table& x,Predicate& pr)
  {
    using value_reference=typename std::conditional<
      std::is_same<key_type,value_type>::value,
      const_reference,
      reference
    >::type;

    std::size_t s=x.size();
    x.for_all_elements(
      [&](group_type* pg,unsigned int n,element_type* p){
        if(pr(const_cast<value_reference>(type_policy::value_from(*p)))){
          x.super::erase(pg,n,p);
        }
      });
    return std::size_t(s-x.size());
  }

  friend bool operator==(const table& x,const table& y)
  {
    return static_cast<const super&>(x)==static_cast<const super&>(y);
  }

  friend bool operator!=(const table& x,const table& y){return !(x==y);}

private:
  template<typename ArraysType>
  table(compatible_concurrent_table&& x,arrays_holder<ArraysType,Allocator>&& ah):
    super{
      std::move(x.h()),std::move(x.pred()),std::move(x.al()),
      [&x]{return arrays_type{
        x.arrays.groups_size_index,x.arrays.groups_size_mask,
        to_pointer<group_type_pointer>(
          reinterpret_cast<group_type*>(x.arrays.groups())),
        x.arrays.elements_};},
      size_ctrl_type{x.size_ctrl.ml,x.size_ctrl.size}}
  {
    compatible_concurrent_table::arrays_type::delete_group_access(x.al(),x.arrays);
    x.arrays=ah.release();
    x.size_ctrl.ml=x.initial_max_load();
    x.size_ctrl.size=0;
    BOOST_UNORDERED_SWAP_STATS(this->cstats,x.cstats);
  }

  template<typename ExclusiveLockGuard>
  table(compatible_concurrent_table&& x,ExclusiveLockGuard):
    table(std::move(x),x.make_empty_arrays())
  {}

  struct erase_on_exit
  {
    erase_on_exit(table& x_,const_iterator it_):x(x_),it(it_){}
    ~erase_on_exit(){if(!rollback_)x.erase(it);}

    void rollback(){rollback_=true;}

    table&         x;
    const_iterator it;
    bool           rollback_=false;
  };

  static inline iterator make_iterator(const locator& l)noexcept
  {
    return {l.pg,l.n,l.p};
  }

  template<typename... Args>
  BOOST_FORCEINLINE std::pair<iterator,bool> emplace_impl(Args&&... args)
  {
    const auto &k=this->key_from(std::forward<Args>(args)...);
    auto        hash=this->hash_for(k);
    auto        pos0=this->position_for(hash);
    auto        loc=super::find(k,pos0,hash);

    if(loc){
      return {make_iterator(loc),false};
    }
    if(BOOST_LIKELY(this->size_ctrl.size<this->size_ctrl.ml)){
      return {
        make_iterator(
          this->unchecked_emplace_at(pos0,hash,std::forward<Args>(args)...)),
        true
      };
    }
    else{
      return {
        make_iterator(
          this->unchecked_emplace_with_rehash(
            hash,std::forward<Args>(args)...)),
        true
      };
    }
  }
};

#ifdef BOOST_MSVC
#pragma warning(pop)
#endif

}
}
}
}

#endif
//  Boost noncopyable.hpp header file  --------------------------------------//

//  (C) Copyright Beman Dawes 1999-2003. Distributed under the Boost
//  Software License, Version 1.0. (See accompanying file
//  LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

//  See http://www.boost.org/libs/utility for documentation.

#ifndef BOOST_CORE_NONCOPYABLE_HPP
#define BOOST_CORE_NONCOPYABLE_HPP

namespace boost {

//  Private copy constructor and copy assignment ensure classes derived from
//  class noncopyable cannot be copied.

//  Contributed by Dave Abrahams

namespace noncopyable_  // protection from unintended ADL
{
#ifndef BOOST_NONCOPYABLE_BASE_TOKEN_DEFINED
#define BOOST_NONCOPYABLE_BASE_TOKEN_DEFINED

// noncopyable derives from base_token to enable Type Traits to detect
// whether a type derives from noncopyable without needing the definition
// of noncopyable itself.
//
// The definition of base_token is macro-guarded so that Type Traits can
// define it locally without including this header, to avoid a dependency
// on Core.

  struct base_token {};

#endif // #ifndef BOOST_NONCOPYABLE_BASE_TOKEN_DEFINED

  class noncopyable: base_token
  {
  protected:
#ifndef BOOST_NO_CXX11_NON_PUBLIC_DEFAULTED_FUNCTIONS
      constexpr noncopyable() = default;
      ~noncopyable() = default;
#else
      noncopyable() {}
      ~noncopyable() {}
#endif
#ifndef BOOST_NO_CXX11_DELETED_FUNCTIONS
      noncopyable( const noncopyable& ) = delete;
      noncopyable& operator=( const noncopyable& ) = delete;
#else
  private:  // emphasize the following members are private
      noncopyable( const noncopyable& );
      noncopyable& operator=( const noncopyable& );
#endif
  };
}

typedef noncopyable_::noncopyable noncopyable;

} // namespace boost

#endif // BOOST_CORE_NONCOPYABLE_HPP
/* Copyright 2023 Joaquin M Lopez Munoz.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifndef BOOST_UNORDERED_DETAIL_ARCHIVE_CONSTRUCTED_HPP
#define BOOST_UNORDERED_DETAIL_ARCHIVE_CONSTRUCTED_HPP

namespace boost{
namespace unordered{
namespace detail{

/* constructs a stack-based object from a serialization archive */

template<typename T>
struct archive_constructed:private noncopyable
{
  template<class Archive>
  archive_constructed(const char* name,Archive& ar,unsigned int version)
  {
    core::load_construct_data_adl(ar,std::addressof(get()),version);
    BOOST_TRY{
      ar>>core::make_nvp(name,get());
    }
    BOOST_CATCH(...){
      get().~T();
      BOOST_RETHROW;
    }
    BOOST_CATCH_END
  }

  ~archive_constructed()
  {
    get().~T();
  }

#if defined(BOOST_GCC)&&(BOOST_GCC>=4*10000+6*100)
#define BOOST_UNORDERED_IGNORE_WSTRICT_ALIASING
#endif

#ifdef BOOST_UNORDERED_IGNORE_WSTRICT_ALIASING
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wstrict-aliasing"
#endif

  T& get(){return *space.address();}

#ifdef BOOST_UNORDERED_IGNORE_WSTRICT_ALIASING
#pragma GCC diagnostic pop
#undef BOOST_UNORDERED_IGNORE_WSTRICT_ALIASING
#endif

private:
  opt_storage<T> space;
};

}
}
}

#endif
/* Copyright 2023 Joaquin M Lopez Munoz.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifndef BOOST_UNORDERED_DETAIL_SERIALIZATION_VERSION_HPP
#define BOOST_UNORDERED_DETAIL_SERIALIZATION_VERSION_HPP

namespace boost{
namespace unordered{
namespace detail{

/* boost::serialization::load_construct_adl(ar,t,version) requires user code
 * to pass the serialization version for t, when this information is really
 * stored in the archive. serialization_version<T> circumvents this design
 * error by acting as a regular serializable type with the same serialization
 * version as T; loading/saving serialization_version<T> does nothing with
 * the archive data itself but captures the stored serialization version
 * at load() time.
 */

template<typename T>
struct serialization_version
{
  serialization_version():
    value(boost::serialization::version<serialization_version>::value){}

  serialization_version& operator=(unsigned int x){value=x;return *this;};

  operator unsigned int()const{return value;}

private:

  template<class Archive>
  void serialize(Archive& ar,unsigned int version)
  {
    core::split_member(ar,*this,version);
  }

  template<class Archive>
  void save(Archive&,unsigned int)const{}

  template<class Archive>
  void load(Archive&,unsigned int version)
  {
    this->value=version;
  }

  unsigned int value;
};

}
}

namespace serialization{

template<typename T>
struct version<boost::unordered::detail::serialization_version<T> >
{
  static const int value=version<T>::value;
};

}

}

#endif
/* Copyright 2023 Joaquin M Lopez Munoz.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifndef BOOST_UNORDERED_DETAIL_SERIALIZE_CONTAINER_HPP
#define BOOST_UNORDERED_DETAIL_SERIALIZE_CONTAINER_HPP

namespace boost{
namespace unordered{
namespace detail{

/* serialize_container(ar,x,v) serializes any of the unordered associative
 * containers in Boost.Unordered. Iterator serialization is also supported
 * through the following protocol:
 *  - At saving time, for each iterator it in [x.begin(),x.end()),
 *    serialization_track(ar,it) is ADL-called to instruct the archive to
 *    track the positions internally pointed to by the iterator via
 *    track_address().
 *  - At loading time, these addresses are mapped to those of the equivalent
 *    reconstructed positions using again serialization_track(ar,it).
 *  - Serializing an iterator reduces to serializing pointers to previously
 *    tracked addresses via serialize_address().
 */

template<typename Iterator>
std::pair<Iterator,bool> adapt_insert_return_type(Iterator it)
{
  return std::pair<Iterator,bool>(it,true);
}

template<typename Iterator>
std::pair<Iterator,bool> adapt_insert_return_type(std::pair<Iterator,bool> p)
{
  return p;
}

template<typename Set,bool IsSaving> struct load_or_save_unordered_set;

template<typename Set> struct load_or_save_unordered_set<Set,true>
{
  template<typename Archive>
  void operator()(Archive& ar,const Set& x,unsigned int)const
  {
    typedef typename Set::value_type     value_type;
    typedef typename Set::const_iterator const_iterator;

    const std::size_t                       s=x.size();
    const serialization_version<value_type> value_version;

    ar<<core::make_nvp("count",s);
    ar<<core::make_nvp("value_version",value_version);

    for(const_iterator first=x.begin(),last=x.end();first!=last;++first){
      core::save_construct_data_adl(ar,std::addressof(*first),value_version);
      ar<<core::make_nvp("item",*first);
      serialization_track(ar,first);
    }
  }
};

template<typename Set> struct load_or_save_unordered_set<Set,false>
{
  template<typename Archive>
  void operator()(Archive& ar,Set& x,unsigned int)const
  {
    typedef typename Set::value_type value_type;
    typedef typename Set::iterator   iterator;

    std::size_t                       s;
    serialization_version<value_type> value_version;

    ar>>core::make_nvp("count",s);
    ar>>core::make_nvp("value_version",value_version);

    x.clear();
    x.reserve(s);

    for(std::size_t n=0;n<s;++n){
      archive_constructed<value_type> value("item",ar,value_version);

      std::pair<iterator,bool> p=adapt_insert_return_type(
        x.insert(std::move(value.get())));
      if(!p.second)throw_exception(bad_archive_exception());
      ar.reset_object_address(
        std::addressof(*p.first),std::addressof(value.get()));
      serialization_track(ar,p.first);
    }
  }
};

template<typename Map,bool IsSaving> struct load_or_save_unordered_map;

template<typename Map> struct load_or_save_unordered_map<Map,true>
{
  template<typename Archive>
  void operator()(Archive& ar,const Map& x,unsigned int)const
  {
    typedef typename std::remove_const<
      typename Map::key_type>::type       key_type;
    typedef typename std::remove_const<
      typename Map::mapped_type>::type    mapped_type;
    typedef typename Map::const_iterator  const_iterator;

    const std::size_t                        s=x.size();
    const serialization_version<key_type>    key_version;
    const serialization_version<mapped_type> mapped_version;

    ar<<core::make_nvp("count",s);
    ar<<core::make_nvp("key_version",key_version);
    ar<<core::make_nvp("mapped_version",mapped_version);

    for(const_iterator first=x.begin(),last=x.end();first!=last;++first){
      /* To remain lib-independent from Boost.Serialization and not rely on
       * the user having included the serialization code for std::pair
       * (boost/serialization/utility.hpp), we serialize the key and the
       * mapped value separately.
       */

      core::save_construct_data_adl(
        ar,std::addressof(first->first),key_version);
      ar<<core::make_nvp("key",first->first);
      core::save_construct_data_adl(
        ar,std::addressof(first->second),mapped_version);
      ar<<core::make_nvp("mapped",first->second);
      serialization_track(ar,first);
    }
  }
};

template<typename Map> struct load_or_save_unordered_map<Map,false>
{
  template<typename Archive>
  void operator()(Archive& ar,Map& x,unsigned int)const
  {
    typedef typename std::remove_const<
      typename Map::key_type>::type       key_type;
    typedef typename std::remove_const<
      typename Map::mapped_type>::type    mapped_type;
    typedef typename Map::iterator        iterator;

    std::size_t                        s;
    serialization_version<key_type>    key_version;
    serialization_version<mapped_type> mapped_version;

    ar>>core::make_nvp("count",s);
    ar>>core::make_nvp("key_version",key_version);
    ar>>core::make_nvp("mapped_version",mapped_version);

    x.clear();
    x.reserve(s);

    for(std::size_t n=0;n<s;++n){
      archive_constructed<key_type>    key("key",ar,key_version);
      archive_constructed<mapped_type> mapped("mapped",ar,mapped_version);

      std::pair<iterator,bool> p=adapt_insert_return_type(
        x.emplace(std::move(key.get()),std::move(mapped.get())));
      if(!p.second)throw_exception(bad_archive_exception());
      ar.reset_object_address(
        std::addressof(p.first->first),std::addressof(key.get()));
      ar.reset_object_address(
        std::addressof(p.first->second),std::addressof(mapped.get()));
      serialization_track(ar,p.first);
    }
  }
};

template<typename Container,bool IsSet,bool IsSaving>
struct load_or_save_container;

template<typename Set,bool IsSaving>
struct load_or_save_container<Set,true,IsSaving>:
  load_or_save_unordered_set<Set,IsSaving>{};

template<typename Map,bool IsSaving>
struct load_or_save_container<Map,false,IsSaving>:
  load_or_save_unordered_map<Map,IsSaving>{};

template<typename Archive,typename Container>
void serialize_container(Archive& ar,Container& x,unsigned int version)
{
  load_or_save_container<
    Container,
    std::is_same<
      typename Container::key_type,typename Container::value_type>::value,
    Archive::is_saving::value>()(ar,x,version);
}

}
}
}

#endif
// Copyright (C) 2022 Christian Mazakas
// Copyright (C) 2024 Braden Ganetsky
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_UNORDERED_FLAT_SET_FWD_HPP_INCLUDED
#define BOOST_UNORDERED_FLAT_SET_FWD_HPP_INCLUDED

#pragma once

namespace boost {
  namespace unordered {
    template <class Key, class Hash = boost::hash<Key>,
      class KeyEqual = std::equal_to<Key>,
      class Allocator = std::allocator<Key> >
    class unordered_flat_set;

    template <class Key, class Hash, class KeyEqual, class Allocator>
    bool operator==(
      unordered_flat_set<Key, Hash, KeyEqual, Allocator> const& lhs,
      unordered_flat_set<Key, Hash, KeyEqual, Allocator> const& rhs);

    template <class Key, class Hash, class KeyEqual, class Allocator>
    bool operator!=(
      unordered_flat_set<Key, Hash, KeyEqual, Allocator> const& lhs,
      unordered_flat_set<Key, Hash, KeyEqual, Allocator> const& rhs);

    template <class Key, class Hash, class KeyEqual, class Allocator>
    void swap(unordered_flat_set<Key, Hash, KeyEqual, Allocator>& lhs,
      unordered_flat_set<Key, Hash, KeyEqual, Allocator>& rhs)
      noexcept(noexcept(lhs.swap(rhs)));

#ifndef BOOST_NO_CXX17_HDR_MEMORY_RESOURCE
    namespace pmr {
      template <class Key, class Hash = boost::hash<Key>,
        class KeyEqual = std::equal_to<Key> >
      using unordered_flat_set = boost::unordered::unordered_flat_set<Key, Hash,
        KeyEqual, std::pmr::polymorphic_allocator<Key> >;
    } // namespace pmr
#endif
  } // namespace unordered

  using boost::unordered::unordered_flat_set;
} // namespace boost

#endif
// Copyright 2017 Peter Dimov.
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

#ifndef BOOST_HASH_IS_UNORDERED_RANGE_HPP_INCLUDED
#define BOOST_HASH_IS_UNORDERED_RANGE_HPP_INCLUDED

#include <ranges>

namespace boost
{
namespace hash_detail
{

template<class T, class E = std::true_type> struct has_hasher_: std::false_type
{
};

template<class T> struct has_hasher_< T, std::integral_constant< bool,
        std::is_same<typename T::hasher, typename T::hasher>::value
    > >: std::true_type
{
};

} // namespace hash_detail

namespace container_hash
{

template<class T> struct is_unordered_range: std::integral_constant< bool, std::ranges::range<T> && hash_detail::has_hasher_<T>::value >
{
};

} // namespace container_hash
} // namespace boost

#endif // #ifndef BOOST_HASH_IS_UNORDERED_RANGE_HPP_INCLUDED
// Copyright 2022 Peter Dimov.
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

#ifndef BOOST_HASH_IS_DESCRIBED_CLASS_HPP_INCLUDED
#define BOOST_HASH_IS_DESCRIBED_CLASS_HPP_INCLUDED

namespace boost
{
namespace container_hash
{

#ifdef BOOST_DESCRIBE_CXX11

template<class T> struct is_described_class: std::integral_constant<bool,
    describe::has_describe_bases<T>::value &&
    describe::has_describe_members<T>::value &&
    !std::is_union<T>::value>
{
};

#else

template<class T> struct is_described_class: std::false_type
{
};

#endif

} // namespace container_hash
} // namespace boost

#endif // #ifndef BOOST_HASH_IS_DESCRIBED_CLASS_HPP_INCLUDED
// Copyright 2022 Peter Dimov
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

#ifndef BOOST_HASH_DETAIL_HASH_MIX_HPP
#define BOOST_HASH_DETAIL_HASH_MIX_HPP

namespace boost
{
namespace hash_detail
{

template<std::size_t Bits> struct hash_mix_impl;

// hash_mix for 64 bit size_t
//
// The general "xmxmx" form of state of the art 64 bit mixers originates
// from Murmur3 by Austin Appleby, which uses the following function as
// its "final mix":
//
//	k ^= k >> 33;
//	k *= 0xff51afd7ed558ccd;
//	k ^= k >> 33;
//	k *= 0xc4ceb9fe1a85ec53;
//	k ^= k >> 33;
//
// (https://github.com/aappleby/smhasher/blob/master/src/MurmurHash3.cpp)
//
// It has subsequently been improved multiple times by different authors
// by changing the constants. The most well known improvement is the
// so-called "variant 13" function by David Stafford:
//
//	k ^= k >> 30;
//	k *= 0xbf58476d1ce4e5b9;
//	k ^= k >> 27;
//	k *= 0x94d049bb133111eb;
//	k ^= k >> 31;
//
// (https://zimbry.blogspot.com/2011/09/better-bit-mixing-improving-on.html)
//
// This mixing function is used in the splitmix64 RNG:
// http://xorshift.di.unimi.it/splitmix64.c
//
// We use Jon Maiga's implementation from
// http://jonkagstrom.com/mx3/mx3_rev2.html
//
// 	x ^= x >> 32;
//	x *= 0xe9846af9b1a615d;
//	x ^= x >> 32;
//	x *= 0xe9846af9b1a615d;
//	x ^= x >> 28;
//
// An equally good alternative is Pelle Evensen's Moremur:
//
//	x ^= x >> 27;
//	x *= 0x3C79AC492BA7B653;
//	x ^= x >> 33;
//	x *= 0x1C69B3F74AC4AE35;
//	x ^= x >> 27;
//
// (https://mostlymangling.blogspot.com/2019/12/stronger-better-morer-moremur-better.html)

template<> struct hash_mix_impl<64>
{
    inline static std::uint64_t fn( std::uint64_t x )
    {
        std::uint64_t const m = 0xe9846af9b1a615d;

        x ^= x >> 32;
        x *= m;
        x ^= x >> 32;
        x *= m;
        x ^= x >> 28;

        return x;
    }
};

// hash_mix for 32 bit size_t
//
// We use the "best xmxmx" implementation from
// https://github.com/skeeto/hash-prospector/issues/19

template<> struct hash_mix_impl<32>
{
    inline static std::uint32_t fn( std::uint32_t x )
    {
        std::uint32_t const m1 = 0x21f0aaad;
        std::uint32_t const m2 = 0x735a2d97;

        x ^= x >> 16;
        x *= m1;
        x ^= x >> 15;
        x *= m2;
        x ^= x >> 15;

        return x;
    }
};

inline std::size_t hash_mix( std::size_t v )
{
    return hash_mix_impl<sizeof(std::size_t) * CHAR_BIT>::fn( v );
}

} // namespace hash_detail
} // namespace boost

#endif // #ifndef BOOST_HASH_DETAIL_HASH_MIX_HPP
// Copyright 2021-2023 Peter Dimov
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

#ifndef BOOST_HASH_DETAIL_HASH_INTEGRAL_HPP
#define BOOST_HASH_DETAIL_HASH_INTEGRAL_HPP

namespace boost
{
namespace hash_detail
{

// libstdc++ doesn't provide support for __int128 in the standard traits

template<class T> struct is_integral: public std::is_integral<T>
{
};

template<class T> struct is_unsigned: public std::is_unsigned<T>
{
};

template<class T> struct make_unsigned: public std::make_unsigned<T>
{
};

#ifdef __SIZEOF_INT128__

template<> struct is_integral<__int128_t>: public std::true_type
{
};

template<> struct is_integral<__uint128_t>: public std::true_type
{
};

template<> struct is_unsigned<__int128_t>: public std::false_type
{
};

template<> struct is_unsigned<__uint128_t>: public std::true_type
{
};

template<> struct make_unsigned<__int128_t>
{
    typedef __uint128_t type;
};

template<> struct make_unsigned<__uint128_t>
{
    typedef __uint128_t type;
};

#endif

template<class T,
    bool bigger_than_size_t = (sizeof(T) > sizeof(std::size_t)),
    bool is_unsigned = is_unsigned<T>::value,
    std::size_t size_t_bits = sizeof(std::size_t) * CHAR_BIT,
    std::size_t type_bits = sizeof(T) * CHAR_BIT>
struct hash_integral_impl;

template<class T, bool is_unsigned, std::size_t size_t_bits, std::size_t type_bits> struct hash_integral_impl<T, false, is_unsigned, size_t_bits, type_bits>
{
    static std::size_t fn( T v )
    {
        return static_cast<std::size_t>( v );
    }
};

template<class T, std::size_t size_t_bits, std::size_t type_bits> struct hash_integral_impl<T, true, false, size_t_bits, type_bits>
{
    static std::size_t fn( T v )
    {
        typedef typename make_unsigned<T>::type U;

        if( v >= 0 )
        {
            return hash_integral_impl<U>::fn( static_cast<U>( v ) );
        }
        else
        {
            return ~hash_integral_impl<U>::fn( static_cast<U>( ~static_cast<U>( v ) ) );
        }
    }
};

template<class T> struct hash_integral_impl<T, true, true, 32, 64>
{
    static std::size_t fn( T v )
    {
        std::size_t seed = 0;

        seed = static_cast<std::size_t>( v >> 32 ) + hash_detail::hash_mix( seed );
        seed = static_cast<std::size_t>( v  & 0xFFFFFFFF ) + hash_detail::hash_mix( seed );

        return seed;
    }
};

template<class T> struct hash_integral_impl<T, true, true, 32, 128>
{
    static std::size_t fn( T v )
    {
        std::size_t seed = 0;

        seed = static_cast<std::size_t>( v >> 96 ) + hash_detail::hash_mix( seed );
        seed = static_cast<std::size_t>( v >> 64 ) + hash_detail::hash_mix( seed );
        seed = static_cast<std::size_t>( v >> 32 ) + hash_detail::hash_mix( seed );
        seed = static_cast<std::size_t>( v ) + hash_detail::hash_mix( seed );

        return seed;
    }
};

template<class T> struct hash_integral_impl<T, true, true, 64, 128>
{
    static std::size_t fn( T v )
    {
        std::size_t seed = 0;

        seed = static_cast<std::size_t>( v >> 64 ) + hash_detail::hash_mix( seed );
        seed = static_cast<std::size_t>( v ) + hash_detail::hash_mix( seed );

        return seed;
    }
};

} // namespace hash_detail

template <typename T>
typename std::enable_if<hash_detail::is_integral<T>::value, std::size_t>::type
    hash_value( T v )
{
    return hash_detail::hash_integral_impl<T>::fn( v );
}

} // namespace boost

#endif // #ifndef BOOST_HASH_DETAIL_HASH_INTEGRAL_HPP
#ifndef BOOST_HASH_IS_TUPLE_LIKE_HPP_INCLUDED
#define BOOST_HASH_IS_TUPLE_LIKE_HPP_INCLUDED

// Copyright 2017, 2022 Peter Dimov.
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

namespace boost
{
namespace hash_detail
{

template<class T, class E = std::true_type> struct is_tuple_like_: std::false_type
{
};

template<class T> struct is_tuple_like_<T, std::integral_constant<bool, std::tuple_size<T>::value == std::tuple_size<T>::value> >: std::true_type
{
};

} // namespace hash_detail

namespace container_hash
{

template<class T> struct is_tuple_like: hash_detail::is_tuple_like_< typename std::remove_cv<T>::type >
{
};

} // namespace container_hash
} // namespace boost

#endif // #ifndef BOOST_HASH_IS_TUPLE_LIKE_HPP_INCLUDED
// Copyright 2005-2009 Daniel James.
// Copyright 2021 Peter Dimov.
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

#ifndef BOOST_HASH_DETAIL_HASH_TUPLE_LIKE_HPP
#define BOOST_HASH_DETAIL_HASH_TUPLE_LIKE_HPP

namespace boost
{
namespace hash_detail
{

template <std::size_t I, typename T>
inline
typename std::enable_if<(I == std::tuple_size<T>::value), void>::type
    hash_combine_tuple_like( std::size_t&, T const& )
{
}

template <std::size_t I, typename T>
inline
typename std::enable_if<(I < std::tuple_size<T>::value), void>::type
    hash_combine_tuple_like( std::size_t& seed, T const& v )
{
    using std::get;
    boost::hash_combine( seed, get<I>( v ) );

    boost::hash_detail::hash_combine_tuple_like<I + 1>( seed, v );
}

template <typename T>
inline std::size_t hash_tuple_like( T const& v )
{
    std::size_t seed = 0;

    boost::hash_detail::hash_combine_tuple_like<0>( seed, v );

    return seed;
}

} // namespace hash_detail

template <class T>
inline
typename std::enable_if<
    container_hash::is_tuple_like<T>::value && !std::ranges::range<T>,
std::size_t>::type
    hash_value( T const& v )
{
    return boost::hash_detail::hash_tuple_like( v );
}

} // namespace boost

#endif // #ifndef BOOST_HASH_DETAIL_HASH_TUPLE_LIKE_HPP
// Copyright 2022, 2023 Peter Dimov
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

#ifndef BOOST_HASH_DETAIL_MULX_HPP
#define BOOST_HASH_DETAIL_MULX_HPP

#ifdef _MSC_VER
# include <intrin.h>
#endif

namespace boost
{
namespace hash_detail
{

#if defined(_MSC_VER) && defined(_M_X64) && !defined(__clang__)

__forceinline std::uint64_t mulx( std::uint64_t x, std::uint64_t y )
{
    std::uint64_t r2;
    std::uint64_t r = _umul128( x, y, &r2 );
    return r ^ r2;
}

#elif defined(_MSC_VER) && defined(_M_ARM64) && !defined(__clang__)

__forceinline std::uint64_t mulx( std::uint64_t x, std::uint64_t y )
{
    std::uint64_t r = x * y;
    std::uint64_t r2 = __umulh( x, y );
    return r ^ r2;
}

#elif defined(__SIZEOF_INT128__)

inline std::uint64_t mulx( std::uint64_t x, std::uint64_t y )
{
    __uint128_t r = static_cast<__uint128_t>( x ) * y;
    return static_cast<std::uint64_t>( r ) ^ static_cast<std::uint64_t>( r >> 64 );
}

#else

inline std::uint64_t mulx( std::uint64_t x, std::uint64_t y )
{
    std::uint64_t x1 = static_cast<std::uint32_t>( x );
    std::uint64_t x2 = x >> 32;

    std::uint64_t y1 = static_cast<std::uint32_t>( y );
    std::uint64_t y2 = y >> 32;

    std::uint64_t r3 = x2 * y2;

    std::uint64_t r2a = x1 * y2;

    r3 += r2a >> 32;

    std::uint64_t r2b = x2 * y1;

    r3 += r2b >> 32;

    std::uint64_t r1 = x1 * y1;

    std::uint64_t r2 = (r1 >> 32) + static_cast<std::uint32_t>( r2a ) + static_cast<std::uint32_t>( r2b );

    r1 = (r2 << 32) + static_cast<std::uint32_t>( r1 );
    r3 += r2 >> 32;

    return r1 ^ r3;
}

#endif

} // namespace hash_detail
} // namespace boost

#endif // #ifndef BOOST_HASH_DETAIL_MULX_HPP
// Copyright 2022 Peter Dimov
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

#ifndef BOOST_HASH_DETAIL_HASH_RANGE_HPP
#define BOOST_HASH_DETAIL_HASH_RANGE_HPP

namespace boost
{
namespace hash_detail
{

template<class T> struct is_char_type: public std::false_type {};

#if CHAR_BIT == 8

template<> struct is_char_type<char>: public std::true_type {};
template<> struct is_char_type<signed char>: public std::true_type {};
template<> struct is_char_type<unsigned char>: public std::true_type {};

#if defined(__cpp_char8_t) && __cpp_char8_t >= 201811L
template<> struct is_char_type<char8_t>: public std::true_type {};
#endif

#if defined(__cpp_lib_byte) && __cpp_lib_byte >= 201603L
template<> struct is_char_type<std::byte>: public std::true_type {};
#endif

#endif

// generic version

template<class It>
inline typename std::enable_if<
    !is_char_type<typename std::iterator_traits<It>::value_type>::value,
std::size_t >::type
    hash_range( std::size_t seed, It first, It last )
{
    for( ; first != last; ++first )
    {
        hash_combine<typename std::iterator_traits<It>::value_type>( seed, *first );
    }

    return seed;
}

// specialized char[] version, 32 bit

template<class It> inline std::uint32_t read32le( It p )
{
    // clang 5+, gcc 5+ figure out this pattern and use a single mov on x86
    // gcc on s390x and power BE even knows how to use load-reverse

    std::uint32_t w =
        static_cast<std::uint32_t>( static_cast<unsigned char>( p[0] ) ) |
        static_cast<std::uint32_t>( static_cast<unsigned char>( p[1] ) ) <<  8 |
        static_cast<std::uint32_t>( static_cast<unsigned char>( p[2] ) ) << 16 |
        static_cast<std::uint32_t>( static_cast<unsigned char>( p[3] ) ) << 24;

    return w;
}

#if defined(_MSC_VER) && !defined(__clang__)

template<class T> inline std::uint32_t read32le( T* p )
{
    std::uint32_t w;

    std::memcpy( &w, p, 4 );
    return w;
}

#endif

inline std::uint64_t mul32( std::uint32_t x, std::uint32_t y )
{
    return static_cast<std::uint64_t>( x ) * y;
}

template<class It>
inline typename std::enable_if<
    is_char_type<typename std::iterator_traits<It>::value_type>::value &&
    std::is_same<typename std::iterator_traits<It>::iterator_category, std::random_access_iterator_tag>::value &&
    std::numeric_limits<std::size_t>::digits <= 32,
std::size_t>::type
    hash_range( std::size_t seed, It first, It last )
{
    It p = first;
    std::size_t n = static_cast<std::size_t>( last - first );

    std::uint32_t const q = 0x9e3779b9U;
    std::uint32_t const k = 0xe35e67b1U; // q * q

    std::uint64_t h = mul32( static_cast<std::uint32_t>( seed ) + q, k );
    std::uint32_t w = static_cast<std::uint32_t>( h & 0xFFFFFFFF );

    h ^= n;

    while( n >= 4 )
    {
        std::uint32_t v1 = read32le( p );

        w += q;
        h ^= mul32( v1 + w, k );

        p += 4;
        n -= 4;
    }

    {
        std::uint32_t v1 = 0;

        if( n >= 1 )
        {
            std::size_t const x1 = ( n - 1 ) & 2; // 1: 0, 2: 0, 3: 2
            std::size_t const x2 = n >> 1;        // 1: 0, 2: 1, 3: 1

            v1 =
                static_cast<std::uint32_t>( static_cast<unsigned char>( p[ static_cast<std::ptrdiff_t>( x1 ) ] ) ) << x1 * 8 |
                static_cast<std::uint32_t>( static_cast<unsigned char>( p[ static_cast<std::ptrdiff_t>( x2 ) ] ) ) << x2 * 8 |
                static_cast<std::uint32_t>( static_cast<unsigned char>( p[ 0 ] ) );
        }

        w += q;
        h ^= mul32( v1 + w, k );
    }

    w += q;
    h ^= mul32( static_cast<std::uint32_t>( h & 0xFFFFFFFF ) + w, static_cast<std::uint32_t>( h >> 32 ) + w + k );

    return static_cast<std::uint32_t>( h & 0xFFFFFFFF ) ^ static_cast<std::uint32_t>( h >> 32 );
}

template<class It>
inline typename std::enable_if<
    is_char_type<typename std::iterator_traits<It>::value_type>::value &&
    !std::is_same<typename std::iterator_traits<It>::iterator_category, std::random_access_iterator_tag>::value &&
    std::numeric_limits<std::size_t>::digits <= 32,
std::size_t>::type
    hash_range( std::size_t seed, It first, It last )
{
    std::size_t n = 0;

    std::uint32_t const q = 0x9e3779b9U;
    std::uint32_t const k = 0xe35e67b1U; // q * q

    std::uint64_t h = mul32( static_cast<std::uint32_t>( seed ) + q, k );
    std::uint32_t w = static_cast<std::uint32_t>( h & 0xFFFFFFFF );

    std::uint32_t v1 = 0;

    for( ;; )
    {
        v1 = 0;

        if( first == last )
        {
            break;
        }

        v1 |= static_cast<std::uint32_t>( static_cast<unsigned char>( *first ) );
        ++first;
        ++n;

        if( first == last )
        {
            break;
        }

        v1 |= static_cast<std::uint32_t>( static_cast<unsigned char>( *first ) ) << 8;
        ++first;
        ++n;

        if( first == last )
        {
            break;
        }

        v1 |= static_cast<std::uint32_t>( static_cast<unsigned char>( *first ) ) << 16;
        ++first;
        ++n;

        if( first == last )
        {
            break;
        }

        v1 |= static_cast<std::uint32_t>( static_cast<unsigned char>( *first ) ) << 24;
        ++first;
        ++n;

        w += q;
        h ^= mul32( v1 + w, k );
    }

    h ^= n;

    w += q;
    h ^= mul32( v1 + w, k );

    w += q;
    h ^= mul32( static_cast<std::uint32_t>( h & 0xFFFFFFFF ) + w, static_cast<std::uint32_t>( h >> 32 ) + w + k );

    return static_cast<std::uint32_t>( h & 0xFFFFFFFF ) ^ static_cast<std::uint32_t>( h >> 32 );
}

// specialized char[] version, 64 bit

template<class It> inline std::uint64_t read64le( It p )
{
    std::uint64_t w =
        static_cast<std::uint64_t>( static_cast<unsigned char>( p[0] ) ) |
        static_cast<std::uint64_t>( static_cast<unsigned char>( p[1] ) ) <<  8 |
        static_cast<std::uint64_t>( static_cast<unsigned char>( p[2] ) ) << 16 |
        static_cast<std::uint64_t>( static_cast<unsigned char>( p[3] ) ) << 24 |
        static_cast<std::uint64_t>( static_cast<unsigned char>( p[4] ) ) << 32 |
        static_cast<std::uint64_t>( static_cast<unsigned char>( p[5] ) ) << 40 |
        static_cast<std::uint64_t>( static_cast<unsigned char>( p[6] ) ) << 48 |
        static_cast<std::uint64_t>( static_cast<unsigned char>( p[7] ) ) << 56;

    return w;
}

#if defined(_MSC_VER) && !defined(__clang__)

template<class T> inline std::uint64_t read64le( T* p )
{
    std::uint64_t w;

    std::memcpy( &w, p, 8 );
    return w;
}

#endif

template<class It>
inline typename std::enable_if<
    is_char_type<typename std::iterator_traits<It>::value_type>::value &&
    std::is_same<typename std::iterator_traits<It>::iterator_category, std::random_access_iterator_tag>::value &&
    (std::numeric_limits<std::size_t>::digits > 32),
std::size_t>::type
    hash_range( std::size_t seed, It first, It last )
{
    It p = first;
    std::size_t n = static_cast<std::size_t>( last - first );

    std::uint64_t const q = 0x9e3779b97f4a7c15;
    std::uint64_t const k = 0xdf442d22ce4859b9; // q * q

    std::uint64_t w = mulx( seed + q, k );
    std::uint64_t h = w ^ n;

    while( n >= 8 )
    {
        std::uint64_t v1 = read64le( p );

        w += q;
        h ^= mulx( v1 + w, k );

        p += 8;
        n -= 8;
    }

    {
        std::uint64_t v1 = 0;

        if( n >= 4 )
        {
            v1 = static_cast<std::uint64_t>( read32le( p + static_cast<std::ptrdiff_t>( n - 4 ) ) ) << ( n - 4 ) * 8 | read32le( p );
        }
        else if( n >= 1 )
        {
            std::size_t const x1 = ( n - 1 ) & 2; // 1: 0, 2: 0, 3: 2
            std::size_t const x2 = n >> 1;        // 1: 0, 2: 1, 3: 1

            v1 =
                static_cast<std::uint64_t>( static_cast<unsigned char>( p[ static_cast<std::ptrdiff_t>( x1 ) ] ) ) << x1 * 8 |
                static_cast<std::uint64_t>( static_cast<unsigned char>( p[ static_cast<std::ptrdiff_t>( x2 ) ] ) ) << x2 * 8 |
                static_cast<std::uint64_t>( static_cast<unsigned char>( p[ 0 ] ) );
        }

        w += q;
        h ^= mulx( v1 + w, k );
    }

    return mulx( h + w, k );
}

template<class It>
inline typename std::enable_if<
    is_char_type<typename std::iterator_traits<It>::value_type>::value &&
    !std::is_same<typename std::iterator_traits<It>::iterator_category, std::random_access_iterator_tag>::value &&
    (std::numeric_limits<std::size_t>::digits > 32),
std::size_t>::type
    hash_range( std::size_t seed, It first, It last )
{
    std::size_t n = 0;

    std::uint64_t const q = 0x9e3779b97f4a7c15;
    std::uint64_t const k = 0xdf442d22ce4859b9; // q * q

    std::uint64_t w = mulx( seed + q, k );
    std::uint64_t h = w;

    std::uint64_t v1 = 0;

    for( ;; )
    {
        v1 = 0;

        if( first == last )
        {
            break;
        }

        v1 |= static_cast<std::uint64_t>( static_cast<unsigned char>( *first ) );
        ++first;
        ++n;

        if( first == last )
        {
            break;
        }

        v1 |= static_cast<std::uint64_t>( static_cast<unsigned char>( *first ) ) << 8;
        ++first;
        ++n;

        if( first == last )
        {
            break;
        }

        v1 |= static_cast<std::uint64_t>( static_cast<unsigned char>( *first ) ) << 16;
        ++first;
        ++n;

        if( first == last )
        {
            break;
        }

        v1 |= static_cast<std::uint64_t>( static_cast<unsigned char>( *first ) ) << 24;
        ++first;
        ++n;

        if( first == last )
        {
            break;
        }

        v1 |= static_cast<std::uint64_t>( static_cast<unsigned char>( *first ) ) << 32;
        ++first;
        ++n;

        if( first == last )
        {
            break;
        }

        v1 |= static_cast<std::uint64_t>( static_cast<unsigned char>( *first ) ) << 40;
        ++first;
        ++n;

        if( first == last )
        {
            break;
        }

        v1 |= static_cast<std::uint64_t>( static_cast<unsigned char>( *first ) ) << 48;
        ++first;
        ++n;

        if( first == last )
        {
            break;
        }

        v1 |= static_cast<std::uint64_t>( static_cast<unsigned char>( *first ) ) << 56;
        ++first;
        ++n;

        w += q;
        h ^= mulx( v1 + w, k );
    }

    h ^= n;

    w += q;
    h ^= mulx( v1 + w, k );

    return mulx( h + w, k );
}

} // namespace hash_detail
} // namespace boost

#endif // #ifndef BOOST_HASH_DETAIL_HASH_RANGE_HPP
// Copyright 2005-2014 Daniel James.
// Copyright 2021, 2022 Peter Dimov.
// Distributed under the Boost Software License, Version 1.0.
// https://www.boost.org/LICENSE_1_0.txt

// Based on Peter Dimov's proposal
// http://www.open-std.org/JTC1/SC22/WG21/docs/papers/2005/n1756.pdf
// issue 6.18.

#ifndef BOOST_FUNCTIONAL_HASH_HASH_HPP
#define BOOST_FUNCTIONAL_HASH_HASH_HPP

#ifdef BOOST_DESCRIBE_CXX14
# include <boost/mp11/algorithm.hpp>
#endif

#ifndef BOOST_NO_CXX11_SMART_PTR
# include <memory>
#endif

#ifndef BOOST_NO_CXX17_HDR_STRING_VIEW
# include <string_view>
#endif

namespace boost
{

    //
    // boost::hash_value
    //

    // integral types
    //   in detail/hash_integral.hpp

    // enumeration types

    template <typename T>
    typename std::enable_if<std::is_enum<T>::value, std::size_t>::type
        hash_value( T v )
    {
        // This should in principle return the equivalent of
        //
        // boost::hash_value( to_underlying(v) );
        //
        // However, the C++03 implementation of underlying_type,
        //
        // conditional<is_signed<T>, make_signed<T>, make_unsigned<T>>::type::type
        //
        // generates a legitimate -Wconversion warning in is_signed,
        // because -1 is not a valid enum value when all the enumerators
        // are nonnegative.
        //
        // So the legacy implementation will have to do for now.

        return static_cast<std::size_t>( v );
    }

    // floating point types

    namespace hash_detail
    {
        template<class T,
            std::size_t Bits = sizeof(T) * CHAR_BIT,
            int Digits = std::numeric_limits<T>::digits>
        struct hash_float_impl;

        // float
        template<class T, int Digits> struct hash_float_impl<T, 32, Digits>
        {
            static std::size_t fn( T v )
            {
                std::uint32_t w;
                std::memcpy( &w, &v, sizeof( v ) );

                return w;
            }
        };

        // double
        template<class T, int Digits> struct hash_float_impl<T, 64, Digits>
        {
            static std::size_t fn( T v )
            {
                std::uint64_t w;
                std::memcpy( &w, &v, sizeof( v ) );

                return hash_value( w );
            }
        };

        // 80 bit long double in 12 bytes
        template<class T> struct hash_float_impl<T, 96, 64>
        {
            static std::size_t fn( T v )
            {
                std::uint64_t w[ 2 ] = {};
                std::memcpy( &w, &v, 80 / CHAR_BIT );

                std::size_t seed = 0;

                seed = hash_value( w[0] ) + hash_detail::hash_mix( seed );
                seed = hash_value( w[1] ) + hash_detail::hash_mix( seed );

                return seed;
            }
        };

        // 80 bit long double in 16 bytes
        template<class T> struct hash_float_impl<T, 128, 64>
        {
            static std::size_t fn( T v )
            {
                std::uint64_t w[ 2 ] = {};
                std::memcpy( &w, &v, 80 / CHAR_BIT );

                std::size_t seed = 0;

                seed = hash_value( w[0] ) + hash_detail::hash_mix( seed );
                seed = hash_value( w[1] ) + hash_detail::hash_mix( seed );

                return seed;
            }
        };

        // 128 bit long double
        template<class T, int Digits> struct hash_float_impl<T, 128, Digits>
        {
            static std::size_t fn( T v )
            {
                std::uint64_t w[ 2 ];
                std::memcpy( &w, &v, sizeof( v ) );

                std::size_t seed = 0;

#if defined(__FLOAT_WORD_ORDER__) && defined(__ORDER_BIG_ENDIAN__) && __FLOAT_WORD_ORDER__ == __ORDER_BIG_ENDIAN__

                seed = hash_value( w[1] ) + hash_detail::hash_mix( seed );
                seed = hash_value( w[0] ) + hash_detail::hash_mix( seed );

#else

                seed = hash_value( w[0] ) + hash_detail::hash_mix( seed );
                seed = hash_value( w[1] ) + hash_detail::hash_mix( seed );

#endif
                return seed;
            }
        };

    } // namespace hash_detail

    template <typename T>
    typename std::enable_if<std::is_floating_point<T>::value, std::size_t>::type
        hash_value( T v )
    {
        return boost::hash_detail::hash_float_impl<T>::fn( v + 0 );
    }

    // pointer types

    // `x + (x >> 3)` adjustment by Alberto Barbati and Dave Harris.
    template <class T> std::size_t hash_value( T* const& v )
    {
        std::uintptr_t x = reinterpret_cast<std::uintptr_t>( v );
        return boost::hash_value( x + (x >> 3) );
    }

    // array types

    template<class T, std::size_t N>
    inline std::size_t hash_value( T const (&x)[ N ] )
    {
        return boost::hash_range( x, x + N );
    }

    template<class T, std::size_t N>
    inline std::size_t hash_value( T (&x)[ N ] )
    {
        return boost::hash_range( x, x + N );
    }

    // complex

    template <class T>
    std::size_t hash_value( std::complex<T> const& v )
    {
        std::size_t re = boost::hash<T>()( v.real() );
        std::size_t im = boost::hash<T>()( v.imag() );

        return re + hash_detail::hash_mix( im );
    }

    // pair

    template <class A, class B>
    std::size_t hash_value( std::pair<A, B> const& v )
    {
        std::size_t seed = 0;

        boost::hash_combine( seed, v.first );
        boost::hash_combine( seed, v.second );

        return seed;
    }

    // ranges (list, set, deque...)

    template <typename T>
    typename std::enable_if<std::ranges::range<T> && !std::ranges::contiguous_range<T> && !container_hash::is_unordered_range<T>::value, std::size_t>::type
        hash_value( T const& v )
    {
        return boost::hash_range( v.begin(), v.end() );
    }

    // contiguous ranges (string, vector, array)

    template <typename T>
    typename std::enable_if<std::ranges::contiguous_range<T>, std::size_t>::type
        hash_value( T const& v )
    {
        return boost::hash_range( v.data(), v.data() + v.size() );
    }

    // unordered ranges (unordered_set, unordered_map)

    template <typename T>
    typename std::enable_if<container_hash::is_unordered_range<T>::value, std::size_t>::type
        hash_value( T const& v )
    {
        return boost::hash_unordered_range( v.begin(), v.end() );
    }

#if (  ( defined(_MSVC_STL_VERSION) && _MSVC_STL_VERSION < 142 ) ||  ( !defined(_MSVC_STL_VERSION) && defined(_CPPLIB_VER) && _CPPLIB_VER >= 520 ) )

    // resolve ambiguity with unconstrained stdext::hash_value in <xhash> :-/

    template<template<class...> class L, class... T>
    typename std::enable_if<std::ranges::range<L<T...>> && !std::ranges::contiguous_range<L<T...>> && !container_hash::is_unordered_range<L<T...>>::value, std::size_t>::type
        hash_value( L<T...> const& v )
    {
        return boost::hash_range( v.begin(), v.end() );
    }

    // contiguous ranges (string, vector, array)

    template<template<class...> class L, class... T>
    typename std::enable_if<std::ranges::contiguous_range<L<T...>>, std::size_t>::type
        hash_value( L<T...> const& v )
    {
        return boost::hash_range( v.data(), v.data() + v.size() );
    }

    template<template<class, std::size_t> class L, class T, std::size_t N>
    typename std::enable_if<std::ranges::contiguous_range<L<T, N>>, std::size_t>::type
        hash_value( L<T, N> const& v )
    {
        return boost::hash_range( v.data(), v.data() + v.size() );
    }

    // unordered ranges (unordered_set, unordered_map)

    template<template<class...> class L, class... T>
    typename std::enable_if<container_hash::is_unordered_range<L<T...>>::value, std::size_t>::type
        hash_value( L<T...> const& v )
    {
        return boost::hash_unordered_range( v.begin(), v.end() );
    }

#endif

    // described classes

#ifdef BOOST_DESCRIBE_CXX14

#if defined(_MSC_VER) && _MSC_VER == 1900
# pragma warning(push)
# pragma warning(disable: 4100) // unreferenced formal parameter
#endif

    template <typename T>
    typename std::enable_if<container_hash::is_described_class<T>::value, std::size_t>::type
        hash_value( T const& v )
    {
        static_assert( !std::is_union<T>::value, "described unions are not supported" );

        std::size_t r = 0;

        using Bd = describe::describe_bases<T, describe::mod_any_access>;

        mp11::mp_for_each<Bd>([&](auto D){

            using B = typename decltype(D)::type;
            boost::hash_combine( r, (B const&)v );

        });

        using Md = describe::describe_members<T, describe::mod_any_access>;

        mp11::mp_for_each<Md>([&](auto D){

            boost::hash_combine( r, v.*D.pointer );

        });

        return r;
    }

#if defined(_MSC_VER) && _MSC_VER == 1900
# pragma warning(pop)
#endif

#endif

    // std::unique_ptr, std::shared_ptr

#ifndef BOOST_NO_CXX11_SMART_PTR

    template <typename T>
    std::size_t hash_value( std::shared_ptr<T> const& x )
    {
        return boost::hash_value( x.get() );
    }

    template <typename T, typename Deleter>
    std::size_t hash_value( std::unique_ptr<T, Deleter> const& x )
    {
        return boost::hash_value( x.get() );
    }

#endif

    // std::type_index

#ifndef BOOST_NO_CXX11_HDR_TYPEINDEX

    inline std::size_t hash_value( std::type_index const& v )
    {
        return v.hash_code();
    }

#endif

    // std::error_code, std::error_condition

#ifndef BOOST_NO_CXX11_HDR_SYSTEM_ERROR

    inline std::size_t hash_value( std::error_code const& v )
    {
        std::size_t seed = 0;

        boost::hash_combine( seed, v.value() );
        boost::hash_combine( seed, &v.category() );

        return seed;
    }

    inline std::size_t hash_value( std::error_condition const& v )
    {
        std::size_t seed = 0;

        boost::hash_combine( seed, v.value() );
        boost::hash_combine( seed, &v.category() );

        return seed;
    }

#endif

    // std::nullptr_t

#ifndef BOOST_NO_CXX11_NULLPTR

    template <typename T>
    typename std::enable_if<std::is_same<T, std::nullptr_t>::value, std::size_t>::type
        hash_value( T const& /*v*/ )
    {
        return boost::hash_value( static_cast<void*>( nullptr ) );
    }

#endif

    // std::optional

#ifndef BOOST_NO_CXX17_HDR_OPTIONAL

    template <typename T>
    std::size_t hash_value( std::optional<T> const& v )
    {
        if( !v )
        {
            // Arbitrary value for empty optional.
            return 0x12345678;
        }
        else
        {
            return boost::hash<T>()(*v);
        }
    }

#endif

    // std::variant

#ifndef BOOST_NO_CXX17_HDR_VARIANT

    inline std::size_t hash_value( std::monostate )
    {
        return 0x87654321;
    }

    template <typename... Types>
    std::size_t hash_value( std::variant<Types...> const& v )
    {
        std::size_t seed = 0;

        hash_combine( seed, v.index() );
        std::visit( [&seed](auto&& x) { hash_combine(seed, x); }, v );

        return seed;
    }

#endif

    //
    // boost::hash_combine
    //

    template <class T>
    inline void hash_combine( std::size_t& seed, T const& v )
    {
        seed = boost::hash_detail::hash_mix( seed + 0x9e3779b9 + boost::hash<T>()( v ) );
    }

    //
    // boost::hash_range
    //

    template <class It>
    inline void hash_range( std::size_t& seed, It first, It last )
    {
        seed = hash_detail::hash_range( seed, first, last );
    }

    template <class It>
    inline std::size_t hash_range( It first, It last )
    {
        std::size_t seed = 0;

        hash_range( seed, first, last );

        return seed;
    }

    //
    // boost::hash_unordered_range
    //

    template <class It>
    inline void hash_unordered_range( std::size_t& seed, It first, It last )
    {
        std::size_t r = 0;
        std::size_t const s2( seed );

        for( ; first != last; ++first )
        {
            std::size_t s3( s2 );

            hash_combine<typename std::iterator_traits<It>::value_type>( s3, *first );

            r += s3;
        }

        seed += r;
    }

    template <class It>
    inline std::size_t hash_unordered_range( It first, It last )
    {
        std::size_t seed = 0;

        hash_unordered_range( seed, first, last );

        return seed;
    }

    //
    // boost::hash
    //

    template <class T> struct hash
    {
        typedef T argument_type;
        typedef std::size_t result_type;

        std::size_t operator()( T const& val ) const
        {
            return hash_value( val );
        }
    };

#if (  ( defined(_MSVC_STL_VERSION) && _MSVC_STL_VERSION < 142 ) ||  ( !defined(_MSVC_STL_VERSION) && defined(_CPPLIB_VER) && _CPPLIB_VER >= 520 ) )

    // Dinkumware has stdext::hash_value for basic_string in <xhash> :-/

    template<class E, class T, class A> struct hash< std::basic_string<E, T, A> >
    {
        typedef std::basic_string<E, T, A> argument_type;
        typedef std::size_t result_type;

        std::size_t operator()( std::basic_string<E, T, A> const& val ) const
        {
            return boost::hash_value( val );
        }
    };

#endif

    // boost::unordered::hash_is_avalanching

    namespace unordered
    {
        template<class T> struct hash_is_avalanching;
        template<class Ch> struct hash_is_avalanching< boost::hash< std::basic_string<Ch> > >: std::is_integral<Ch> {};

#ifndef BOOST_NO_CXX17_HDR_STRING_VIEW

        template<class Ch> struct hash_is_avalanching< boost::hash< std::basic_string_view<Ch> > >: std::is_integral<Ch> {};

#endif
    } // namespace unordered

} // namespace boost

#endif // #ifndef BOOST_FUNCTIONAL_HASH_HASH_HPP
// Copyright (C) 2022-2023 Christian Mazakas
// Copyright (C) 2024 Joaquin M Lopez Munoz
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_UNORDERED_UNORDERED_FLAT_SET_HPP_INCLUDED
#define BOOST_UNORDERED_UNORDERED_FLAT_SET_HPP_INCLUDED

#pragma once

namespace boost {
  namespace unordered {

#ifdef BOOST_MSVC
#pragma warning(push)
#pragma warning(disable : 4714)
#endif

    template <class Key, class Hash, class KeyEqual, class Allocator>
    class unordered_flat_set
    {
      template <class Key2, class Hash2, class KeyEqual2, class Allocator2>
      friend class concurrent_flat_set;

      using set_types = detail::foa::flat_set_types<Key>;

      using table_type = detail::foa::table<set_types, Hash, KeyEqual,
        typename std::allocator_traits<Allocator>::template rebind_alloc<
          typename set_types::value_type>>;

      table_type table_;

      template <class K, class H, class KE, class A>
      bool friend operator==(unordered_flat_set<K, H, KE, A> const& lhs,
        unordered_flat_set<K, H, KE, A> const& rhs);

      template <class K, class H, class KE, class A, class Pred>
      typename unordered_flat_set<K, H, KE, A>::size_type friend erase_if(
        unordered_flat_set<K, H, KE, A>& set, Pred pred);

    public:
      using key_type = Key;
      using value_type = typename set_types::value_type;
      using init_type = typename set_types::init_type;
      using size_type = std::size_t;
      using difference_type = std::ptrdiff_t;
      using hasher = Hash;
      using key_equal = KeyEqual;
      using allocator_type = Allocator;
      using reference = value_type&;
      using const_reference = value_type const&;
      using pointer = typename std::allocator_traits<allocator_type>::pointer;
      using const_pointer =
        typename std::allocator_traits<allocator_type>::const_pointer;
      using iterator = typename table_type::iterator;
      using const_iterator = typename table_type::const_iterator;

#ifdef BOOST_UNORDERED_ENABLE_STATS
      using stats = typename table_type::stats;
#endif

      unordered_flat_set() : unordered_flat_set(0) {}

      explicit unordered_flat_set(size_type n, hasher const& h = hasher(),
        key_equal const& pred = key_equal(),
        allocator_type const& a = allocator_type())
          : table_(n, h, pred, a)
      {
      }

      unordered_flat_set(size_type n, allocator_type const& a)
          : unordered_flat_set(n, hasher(), key_equal(), a)
      {
      }

      unordered_flat_set(size_type n, hasher const& h, allocator_type const& a)
          : unordered_flat_set(n, h, key_equal(), a)
      {
      }

      template <class InputIterator>
      unordered_flat_set(
        InputIterator f, InputIterator l, allocator_type const& a)
          : unordered_flat_set(f, l, size_type(0), hasher(), key_equal(), a)
      {
      }

      explicit unordered_flat_set(allocator_type const& a)
          : unordered_flat_set(0, a)
      {
      }

      template <class Iterator>
      unordered_flat_set(Iterator first, Iterator last, size_type n = 0,
        hasher const& h = hasher(), key_equal const& pred = key_equal(),
        allocator_type const& a = allocator_type())
          : unordered_flat_set(n, h, pred, a)
      {
        this->insert(first, last);
      }

      template <class InputIt>
      unordered_flat_set(
        InputIt first, InputIt last, size_type n, allocator_type const& a)
          : unordered_flat_set(first, last, n, hasher(), key_equal(), a)
      {
      }

      template <class Iterator>
      unordered_flat_set(Iterator first, Iterator last, size_type n,
        hasher const& h, allocator_type const& a)
          : unordered_flat_set(first, last, n, h, key_equal(), a)
      {
      }

      unordered_flat_set(unordered_flat_set const& other) : table_(other.table_)
      {
      }

      unordered_flat_set(
        unordered_flat_set const& other, allocator_type const& a)
          : table_(other.table_, a)
      {
      }

      unordered_flat_set(unordered_flat_set&& other)
        noexcept(std::is_nothrow_move_constructible<table_type>::value)
          : table_(std::move(other.table_))
      {
      }

      unordered_flat_set(unordered_flat_set&& other, allocator_type const& al)
          : table_(std::move(other.table_), al)
      {
      }

      unordered_flat_set(std::initializer_list<value_type> ilist,
        size_type n = 0, hasher const& h = hasher(),
        key_equal const& pred = key_equal(),
        allocator_type const& a = allocator_type())
          : unordered_flat_set(ilist.begin(), ilist.end(), n, h, pred, a)
      {
      }

      unordered_flat_set(
        std::initializer_list<value_type> il, allocator_type const& a)
          : unordered_flat_set(il, size_type(0), hasher(), key_equal(), a)
      {
      }

      unordered_flat_set(std::initializer_list<value_type> init, size_type n,
        allocator_type const& a)
          : unordered_flat_set(init, n, hasher(), key_equal(), a)
      {
      }

      unordered_flat_set(std::initializer_list<value_type> init, size_type n,
        hasher const& h, allocator_type const& a)
          : unordered_flat_set(init, n, h, key_equal(), a)
      {
      }

      template <bool avoid_explicit_instantiation = true>
      unordered_flat_set(
        concurrent_flat_set<Key, Hash, KeyEqual, Allocator>&& other)
          : table_(std::move(other.table_))
      {
      }

      ~unordered_flat_set() = default;

      unordered_flat_set& operator=(unordered_flat_set const& other)
      {
        table_ = other.table_;
        return *this;
      }

      unordered_flat_set& operator=(unordered_flat_set&& other) noexcept(
        noexcept(std::declval<table_type&>() = std::declval<table_type&&>()))
      {
        table_ = std::move(other.table_);
        return *this;
      }

      unordered_flat_set& operator=(std::initializer_list<value_type> il)
      {
        this->clear();
        this->insert(il.begin(), il.end());
        return *this;
      }

      allocator_type get_allocator() const noexcept
      {
        return table_.get_allocator();
      }

      /// Iterators
      ///

      iterator begin() noexcept { return table_.begin(); }
      const_iterator begin() const noexcept { return table_.begin(); }
      const_iterator cbegin() const noexcept { return table_.cbegin(); }

      iterator end() noexcept { return table_.end(); }
      const_iterator end() const noexcept { return table_.end(); }
      const_iterator cend() const noexcept { return table_.cend(); }

      /// Capacity
      ///

      [[nodiscard]] bool empty() const noexcept
      {
        return table_.empty();
      }

      size_type size() const noexcept { return table_.size(); }

      size_type max_size() const noexcept { return table_.max_size(); }

      /// Modifiers
      ///

      void clear() noexcept { table_.clear(); }

      BOOST_FORCEINLINE std::pair<iterator, bool> insert(
        value_type const& value)
      {
        return table_.insert(value);
      }

      BOOST_FORCEINLINE std::pair<iterator, bool> insert(value_type&& value)
      {
        return table_.insert(std::move(value));
      }

      template <class K>
      BOOST_FORCEINLINE typename std::enable_if<
        detail::transparent_non_iterable<K, unordered_flat_set>::value,
        std::pair<iterator, bool> >::type
      insert(K&& k)
      {
        return table_.try_emplace(std::forward<K>(k));
      }

      BOOST_FORCEINLINE iterator insert(const_iterator, value_type const& value)
      {
        return table_.insert(value).first;
      }

      BOOST_FORCEINLINE iterator insert(const_iterator, value_type&& value)
      {
        return table_.insert(std::move(value)).first;
      }

      template <class K>
      BOOST_FORCEINLINE typename std::enable_if<
        detail::transparent_non_iterable<K, unordered_flat_set>::value,
        iterator>::type
      insert(const_iterator, K&& k)
      {
        return table_.try_emplace(std::forward<K>(k)).first;
      }

      template <class InputIterator>
      void insert(InputIterator first, InputIterator last)
      {
        for (auto pos = first; pos != last; ++pos) {
          table_.emplace(*pos);
        }
      }

      void insert(std::initializer_list<value_type> ilist)
      {
        this->insert(ilist.begin(), ilist.end());
      }

      template <class... Args>
      BOOST_FORCEINLINE std::pair<iterator, bool> emplace(Args&&... args)
      {
        return table_.emplace(std::forward<Args>(args)...);
      }

      template <class... Args>
      BOOST_FORCEINLINE iterator emplace_hint(const_iterator, Args&&... args)
      {
        return table_.emplace(std::forward<Args>(args)...).first;
      }

      BOOST_FORCEINLINE typename table_type::erase_return_type erase(
        const_iterator pos)
      {
        return table_.erase(pos);
      }

      iterator erase(const_iterator first, const_iterator last)
      {
        while (first != last) {
          this->erase(first++);
        }
        return iterator{detail::foa::const_iterator_cast_tag{}, last};
      }

      BOOST_FORCEINLINE size_type erase(key_type const& key)
      {
        return table_.erase(key);
      }

      template <class K>
      BOOST_FORCEINLINE typename std::enable_if<
        detail::transparent_non_iterable<K, unordered_flat_set>::value,
        size_type>::type
      erase(K const& key)
      {
        return table_.erase(key);
      }

      void swap(unordered_flat_set& rhs) noexcept(
        noexcept(std::declval<table_type&>().swap(std::declval<table_type&>())))
      {
        table_.swap(rhs.table_);
      }

      template <class H2, class P2>
      void merge(unordered_flat_set<key_type, H2, P2, allocator_type>& source)
      {
        table_.merge(source.table_);
      }

      template <class H2, class P2>
      void merge(unordered_flat_set<key_type, H2, P2, allocator_type>&& source)
      {
        table_.merge(std::move(source.table_));
      }

      /// Lookup
      ///

      BOOST_FORCEINLINE size_type count(key_type const& key) const
      {
        auto pos = table_.find(key);
        return pos != table_.end() ? 1 : 0;
      }

      template <class K>
      BOOST_FORCEINLINE typename std::enable_if<
        detail::are_transparent<K, hasher, key_equal>::value, size_type>::type
      count(K const& key) const
      {
        auto pos = table_.find(key);
        return pos != table_.end() ? 1 : 0;
      }

      BOOST_FORCEINLINE iterator find(key_type const& key)
      {
        return table_.find(key);
      }

      BOOST_FORCEINLINE const_iterator find(key_type const& key) const
      {
        return table_.find(key);
      }

      template <class K>
      BOOST_FORCEINLINE typename std::enable_if<
        boost::unordered::detail::are_transparent<K, hasher, key_equal>::value,
        iterator>::type
      find(K const& key)
      {
        return table_.find(key);
      }

      template <class K>
      BOOST_FORCEINLINE typename std::enable_if<
        boost::unordered::detail::are_transparent<K, hasher, key_equal>::value,
        const_iterator>::type
      find(K const& key) const
      {
        return table_.find(key);
      }

      BOOST_FORCEINLINE bool contains(key_type const& key) const
      {
        return this->find(key) != this->end();
      }

      template <class K>
      BOOST_FORCEINLINE typename std::enable_if<
        boost::unordered::detail::are_transparent<K, hasher, key_equal>::value,
        bool>::type
      contains(K const& key) const
      {
        return this->find(key) != this->end();
      }

      std::pair<iterator, iterator> equal_range(key_type const& key)
      {
        auto pos = table_.find(key);
        if (pos == table_.end()) {
          return {pos, pos};
        }

        auto next = pos;
        ++next;
        return {pos, next};
      }

      std::pair<const_iterator, const_iterator> equal_range(
        key_type const& key) const
      {
        auto pos = table_.find(key);
        if (pos == table_.end()) {
          return {pos, pos};
        }

        auto next = pos;
        ++next;
        return {pos, next};
      }

      template <class K>
      typename std::enable_if<
        detail::are_transparent<K, hasher, key_equal>::value,
        std::pair<iterator, iterator> >::type
      equal_range(K const& key)
      {
        auto pos = table_.find(key);
        if (pos == table_.end()) {
          return {pos, pos};
        }

        auto next = pos;
        ++next;
        return {pos, next};
      }

      template <class K>
      typename std::enable_if<
        detail::are_transparent<K, hasher, key_equal>::value,
        std::pair<const_iterator, const_iterator> >::type
      equal_range(K const& key) const
      {
        auto pos = table_.find(key);
        if (pos == table_.end()) {
          return {pos, pos};
        }

        auto next = pos;
        ++next;
        return {pos, next};
      }

      /// Hash Policy
      ///

      size_type bucket_count() const noexcept { return table_.capacity(); }

      float load_factor() const noexcept { return table_.load_factor(); }

      float max_load_factor() const noexcept
      {
        return table_.max_load_factor();
      }

      void max_load_factor(float) {}

      size_type max_load() const noexcept { return table_.max_load(); }

      void rehash(size_type n) { table_.rehash(n); }

      void reserve(size_type n) { table_.reserve(n); }

#ifdef BOOST_UNORDERED_ENABLE_STATS
      /// Stats
      ///
      stats get_stats() const { return table_.get_stats(); }

      void reset_stats() noexcept { table_.reset_stats(); }
#endif

      /// Observers
      ///

      hasher hash_function() const { return table_.hash_function(); }

      key_equal key_eq() const { return table_.key_eq(); }
    };

    template <class Key, class Hash, class KeyEqual, class Allocator>
    bool operator==(
      unordered_flat_set<Key, Hash, KeyEqual, Allocator> const& lhs,
      unordered_flat_set<Key, Hash, KeyEqual, Allocator> const& rhs)
    {
      return lhs.table_ == rhs.table_;
    }

    template <class Key, class Hash, class KeyEqual, class Allocator>
    bool operator!=(
      unordered_flat_set<Key, Hash, KeyEqual, Allocator> const& lhs,
      unordered_flat_set<Key, Hash, KeyEqual, Allocator> const& rhs)
    {
      return !(lhs == rhs);
    }

    template <class Key, class Hash, class KeyEqual, class Allocator>
    void swap(unordered_flat_set<Key, Hash, KeyEqual, Allocator>& lhs,
      unordered_flat_set<Key, Hash, KeyEqual, Allocator>& rhs)
      noexcept(noexcept(lhs.swap(rhs)))
    {
      lhs.swap(rhs);
    }

    template <class Key, class Hash, class KeyEqual, class Allocator,
      class Pred>
    typename unordered_flat_set<Key, Hash, KeyEqual, Allocator>::size_type
    erase_if(unordered_flat_set<Key, Hash, KeyEqual, Allocator>& set, Pred pred)
    {
      return erase_if(set.table_, pred);
    }

    template <class Archive, class Key, class Hash, class KeyEqual,
      class Allocator>
    void serialize(Archive& ar,
      unordered_flat_set<Key, Hash, KeyEqual, Allocator>& set,
      unsigned int version)
    {
      detail::serialize_container(ar, set, version);
    }

#ifdef BOOST_MSVC
#pragma warning(pop)
#endif

#if BOOST_UNORDERED_TEMPLATE_DEDUCTION_GUIDES
    template <class InputIterator,
      class Hash =
        boost::hash<typename std::iterator_traits<InputIterator>::value_type>,
      class Pred =
        std::equal_to<typename std::iterator_traits<InputIterator>::value_type>,
      class Allocator = std::allocator<
        typename std::iterator_traits<InputIterator>::value_type>,
      class = std::enable_if_t<detail::is_input_iterator_v<InputIterator> >,
      class = std::enable_if_t<detail::is_hash_v<Hash> >,
      class = std::enable_if_t<detail::is_pred_v<Pred> >,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_set(InputIterator, InputIterator,
      std::size_t = boost::unordered::detail::foa::default_bucket_count,
      Hash = Hash(), Pred = Pred(), Allocator = Allocator())
      -> unordered_flat_set<
        typename std::iterator_traits<InputIterator>::value_type, Hash, Pred,
        Allocator>;

    template <class T, class Hash = boost::hash<T>,
      class Pred = std::equal_to<T>, class Allocator = std::allocator<T>,
      class = std::enable_if_t<detail::is_hash_v<Hash> >,
      class = std::enable_if_t<detail::is_pred_v<Pred> >,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_set(std::initializer_list<T>,
      std::size_t = boost::unordered::detail::foa::default_bucket_count,
      Hash = Hash(), Pred = Pred(), Allocator = Allocator())
      -> unordered_flat_set<T, Hash, Pred, Allocator>;

    template <class InputIterator, class Allocator,
      class = std::enable_if_t<detail::is_input_iterator_v<InputIterator> >,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_set(InputIterator, InputIterator, std::size_t, Allocator)
      -> unordered_flat_set<
        typename std::iterator_traits<InputIterator>::value_type,
        boost::hash<typename std::iterator_traits<InputIterator>::value_type>,
        std::equal_to<typename std::iterator_traits<InputIterator>::value_type>,
        Allocator>;

    template <class InputIterator, class Hash, class Allocator,
      class = std::enable_if_t<detail::is_hash_v<Hash> >,
      class = std::enable_if_t<detail::is_input_iterator_v<InputIterator> >,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_set(
      InputIterator, InputIterator, std::size_t, Hash, Allocator)
      -> unordered_flat_set<
        typename std::iterator_traits<InputIterator>::value_type, Hash,
        std::equal_to<typename std::iterator_traits<InputIterator>::value_type>,
        Allocator>;

    template <class T, class Allocator,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_set(std::initializer_list<T>, std::size_t, Allocator)
      -> unordered_flat_set<T, boost::hash<T>, std::equal_to<T>, Allocator>;

    template <class T, class Hash, class Allocator,
      class = std::enable_if_t<detail::is_hash_v<Hash> >,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_set(std::initializer_list<T>, std::size_t, Hash, Allocator)
      -> unordered_flat_set<T, Hash, std::equal_to<T>, Allocator>;

    template <class InputIterator, class Allocator,
      class = std::enable_if_t<detail::is_input_iterator_v<InputIterator> >,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_set(InputIterator, InputIterator, Allocator)
      -> unordered_flat_set<
        typename std::iterator_traits<InputIterator>::value_type,
        boost::hash<typename std::iterator_traits<InputIterator>::value_type>,
        std::equal_to<typename std::iterator_traits<InputIterator>::value_type>,
        Allocator>;

    template <class T, class Allocator,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_set(std::initializer_list<T>, Allocator)
      -> unordered_flat_set<T, boost::hash<T>, std::equal_to<T>, Allocator>;
#endif

  } // namespace unordered
} // namespace boost

#endif
/* Fast open-addressing concurrent hashmap.
 *
 * Copyright 2023 Christian Mazakas.
 * Copyright 2024 Braden Ganetsky.
 * Distributed under the Boost Software License, Version 1.0.
 * (See accompanying file LICENSE_1_0.txt or copy at
 * http://www.boost.org/LICENSE_1_0.txt)
 *
 * See https://www.boost.org/libs/unordered for library home page.
 */

#ifndef BOOST_UNORDERED_CONCURRENT_FLAT_MAP_FWD_HPP
#define BOOST_UNORDERED_CONCURRENT_FLAT_MAP_FWD_HPP

namespace boost {
  namespace unordered {

    template <class Key, class T, class Hash = boost::hash<Key>,
      class Pred = std::equal_to<Key>,
      class Allocator = std::allocator<std::pair<Key const, T> > >
    class concurrent_flat_map;

    template <class Key, class T, class Hash, class KeyEqual, class Allocator>
    bool operator==(
      concurrent_flat_map<Key, T, Hash, KeyEqual, Allocator> const& lhs,
      concurrent_flat_map<Key, T, Hash, KeyEqual, Allocator> const& rhs);

    template <class Key, class T, class Hash, class KeyEqual, class Allocator>
    bool operator!=(
      concurrent_flat_map<Key, T, Hash, KeyEqual, Allocator> const& lhs,
      concurrent_flat_map<Key, T, Hash, KeyEqual, Allocator> const& rhs);

    template <class Key, class T, class Hash, class Pred, class Alloc>
    void swap(concurrent_flat_map<Key, T, Hash, Pred, Alloc>& x,
      concurrent_flat_map<Key, T, Hash, Pred, Alloc>& y)
      noexcept(noexcept(x.swap(y)));

    template <class K, class T, class H, class P, class A, class Predicate>
    typename concurrent_flat_map<K, T, H, P, A>::size_type erase_if(
      concurrent_flat_map<K, T, H, P, A>& c, Predicate pred);

#ifndef BOOST_NO_CXX17_HDR_MEMORY_RESOURCE
    namespace pmr {
      template <class Key, class T, class Hash = boost::hash<Key>,
        class Pred = std::equal_to<Key> >
      using concurrent_flat_map = boost::unordered::concurrent_flat_map<Key, T,
        Hash, Pred, std::pmr::polymorphic_allocator<std::pair<Key const, T> > >;
    } // namespace pmr
#endif

  } // namespace unordered

  using boost::unordered::concurrent_flat_map;
} // namespace boost

#endif // BOOST_UNORDERED_CONCURRENT_FLAT_MAP_HPP
// Copyright (C) 2023 Christian Mazakas
// Copyright (C) 2024 Braden Ganetsky
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_UNORDERED_DETAIL_FOA_FLAT_MAP_TYPES_HPP
#define BOOST_UNORDERED_DETAIL_FOA_FLAT_MAP_TYPES_HPP

namespace boost {
  namespace unordered {
    namespace detail {
      namespace foa {
        template <class Key, class T> struct flat_map_types
        {
          using key_type = Key;
          using mapped_type = T;
          using raw_key_type = typename std::remove_const<Key>::type;
          using raw_mapped_type = typename std::remove_const<T>::type;

          using init_type = std::pair<raw_key_type, raw_mapped_type>;
          using moved_type = std::pair<raw_key_type&&, raw_mapped_type&&>;
          using value_type = std::pair<Key const, T>;

          using element_type = value_type;

          using types = flat_map_types<Key, T>;
          using constructibility_checker = map_types_constructibility<types>;

          static value_type& value_from(element_type& x) { return x; }

          template <class K, class V>
          static raw_key_type const& extract(std::pair<K, V> const& kv)
          {
            return kv.first;
          }

          static moved_type move(init_type& x)
          {
            return {std::move(x.first), std::move(x.second)};
          }

          static moved_type move(element_type& x)
          {
            // TODO: we probably need to launder here
            return {std::move(const_cast<raw_key_type&>(x.first)),
              std::move(const_cast<raw_mapped_type&>(x.second))};
          }

          template <class A, class... Args>
          static void construct(A& al, init_type* p, Args&&... args)
          {
            constructibility_checker::check(al, p, std::forward<Args>(args)...);
            std::allocator_traits<std::remove_cvref_t<decltype(al)>>::construct(al, p, std::forward<Args>(args)...);
          }

          template <class A, class... Args>
          static void construct(A& al, value_type* p, Args&&... args)
          {
            constructibility_checker::check(al, p, std::forward<Args>(args)...);
            std::allocator_traits<std::remove_cvref_t<decltype(al)>>::construct(al, p, std::forward<Args>(args)...);
          }

          template <class A, class... Args>
          static void construct(A& al, key_type* p, Args&&... args)
          {
            constructibility_checker::check(al, p, std::forward<Args>(args)...);
            std::allocator_traits<std::remove_cvref_t<decltype(al)>>::construct(al, p, std::forward<Args>(args)...);
          }

          template <class A> static void destroy(A& al, init_type* p) noexcept
          {
            std::allocator_traits<std::remove_cvref_t<decltype(al)>>::destroy(al,  p);
          }

          template <class A> static void destroy(A& al, value_type* p) noexcept
          {
            std::allocator_traits<std::remove_cvref_t<decltype(al)>>::destroy(al,  p);
          }

          template <class A> static void destroy(A& al, key_type* p) noexcept
          {
            std::allocator_traits<std::remove_cvref_t<decltype(al)>>::destroy(al,  p);
          }
        };
      } // namespace foa
    } // namespace detail
  } // namespace unordered
} // namespace boost

#endif // BOOST_UNORDERED_DETAIL_FOA_FLAT_MAP_TYPES_HPP
// Copyright (C) 2023 Braden Ganetsky
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_UNORDERED_DETAIL_THROW_EXCEPTION_HPP
#define BOOST_UNORDERED_DETAIL_THROW_EXCEPTION_HPP

#pragma once

namespace boost {
  namespace unordered {
    namespace detail {

      BOOST_NOINLINE BOOST_NORETURN inline void throw_out_of_range(
        char const* message)
      {
        boost::throw_exception(std::out_of_range(message));
      }

    } // namespace detail
  } // namespace unordered
} // namespace boost

#endif // BOOST_UNORDERED_DETAIL_THROW_EXCEPTION_HPP
// Copyright (C) 2022 Christian Mazakas
// Copyright (C) 2024 Braden Ganetsky
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_UNORDERED_FLAT_MAP_FWD_HPP_INCLUDED
#define BOOST_UNORDERED_FLAT_MAP_FWD_HPP_INCLUDED

#pragma once

namespace boost {
  namespace unordered {
    template <class Key, class T, class Hash = boost::hash<Key>,
      class KeyEqual = std::equal_to<Key>,
      class Allocator = std::allocator<std::pair<const Key, T> > >
    class unordered_flat_map;

    template <class Key, class T, class Hash, class KeyEqual, class Allocator>
    bool operator==(
      unordered_flat_map<Key, T, Hash, KeyEqual, Allocator> const& lhs,
      unordered_flat_map<Key, T, Hash, KeyEqual, Allocator> const& rhs);

    template <class Key, class T, class Hash, class KeyEqual, class Allocator>
    bool operator!=(
      unordered_flat_map<Key, T, Hash, KeyEqual, Allocator> const& lhs,
      unordered_flat_map<Key, T, Hash, KeyEqual, Allocator> const& rhs);

    template <class Key, class T, class Hash, class KeyEqual, class Allocator>
    void swap(unordered_flat_map<Key, T, Hash, KeyEqual, Allocator>& lhs,
      unordered_flat_map<Key, T, Hash, KeyEqual, Allocator>& rhs)
      noexcept(noexcept(lhs.swap(rhs)));

#ifndef BOOST_NO_CXX17_HDR_MEMORY_RESOURCE
    namespace pmr {
      template <class Key, class T, class Hash = boost::hash<Key>,
        class KeyEqual = std::equal_to<Key> >
      using unordered_flat_map =
        boost::unordered::unordered_flat_map<Key, T, Hash, KeyEqual,
          std::pmr::polymorphic_allocator<std::pair<const Key, T> > >;
    } // namespace pmr
#endif
  } // namespace unordered

  using boost::unordered::unordered_flat_map;
} // namespace boost

#endif
// Copyright (C) 2022-2023 Christian Mazakas
// Copyright (C) 2024 Joaquin M Lopez Munoz
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef BOOST_UNORDERED_UNORDERED_FLAT_MAP_HPP_INCLUDED
#define BOOST_UNORDERED_UNORDERED_FLAT_MAP_HPP_INCLUDED

#pragma once

namespace boost {
  namespace unordered {

#ifdef BOOST_MSVC
#pragma warning(push)
#pragma warning(disable : 4714)
#endif

    template <class Key, class T, class Hash, class KeyEqual, class Allocator>
    class unordered_flat_map
    {
      template <class Key2, class T2, class Hash2, class Pred2,
        class Allocator2>
      friend class concurrent_flat_map;

      using map_types = detail::foa::flat_map_types<Key, T>;

      using table_type = detail::foa::table<map_types, Hash, KeyEqual,
        typename std::allocator_traits<Allocator>::template rebind_alloc<
          typename map_types::value_type>>;

      table_type table_;

      template <class K, class V, class H, class KE, class A>
      bool friend operator==(unordered_flat_map<K, V, H, KE, A> const& lhs,
        unordered_flat_map<K, V, H, KE, A> const& rhs);

      template <class K, class V, class H, class KE, class A, class Pred>
      typename unordered_flat_map<K, V, H, KE, A>::size_type friend erase_if(
        unordered_flat_map<K, V, H, KE, A>& set, Pred pred);

    public:
      using key_type = Key;
      using mapped_type = T;
      using value_type = typename map_types::value_type;
      using init_type = typename map_types::init_type;
      using size_type = std::size_t;
      using difference_type = std::ptrdiff_t;
      using hasher = typename boost::unordered::detail::type_identity<Hash>::type;
      using key_equal = typename boost::unordered::detail::type_identity<KeyEqual>::type;
      using allocator_type = typename boost::unordered::detail::type_identity<Allocator>::type;
      using reference = value_type&;
      using const_reference = value_type const&;
      using pointer = typename std::allocator_traits<allocator_type>::pointer;
      using const_pointer =
        typename std::allocator_traits<allocator_type>::const_pointer;
      using iterator = typename table_type::iterator;
      using const_iterator = typename table_type::const_iterator;

#ifdef BOOST_UNORDERED_ENABLE_STATS
      using stats = typename table_type::stats;
#endif

      unordered_flat_map() : unordered_flat_map(0) {}

      explicit unordered_flat_map(size_type n, hasher const& h = hasher(),
        key_equal const& pred = key_equal(),
        allocator_type const& a = allocator_type())
          : table_(n, h, pred, a)
      {
      }

      unordered_flat_map(size_type n, allocator_type const& a)
          : unordered_flat_map(n, hasher(), key_equal(), a)
      {
      }

      unordered_flat_map(size_type n, hasher const& h, allocator_type const& a)
          : unordered_flat_map(n, h, key_equal(), a)
      {
      }

      template <class InputIterator>
      unordered_flat_map(
        InputIterator f, InputIterator l, allocator_type const& a)
          : unordered_flat_map(f, l, size_type(0), hasher(), key_equal(), a)
      {
      }

      explicit unordered_flat_map(allocator_type const& a)
          : unordered_flat_map(0, a)
      {
      }

      template <class Iterator>
      unordered_flat_map(Iterator first, Iterator last, size_type n = 0,
        hasher const& h = hasher(), key_equal const& pred = key_equal(),
        allocator_type const& a = allocator_type())
          : unordered_flat_map(n, h, pred, a)
      {
        this->insert(first, last);
      }

      template <class Iterator>
      unordered_flat_map(
        Iterator first, Iterator last, size_type n, allocator_type const& a)
          : unordered_flat_map(first, last, n, hasher(), key_equal(), a)
      {
      }

      template <class Iterator>
      unordered_flat_map(Iterator first, Iterator last, size_type n,
        hasher const& h, allocator_type const& a)
          : unordered_flat_map(first, last, n, h, key_equal(), a)
      {
      }

      unordered_flat_map(unordered_flat_map const& other) : table_(other.table_)
      {
      }

      unordered_flat_map(
        unordered_flat_map const& other, allocator_type const& a)
          : table_(other.table_, a)
      {
      }

      unordered_flat_map(unordered_flat_map&& other)
        noexcept(std::is_nothrow_move_constructible<table_type>::value)
          : table_(std::move(other.table_))
      {
      }

      unordered_flat_map(unordered_flat_map&& other, allocator_type const& al)
          : table_(std::move(other.table_), al)
      {
      }

      unordered_flat_map(std::initializer_list<value_type> ilist,
        size_type n = 0, hasher const& h = hasher(),
        key_equal const& pred = key_equal(),
        allocator_type const& a = allocator_type())
          : unordered_flat_map(ilist.begin(), ilist.end(), n, h, pred, a)
      {
      }

      unordered_flat_map(
        std::initializer_list<value_type> il, allocator_type const& a)
          : unordered_flat_map(il, size_type(0), hasher(), key_equal(), a)
      {
      }

      unordered_flat_map(std::initializer_list<value_type> init, size_type n,
        allocator_type const& a)
          : unordered_flat_map(init, n, hasher(), key_equal(), a)
      {
      }

      unordered_flat_map(std::initializer_list<value_type> init, size_type n,
        hasher const& h, allocator_type const& a)
          : unordered_flat_map(init, n, h, key_equal(), a)
      {
      }

      template <bool avoid_explicit_instantiation = true>
      unordered_flat_map(
        concurrent_flat_map<Key, T, Hash, KeyEqual, Allocator>&& other)
          : table_(std::move(other.table_))
      {
      }

      ~unordered_flat_map() = default;

      unordered_flat_map& operator=(unordered_flat_map const& other)
      {
        table_ = other.table_;
        return *this;
      }

      unordered_flat_map& operator=(unordered_flat_map&& other) noexcept(
        noexcept(std::declval<table_type&>() = std::declval<table_type&&>()))
      {
        table_ = std::move(other.table_);
        return *this;
      }

      unordered_flat_map& operator=(std::initializer_list<value_type> il)
      {
        this->clear();
        this->insert(il.begin(), il.end());
        return *this;
      }

      allocator_type get_allocator() const noexcept
      {
        return table_.get_allocator();
      }

      /// Iterators
      ///

      iterator begin() noexcept { return table_.begin(); }
      const_iterator begin() const noexcept { return table_.begin(); }
      const_iterator cbegin() const noexcept { return table_.cbegin(); }

      iterator end() noexcept { return table_.end(); }
      const_iterator end() const noexcept { return table_.end(); }
      const_iterator cend() const noexcept { return table_.cend(); }

      /// Capacity
      ///

      [[nodiscard]] bool empty() const noexcept
      {
        return table_.empty();
      }

      size_type size() const noexcept { return table_.size(); }

      size_type max_size() const noexcept { return table_.max_size(); }

      /// Modifiers
      ///

      void clear() noexcept { table_.clear(); }

      template <class Ty>
      BOOST_FORCEINLINE auto insert(Ty&& value)
        -> decltype(table_.insert(std::forward<Ty>(value)))
      {
        return table_.insert(std::forward<Ty>(value));
      }

      BOOST_FORCEINLINE std::pair<iterator, bool> insert(init_type&& value)
      {
        return table_.insert(std::move(value));
      }

      template <class Ty>
      BOOST_FORCEINLINE auto insert(const_iterator, Ty&& value)
        -> decltype(table_.insert(std::forward<Ty>(value)).first)
      {
        return table_.insert(std::forward<Ty>(value)).first;
      }

      BOOST_FORCEINLINE iterator insert(const_iterator, init_type&& value)
      {
        return table_.insert(std::move(value)).first;
      }

      template <class InputIterator>
      BOOST_FORCEINLINE void insert(InputIterator first, InputIterator last)
      {
        for (auto pos = first; pos != last; ++pos) {
          table_.emplace(*pos);
        }
      }

      void insert(std::initializer_list<value_type> ilist)
      {
        this->insert(ilist.begin(), ilist.end());
      }

      template <class M>
      std::pair<iterator, bool> insert_or_assign(key_type const& key, M&& obj)
      {
        auto ibp = table_.try_emplace(key, std::forward<M>(obj));
        if (ibp.second) {
          return ibp;
        }
        ibp.first->second = std::forward<M>(obj);
        return ibp;
      }

      template <class M>
      std::pair<iterator, bool> insert_or_assign(key_type&& key, M&& obj)
      {
        auto ibp = table_.try_emplace(std::move(key), std::forward<M>(obj));
        if (ibp.second) {
          return ibp;
        }
        ibp.first->second = std::forward<M>(obj);
        return ibp;
      }

      template <class K, class M>
      typename std::enable_if<
        boost::unordered::detail::are_transparent<K, hasher, key_equal>::value,
        std::pair<iterator, bool> >::type
      insert_or_assign(K&& k, M&& obj)
      {
        auto ibp = table_.try_emplace(std::forward<K>(k), std::forward<M>(obj));
        if (ibp.second) {
          return ibp;
        }
        ibp.first->second = std::forward<M>(obj);
        return ibp;
      }

      template <class M>
      iterator insert_or_assign(const_iterator, key_type const& key, M&& obj)
      {
        return this->insert_or_assign(key, std::forward<M>(obj)).first;
      }

      template <class M>
      iterator insert_or_assign(const_iterator, key_type&& key, M&& obj)
      {
        return this->insert_or_assign(std::move(key), std::forward<M>(obj))
          .first;
      }

      template <class K, class M>
      typename std::enable_if<
        boost::unordered::detail::are_transparent<K, hasher, key_equal>::value,
        iterator>::type
      insert_or_assign(const_iterator, K&& k, M&& obj)
      {
        return this->insert_or_assign(std::forward<K>(k), std::forward<M>(obj))
          .first;
      }

      template <class... Args>
      BOOST_FORCEINLINE std::pair<iterator, bool> emplace(Args&&... args)
      {
        return table_.emplace(std::forward<Args>(args)...);
      }

      template <class... Args>
      BOOST_FORCEINLINE iterator emplace_hint(const_iterator, Args&&... args)
      {
        return table_.emplace(std::forward<Args>(args)...).first;
      }

      template <class... Args>
      BOOST_FORCEINLINE std::pair<iterator, bool> try_emplace(
        key_type const& key, Args&&... args)
      {
        return table_.try_emplace(key, std::forward<Args>(args)...);
      }

      template <class... Args>
      BOOST_FORCEINLINE std::pair<iterator, bool> try_emplace(
        key_type&& key, Args&&... args)
      {
        return table_.try_emplace(std::move(key), std::forward<Args>(args)...);
      }

      template <class K, class... Args>
      BOOST_FORCEINLINE typename std::enable_if<
        boost::unordered::detail::transparent_non_iterable<K,
          unordered_flat_map>::value,
        std::pair<iterator, bool> >::type
      try_emplace(K&& key, Args&&... args)
      {
        return table_.try_emplace(
          std::forward<K>(key), std::forward<Args>(args)...);
      }

      template <class... Args>
      BOOST_FORCEINLINE iterator try_emplace(
        const_iterator, key_type const& key, Args&&... args)
      {
        return table_.try_emplace(key, std::forward<Args>(args)...).first;
      }

      template <class... Args>
      BOOST_FORCEINLINE iterator try_emplace(
        const_iterator, key_type&& key, Args&&... args)
      {
        return table_.try_emplace(std::move(key), std::forward<Args>(args)...)
          .first;
      }

      template <class K, class... Args>
      BOOST_FORCEINLINE typename std::enable_if<
        boost::unordered::detail::transparent_non_iterable<K,
          unordered_flat_map>::value,
        iterator>::type
      try_emplace(const_iterator, K&& key, Args&&... args)
      {
        return table_
          .try_emplace(std::forward<K>(key), std::forward<Args>(args)...)
          .first;
      }

      BOOST_FORCEINLINE typename table_type::erase_return_type erase(
        iterator pos)
      {
        return table_.erase(pos);
      }

      BOOST_FORCEINLINE typename table_type::erase_return_type erase(
        const_iterator pos)
      {
        return table_.erase(pos);
      }

      iterator erase(const_iterator first, const_iterator last)
      {
        while (first != last) {
          this->erase(first++);
        }
        return iterator{detail::foa::const_iterator_cast_tag{}, last};
      }

      BOOST_FORCEINLINE size_type erase(key_type const& key)
      {
        return table_.erase(key);
      }

      template <class K>
      BOOST_FORCEINLINE typename std::enable_if<
        detail::transparent_non_iterable<K, unordered_flat_map>::value,
        size_type>::type
      erase(K const& key)
      {
        return table_.erase(key);
      }

      void swap(unordered_flat_map& rhs) noexcept(
        noexcept(std::declval<table_type&>().swap(std::declval<table_type&>())))
      {
        table_.swap(rhs.table_);
      }

      template <class H2, class P2>
      void merge(
        unordered_flat_map<key_type, mapped_type, H2, P2, allocator_type>&
          source)
      {
        table_.merge(source.table_);
      }

      template <class H2, class P2>
      void merge(
        unordered_flat_map<key_type, mapped_type, H2, P2, allocator_type>&&
          source)
      {
        table_.merge(std::move(source.table_));
      }

      /// Lookup
      ///

      mapped_type& at(key_type const& key)
      {
        auto pos = table_.find(key);
        if (pos != table_.end()) {
          return pos->second;
        }
        // TODO: someday refactor this to conditionally serialize the key and
        // include it in the error message
        //
        boost::unordered::detail::throw_out_of_range(
          "key was not found in unordered_flat_map");
      }

      mapped_type const& at(key_type const& key) const
      {
        auto pos = table_.find(key);
        if (pos != table_.end()) {
          return pos->second;
        }
        boost::unordered::detail::throw_out_of_range(
          "key was not found in unordered_flat_map");
      }

      template <class K>
      typename std::enable_if<
        boost::unordered::detail::are_transparent<K, hasher, key_equal>::value,
        mapped_type&>::type
      at(K&& key)
      {
        auto pos = table_.find(std::forward<K>(key));
        if (pos != table_.end()) {
          return pos->second;
        }
        boost::unordered::detail::throw_out_of_range(
          "key was not found in unordered_flat_map");
      }

      template <class K>
      typename std::enable_if<
        boost::unordered::detail::are_transparent<K, hasher, key_equal>::value,
        mapped_type const&>::type
      at(K&& key) const
      {
        auto pos = table_.find(std::forward<K>(key));
        if (pos != table_.end()) {
          return pos->second;
        }
        boost::unordered::detail::throw_out_of_range(
          "key was not found in unordered_flat_map");
      }

      BOOST_FORCEINLINE mapped_type& operator[](key_type const& key)
      {
        return table_.try_emplace(key).first->second;
      }

      BOOST_FORCEINLINE mapped_type& operator[](key_type&& key)
      {
        return table_.try_emplace(std::move(key)).first->second;
      }

      template <class K>
      typename std::enable_if<
        boost::unordered::detail::are_transparent<K, hasher, key_equal>::value,
        mapped_type&>::type
      operator[](K&& key)
      {
        return table_.try_emplace(std::forward<K>(key)).first->second;
      }

      BOOST_FORCEINLINE size_type count(key_type const& key) const
      {
        auto pos = table_.find(key);
        return pos != table_.end() ? 1 : 0;
      }

      template <class K>
      BOOST_FORCEINLINE typename std::enable_if<
        detail::are_transparent<K, hasher, key_equal>::value, size_type>::type
      count(K const& key) const
      {
        auto pos = table_.find(key);
        return pos != table_.end() ? 1 : 0;
      }

      BOOST_FORCEINLINE iterator find(key_type const& key)
      {
        return table_.find(key);
      }

      BOOST_FORCEINLINE const_iterator find(key_type const& key) const
      {
        return table_.find(key);
      }

      template <class K>
      BOOST_FORCEINLINE typename std::enable_if<
        boost::unordered::detail::are_transparent<K, hasher, key_equal>::value,
        iterator>::type
      find(K const& key)
      {
        return table_.find(key);
      }

      template <class K>
      BOOST_FORCEINLINE typename std::enable_if<
        boost::unordered::detail::are_transparent<K, hasher, key_equal>::value,
        const_iterator>::type
      find(K const& key) const
      {
        return table_.find(key);
      }

      BOOST_FORCEINLINE bool contains(key_type const& key) const
      {
        return this->find(key) != this->end();
      }

      template <class K>
      BOOST_FORCEINLINE typename std::enable_if<
        boost::unordered::detail::are_transparent<K, hasher, key_equal>::value,
        bool>::type
      contains(K const& key) const
      {
        return this->find(key) != this->end();
      }

      std::pair<iterator, iterator> equal_range(key_type const& key)
      {
        auto pos = table_.find(key);
        if (pos == table_.end()) {
          return {pos, pos};
        }

        auto next = pos;
        ++next;
        return {pos, next};
      }

      std::pair<const_iterator, const_iterator> equal_range(
        key_type const& key) const
      {
        auto pos = table_.find(key);
        if (pos == table_.end()) {
          return {pos, pos};
        }

        auto next = pos;
        ++next;
        return {pos, next};
      }

      template <class K>
      typename std::enable_if<
        detail::are_transparent<K, hasher, key_equal>::value,
        std::pair<iterator, iterator> >::type
      equal_range(K const& key)
      {
        auto pos = table_.find(key);
        if (pos == table_.end()) {
          return {pos, pos};
        }

        auto next = pos;
        ++next;
        return {pos, next};
      }

      template <class K>
      typename std::enable_if<
        detail::are_transparent<K, hasher, key_equal>::value,
        std::pair<const_iterator, const_iterator> >::type
      equal_range(K const& key) const
      {
        auto pos = table_.find(key);
        if (pos == table_.end()) {
          return {pos, pos};
        }

        auto next = pos;
        ++next;
        return {pos, next};
      }

      /// Hash Policy
      ///

      size_type bucket_count() const noexcept { return table_.capacity(); }

      float load_factor() const noexcept { return table_.load_factor(); }

      float max_load_factor() const noexcept
      {
        return table_.max_load_factor();
      }

      void max_load_factor(float) {}

      size_type max_load() const noexcept { return table_.max_load(); }

      void rehash(size_type n) { table_.rehash(n); }

      void reserve(size_type n) { table_.reserve(n); }

#ifdef BOOST_UNORDERED_ENABLE_STATS
      /// Stats
      ///
      stats get_stats() const { return table_.get_stats(); }

      void reset_stats() noexcept { table_.reset_stats(); }
#endif

      /// Observers
      ///

      hasher hash_function() const { return table_.hash_function(); }

      key_equal key_eq() const { return table_.key_eq(); }
    };

    template <class Key, class T, class Hash, class KeyEqual, class Allocator>
    bool operator==(
      unordered_flat_map<Key, T, Hash, KeyEqual, Allocator> const& lhs,
      unordered_flat_map<Key, T, Hash, KeyEqual, Allocator> const& rhs)
    {
      return lhs.table_ == rhs.table_;
    }

    template <class Key, class T, class Hash, class KeyEqual, class Allocator>
    bool operator!=(
      unordered_flat_map<Key, T, Hash, KeyEqual, Allocator> const& lhs,
      unordered_flat_map<Key, T, Hash, KeyEqual, Allocator> const& rhs)
    {
      return !(lhs == rhs);
    }

    template <class Key, class T, class Hash, class KeyEqual, class Allocator>
    void swap(unordered_flat_map<Key, T, Hash, KeyEqual, Allocator>& lhs,
      unordered_flat_map<Key, T, Hash, KeyEqual, Allocator>& rhs)
      noexcept(noexcept(lhs.swap(rhs)))
    {
      lhs.swap(rhs);
    }

    template <class Key, class T, class Hash, class KeyEqual, class Allocator,
      class Pred>
    typename unordered_flat_map<Key, T, Hash, KeyEqual, Allocator>::size_type
    erase_if(
      unordered_flat_map<Key, T, Hash, KeyEqual, Allocator>& map, Pred pred)
    {
      return erase_if(map.table_, pred);
    }

    template <class Archive, class Key, class T, class Hash, class KeyEqual,
      class Allocator>
    void serialize(Archive& ar,
      unordered_flat_map<Key, T, Hash, KeyEqual, Allocator>& map,
      unsigned int version)
    {
      detail::serialize_container(ar, map, version);
    }

#ifdef BOOST_MSVC
#pragma warning(pop)
#endif

#if BOOST_UNORDERED_TEMPLATE_DEDUCTION_GUIDES

    template <class InputIterator,
      class Hash =
        boost::hash<boost::unordered::detail::iter_key_t<InputIterator> >,
      class Pred =
        std::equal_to<boost::unordered::detail::iter_key_t<InputIterator> >,
      class Allocator = std::allocator<
        boost::unordered::detail::iter_to_alloc_t<InputIterator> >,
      class = std::enable_if_t<detail::is_input_iterator_v<InputIterator> >,
      class = std::enable_if_t<detail::is_hash_v<Hash> >,
      class = std::enable_if_t<detail::is_pred_v<Pred> >,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_map(InputIterator, InputIterator,
      std::size_t = boost::unordered::detail::foa::default_bucket_count,
      Hash = Hash(), Pred = Pred(), Allocator = Allocator())
      -> unordered_flat_map<boost::unordered::detail::iter_key_t<InputIterator>,
        boost::unordered::detail::iter_val_t<InputIterator>, Hash, Pred,
        Allocator>;

    template <class Key, class T,
      class Hash = boost::hash<std::remove_const_t<Key> >,
      class Pred = std::equal_to<std::remove_const_t<Key> >,
      class Allocator = std::allocator<std::pair<const Key, T> >,
      class = std::enable_if_t<detail::is_hash_v<Hash> >,
      class = std::enable_if_t<detail::is_pred_v<Pred> >,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_map(std::initializer_list<std::pair<Key, T> >,
      std::size_t = boost::unordered::detail::foa::default_bucket_count,
      Hash = Hash(), Pred = Pred(), Allocator = Allocator())
      -> unordered_flat_map<std::remove_const_t<Key>, T, Hash, Pred,
        Allocator>;

    template <class InputIterator, class Allocator,
      class = std::enable_if_t<detail::is_input_iterator_v<InputIterator> >,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_map(InputIterator, InputIterator, std::size_t, Allocator)
      -> unordered_flat_map<boost::unordered::detail::iter_key_t<InputIterator>,
        boost::unordered::detail::iter_val_t<InputIterator>,
        boost::hash<boost::unordered::detail::iter_key_t<InputIterator> >,
        std::equal_to<boost::unordered::detail::iter_key_t<InputIterator> >,
        Allocator>;

    template <class InputIterator, class Allocator,
      class = std::enable_if_t<detail::is_input_iterator_v<InputIterator> >,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_map(InputIterator, InputIterator, Allocator)
      -> unordered_flat_map<boost::unordered::detail::iter_key_t<InputIterator>,
        boost::unordered::detail::iter_val_t<InputIterator>,
        boost::hash<boost::unordered::detail::iter_key_t<InputIterator> >,
        std::equal_to<boost::unordered::detail::iter_key_t<InputIterator> >,
        Allocator>;

    template <class InputIterator, class Hash, class Allocator,
      class = std::enable_if_t<detail::is_hash_v<Hash> >,
      class = std::enable_if_t<detail::is_input_iterator_v<InputIterator> >,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_map(
      InputIterator, InputIterator, std::size_t, Hash, Allocator)
      -> unordered_flat_map<boost::unordered::detail::iter_key_t<InputIterator>,
        boost::unordered::detail::iter_val_t<InputIterator>, Hash,
        std::equal_to<boost::unordered::detail::iter_key_t<InputIterator> >,
        Allocator>;

    template <class Key, class T, class Allocator,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_map(std::initializer_list<std::pair<Key, T> >, std::size_t,
      Allocator) -> unordered_flat_map<std::remove_const_t<Key>, T,
      boost::hash<std::remove_const_t<Key> >,
      std::equal_to<std::remove_const_t<Key> >, Allocator>;

    template <class Key, class T, class Allocator,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_map(std::initializer_list<std::pair<Key, T> >, Allocator)
      -> unordered_flat_map<std::remove_const_t<Key>, T,
        boost::hash<std::remove_const_t<Key> >,
        std::equal_to<std::remove_const_t<Key> >, Allocator>;

    template <class Key, class T, class Hash, class Allocator,
      class = std::enable_if_t<detail::is_hash_v<Hash> >,
      class = std::enable_if_t<detail::is_allocator_v<Allocator> > >
    unordered_flat_map(std::initializer_list<std::pair<Key, T> >, std::size_t,
      Hash, Allocator) -> unordered_flat_map<std::remove_const_t<Key>, T,
      Hash, std::equal_to<std::remove_const_t<Key> >, Allocator>;
#endif

  } // namespace unordered
} // namespace boost

#endif
