//! \file eggs/variant/detail/storage.hpp
// Eggs.Variant
//
// Copyright Agustin K-ballo Berge, Fusion Fenix 2014-2016
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef EGGS_VARIANT_DETAIL_STORAGE_HPP
#define EGGS_VARIANT_DETAIL_STORAGE_HPP

#include <eggs/variant/detail/pack.hpp>
#include <eggs/variant/detail/utility.hpp>
#include <eggs/variant/detail/visitor.hpp>

#include <cstddef>
#include <new>
#include <type_traits>
#include <typeinfo>
#include <utility>

#include <eggs/variant/detail/config/prefix.hpp>

namespace eggs { namespace variants { namespace detail
{
    template <typename Ts, bool IsTriviallyDestructible>
    struct _union;

#if EGGS_CXX11_HAS_UNRESTRICTED_UNIONS
    ///////////////////////////////////////////////////////////////////////////
    template <bool IsTriviallyDestructible>
    struct _union<pack<>, IsTriviallyDestructible>
    {};

    template <typename T, typename ...Ts>
    struct _union<pack<T, Ts...>, true>
    {
        EGGS_CXX11_STATIC_CONSTEXPR std::size_t size = 1 + sizeof...(Ts);

        template <typename ...Args>
        EGGS_CXX11_CONSTEXPR _union(index<0>, Args&&... args)
          : _head(detail::forward<Args>(args)...)
        {}

        template <std::size_t I, typename ...Args>
        EGGS_CXX11_CONSTEXPR _union(index<I>, Args&&... args)
          : _tail(index<I - 1>{}, detail::forward<Args>(args)...)
        {}

        EGGS_CXX14_CONSTEXPR void* target() EGGS_CXX11_NOEXCEPT
        {
            return &_target;
        }

        EGGS_CXX11_CONSTEXPR void const* target() const EGGS_CXX11_NOEXCEPT
        {
            return &_target;
        }

        EGGS_CXX14_CONSTEXPR T& get(index<0>) EGGS_CXX11_NOEXCEPT
        {
            return this->_head;
        }

        EGGS_CXX11_CONSTEXPR T const& get(index<0>) const EGGS_CXX11_NOEXCEPT
        {
            return this->_head;
        }

        template <
            std::size_t I
          , typename U = typename at_index<I, pack<T, Ts...>>::type
        >
        EGGS_CXX14_CONSTEXPR U& get(index<I>) EGGS_CXX11_NOEXCEPT
        {
            return this->_tail.get(index<I - 1>{});
        }

        template <
            std::size_t I
          , typename U = typename at_index<I, pack<T, Ts...>>::type
        >
        EGGS_CXX11_CONSTEXPR U const& get(index<I>) const EGGS_CXX11_NOEXCEPT
        {
            return this->_tail.get(index<I - 1>{});
        }

    private:
        union
        {
            char _target;
            T _head;
            _union<pack<Ts...>, true> _tail;
        };
    };

    template <typename T, typename ...Ts>
    struct _union<pack<T, Ts...>, false>
    {
        EGGS_CXX11_STATIC_CONSTEXPR std::size_t size = 1 + sizeof...(Ts);

        template <typename ...Args>
        EGGS_CXX11_CONSTEXPR _union(index<0>, Args&&... args)
          : _head(detail::forward<Args>(args)...)
        {}

        template <std::size_t I, typename ...Args>
        EGGS_CXX11_CONSTEXPR _union(index<I>, Args&&... args)
          : _tail(index<I - 1>{}, detail::forward<Args>(args)...)
        {}

        ~_union() {}

        EGGS_CXX14_CONSTEXPR void* target() EGGS_CXX11_NOEXCEPT
        {
            return &_target;
        }

        EGGS_CXX11_CONSTEXPR void const* target() const EGGS_CXX11_NOEXCEPT
        {
            return &_target;
        }

        EGGS_CXX14_CONSTEXPR T& get(index<0>) EGGS_CXX11_NOEXCEPT
        {
            return this->_head;
        }

        EGGS_CXX11_CONSTEXPR T const& get(index<0>) const EGGS_CXX11_NOEXCEPT
        {
            return this->_head;
        }

        template <
            std::size_t I
          , typename U = typename at_index<I, pack<T, Ts...>>::type
        >
        EGGS_CXX14_CONSTEXPR U& get(index<I>) EGGS_CXX11_NOEXCEPT
        {
            return this->_tail.get(index<I - 1>{});
        }

        template <
            std::size_t I
          , typename U = typename at_index<I, pack<T, Ts...>>::type
        >
        EGGS_CXX11_CONSTEXPR U const& get(index<I>) const EGGS_CXX11_NOEXCEPT
        {
            return this->_tail.get(index<I - 1>{});
        }

    private:
        union
        {
            char _target;
            T _head;
            _union<pack<Ts...>, false> _tail;
        };
    };
#else
    ///////////////////////////////////////////////////////////////////////////
    namespace conditionally_deleted
    {
        template <bool CopyCnstr, bool MoveCnstr = CopyCnstr>
        struct cnstr
        {};

#  if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS && EGGS_CXX11_HAS_DELETED_FUNCTIONS
        template <>
        struct cnstr<true, false>
        {
            cnstr() EGGS_CXX11_NOEXCEPT = default;
            cnstr(cnstr const&) EGGS_CXX11_NOEXCEPT = delete;
            cnstr(cnstr&&) EGGS_CXX11_NOEXCEPT = default;
            cnstr& operator=(cnstr const&) EGGS_CXX11_NOEXCEPT = default;
            cnstr& operator=(cnstr&&) EGGS_CXX11_NOEXCEPT = default;
        };

        template <>
        struct cnstr<false, true>
        {
            cnstr() EGGS_CXX11_NOEXCEPT = default;
            cnstr(cnstr const&) EGGS_CXX11_NOEXCEPT = default;
            cnstr(cnstr&&) EGGS_CXX11_NOEXCEPT = delete;
            cnstr& operator=(cnstr const&) EGGS_CXX11_NOEXCEPT = default;
            cnstr& operator=(cnstr&&) EGGS_CXX11_NOEXCEPT = default;
        };

        template <>
        struct cnstr<true, true>
        {
            cnstr() EGGS_CXX11_NOEXCEPT = default;
            cnstr(cnstr const&) EGGS_CXX11_NOEXCEPT = delete;
            cnstr(cnstr&&) EGGS_CXX11_NOEXCEPT = delete;
            cnstr& operator=(cnstr const&) EGGS_CXX11_NOEXCEPT = default;
            cnstr& operator=(cnstr&&) EGGS_CXX11_NOEXCEPT = default;
        };
#  endif

        template <bool CopyAssign, bool MoveAssign = CopyAssign>
        struct assign
        {};

#  if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS && EGGS_CXX11_HAS_DELETED_FUNCTIONS
        template <>
        struct assign<true, false>
        {
            assign() EGGS_CXX11_NOEXCEPT = default;
            assign& operator=(assign const&) EGGS_CXX11_NOEXCEPT = delete;
            assign& operator=(assign&&) EGGS_CXX11_NOEXCEPT = default;
        };

        template <>
        struct assign<false, true>
        {
            assign() EGGS_CXX11_NOEXCEPT = default;
            assign& operator=(assign const&) EGGS_CXX11_NOEXCEPT = default;
            assign& operator=(assign&&) EGGS_CXX11_NOEXCEPT = delete;
        };

        template <>
        struct assign<true, true>
        {
            assign() EGGS_CXX11_NOEXCEPT = default;
            assign& operator=(assign const&) EGGS_CXX11_NOEXCEPT = delete;
            assign& operator=(assign&&) EGGS_CXX11_NOEXCEPT = delete;
        };
#  endif
    }

    template <bool CopyCnstr, bool MoveCnstr = CopyCnstr>
    using conditionally_deleted_cnstr =
        conditionally_deleted::cnstr<CopyCnstr, MoveCnstr>;

        template <bool CopyAssign, bool MoveAssign = CopyAssign>
    using conditionally_deleted_assign =
        conditionally_deleted::assign<CopyAssign, MoveAssign>;

    ///////////////////////////////////////////////////////////////////////////
#  if EGGS_CXX11_STD_HAS_ALIGNED_UNION
    using std::aligned_union;
#  else
    template <std::size_t ...Vs>
    struct _static_max;

    template <std::size_t V0>
    struct _static_max<V0>
      : std::integral_constant<std::size_t, V0>
    {};

    template <std::size_t V0, std::size_t V1, std::size_t ...Vs>
    struct _static_max<V0, V1, Vs...>
      : _static_max<V0 < V1 ? V1 : V0, Vs...>
    {};

    template <std::size_t Len, typename ...Types>
    struct aligned_union
      : std::aligned_storage<
            _static_max<Len, sizeof(Types)...>::value
          , _static_max<std::alignment_of<Types>::value...>::value
        >
    {};
#  endif

    ///////////////////////////////////////////////////////////////////////////
    template <typename ...Ts, bool IsTriviallyDestructible>
    struct _union<pack<Ts...>, IsTriviallyDestructible>
      : conditionally_deleted_cnstr<
            !all_of<pack<std::is_copy_constructible<Ts>...>>::value
          , !all_of<pack<std::is_move_constructible<Ts>...>>::value
        >
      , conditionally_deleted_assign<
            !all_of<pack<std::is_copy_assignable<Ts>...>>::value
          , !all_of<pack<std::is_move_assignable<Ts>...>>::value
        >
    {
        EGGS_CXX11_STATIC_CONSTEXPR std::size_t size = sizeof...(Ts);

        template <
            std::size_t I, typename ...Args
          , typename T = typename at_index<I, pack<Ts...>>::type
        >
        _union(index<I> /*which*/, Args&&... args)
        {
            ::new (target()) T(detail::forward<Args>(args)...);
        }

        void* target() EGGS_CXX11_NOEXCEPT
        {
            return &_buffer;
        }

        void const* target() const EGGS_CXX11_NOEXCEPT
        {
            return &_buffer;
        }

        template <
            std::size_t I
          , typename T = typename at_index<I, pack<Ts...>>::type
        >
        T& get(index<I>) EGGS_CXX11_NOEXCEPT
        {
            return *static_cast<T*>(target());
        }

        template <
            std::size_t I
          , typename T = typename at_index<I, pack<Ts...>>::type
        >
        T const& get(index<I>) const EGGS_CXX11_NOEXCEPT
        {
            return *static_cast<T const*>(target());
        }

        typename aligned_union<0, Ts...>::type _buffer;
    };
#endif

    ///////////////////////////////////////////////////////////////////////////
#if EGGS_CXX11_STD_HAS_IS_TRIVIALLY_COPYABLE && EGGS_CXX11_STD_HAS_IS_TRIVIALLY_DESTRUCTIBLE
    using std::is_trivially_copyable;
#else
    template <typename T>
    struct is_trivially_copyable
      : std::is_pod<T>
    {};
#endif

#if EGGS_CXX11_STD_HAS_IS_TRIVIALLY_DESTRUCTIBLE
    using std::is_trivially_destructible;
#else
    template <typename T>
    struct is_trivially_destructible
      : std::is_pod<T>
    {};
#endif

    ///////////////////////////////////////////////////////////////////////////
    template <typename Ts, bool TriviallyCopyable, bool TriviallyDestructible>
    struct _storage;

    template <typename ...Ts>
    struct _storage<pack<Ts...>, true, true>
      : _union<
            pack<Ts...>
          , all_of<pack<is_trivially_destructible<Ts>...>>::value
        >
    {
        using base_type = _union<
            pack<Ts...>
          , all_of<pack<is_trivially_destructible<Ts>...>>::value
        >;

        EGGS_CXX11_CONSTEXPR _storage() EGGS_CXX11_NOEXCEPT
          : base_type{index<0>{}}
          , _which{0}
        {}

#if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS
        _storage(_storage const& rhs) = default;
        _storage(_storage&& rhs) = default;
#endif

        void _move(_storage& rhs)
        {
            detail::move_construct{}(
                pack<Ts...>{}, rhs._which
              , target(), rhs.target()
            );
            _which = rhs._which;
        }

        template <std::size_t I, typename ...Args>
        EGGS_CXX11_CONSTEXPR _storage(index<I> which, Args&&... args)
          : base_type{which, detail::forward<Args>(args)...}
          , _which{I}
        {}

        template <std::size_t I, typename ...Args>
        EGGS_CXX14_CONSTEXPR void _emplace(
            /*is_copy_assignable<Ts...>=*/std::true_type
          , index<I> which, Args&&... args)
        {
            *this = _storage(which, detail::forward<Args>(args)...);
        }

        template <
            std::size_t I, typename ...Args
          , typename T = typename at_index<I, pack<Ts...>>::type
        >
        void _emplace(
            /*is_copy_assignable<Ts...>=*/std::false_type
          , index<I> /*which*/, Args&&... args)
        {
            ::new (target()) T(detail::forward<Args>(args)...);
            _which = I;
        }

        template <std::size_t I, typename ...Args>
        EGGS_CXX14_CONSTEXPR void emplace(index<I> which, Args&&... args)
        {
            using is_copy_assignable = all_of<pack<std::is_copy_assignable<Ts>...>>;
            _emplace(
                is_copy_assignable{}
              , which, detail::forward<Args>(args)...);
        }

#if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS
        _storage& operator=(_storage const& rhs) = default;
        _storage& operator=(_storage&& rhs) = default;
#endif

        EGGS_CXX14_CONSTEXPR void _swap(
            /*is_copy_assignable<Ts...>=*/std::true_type
          , _storage& rhs)
        {
            _storage tmp(detail::move(*this));
            *this = detail::move(rhs);
            rhs = detail::move(tmp);
        }

        void _swap(
            /*is_copy_assignable<Ts...>=*/std::false_type
          , _storage& rhs)
        {
            if (_which == rhs._which)
            {
                detail::swap{}(
                    pack<Ts...>{}, _which
                  , target(), rhs.target()
                );
            } else {
                _storage tmp(std::move(*this));
                _move(rhs);
                rhs._move(tmp);
            }
        }

        EGGS_CXX14_CONSTEXPR void swap(_storage& rhs)
        {
            _swap(
                all_of<pack<std::is_copy_assignable<Ts>...>>{}
              , rhs);
        }

        EGGS_CXX11_CONSTEXPR std::size_t which() const
        {
            return _which;
        }

        using base_type::target;
        using base_type::get;

    protected:
        std::size_t _which;
    };

    template <typename ...Ts>
    struct _storage<pack<Ts...>, false, true>
      : _storage<pack<Ts...>, true, true>
    {
        using base_type = _storage<pack<Ts...>, true, true>;

#if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS
        _storage() = default;
#else
        EGGS_CXX11_CONSTEXPR _storage() EGGS_CXX11_NOEXCEPT
          : base_type{}
        {}
#endif

        _storage(_storage const& rhs)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(all_of<pack<
                std::is_nothrow_copy_constructible<Ts>...
            >>::value)
#endif
          : base_type{}
        {
            detail::copy_construct{}(
                pack<Ts...>{}, rhs._which
              , target(), rhs.target()
            );
            _which = rhs._which;
        }

        _storage(_storage&& rhs)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(all_of<pack<
                std::is_nothrow_move_constructible<Ts>...
            >>::value)
#endif
          : base_type{}
        {
            detail::move_construct{}(
                pack<Ts...>{}, rhs._which
              , target(), rhs.target()
            );
            _which = rhs._which;
        }

        template <std::size_t I, typename ...Args>
        EGGS_CXX11_CONSTEXPR _storage(index<I> which, Args&&... args)
          : base_type{which, detail::forward<Args>(args)...}
        {}

        void _copy(_storage const& rhs)
        {
            _destroy();
            detail::copy_construct{}(
                pack<Ts...>{}, rhs._which
              , target(), rhs.target()
            );
            _which = rhs._which;
        }

        void _move(_storage& rhs)
        {
            _destroy();
            detail::move_construct{}(
                pack<Ts...>{}, rhs._which
              , target(), rhs.target()
            );
            _which = rhs._which;
        }

        template <
            std::size_t I, typename ...Args
          , typename T = typename at_index<I, pack<Ts...>>::type
        >
        void emplace(index<I> /*which*/, Args&&... args)
        {
            _destroy();
            ::new (target()) T(detail::forward<Args>(args)...);
            _which = I;
        }

        _storage& operator=(_storage const& rhs)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(all_of<pack<
                std::is_nothrow_copy_assignable<Ts>...
              , std::is_nothrow_copy_constructible<Ts>...
            >>::value)
#endif
        {
            if (_which == rhs._which)
            {
                detail::copy_assign{}(
                    pack<Ts...>{}, _which
                  , target(), rhs.target()
                );
            } else {
                _copy(rhs);
            }
            return *this;
        }

        _storage& operator=(_storage&& rhs)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(all_of<pack<
                std::is_nothrow_move_assignable<Ts>...
              , std::is_nothrow_move_constructible<Ts>...
            >>::value)
#endif
        {
            if (_which == rhs._which)
            {
                detail::move_assign{}(
                    pack<Ts...>{}, _which
                  , target(), rhs.target()
                );
            } else {
                _move(rhs);
            }
            return *this;
        }

        void swap(_storage& rhs)
        {
            if (_which == rhs._which)
            {
                detail::swap{}(
                    pack<Ts...>{}, _which
                  , target(), rhs.target()
                );
            } else if (_which == 0) {
                _move(rhs);
                rhs._destroy();
            } else if (rhs._which == 0) {
                rhs._move(*this);
                _destroy();
            } else {
                _storage tmp(std::move(*this));
                _move(rhs);
                rhs._move(tmp);
                tmp._destroy();
            }
        }

        using base_type::which;
        using base_type::target;

    protected:
        void _destroy(
            /*is_trivially_destructible<Ts...>=*/std::true_type)
        {}

        void _destroy(
            /*is_trivially_destructible<Ts...>=*/std::false_type)
        {
            detail::destroy{}(
                pack<Ts...>{}, _which
              , target()
            );
        }

        void _destroy()
        {
            _destroy(all_of<pack<is_trivially_destructible<Ts>...>>{});
            _which = 0;
        }

    protected:
        using base_type::_which;
    };

    template <typename ...Ts>
    struct _storage<pack<Ts...>, false, false>
      : _storage<pack<Ts...>, false, true>
    {
        using base_type = _storage<pack<Ts...>, false, true>;

#if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS
        _storage() = default;
        _storage(_storage const& rhs) = default;
        _storage(_storage&& rhs) = default;
#else
        EGGS_CXX11_CONSTEXPR _storage() EGGS_CXX11_NOEXCEPT
          : base_type{}
        {}

        _storage(_storage const& rhs)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(
                std::is_nothrow_copy_constructible<base_type>::value
            )
#endif
          : base_type{static_cast<base_type const&>(rhs)}
        {}

        _storage(_storage&& rhs)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(
                std::is_nothrow_move_constructible<base_type>::value
            )
#endif
          : base_type{static_cast<base_type&&>(rhs)}
        {}
#endif

        template <std::size_t I, typename ...Args>
        EGGS_CXX11_CONSTEXPR _storage(index<I> which, Args&&... args)
          : base_type{which, detail::forward<Args>(args)...}
        {}

        ~_storage()
        {
            base_type::_destroy();
        }

        using base_type::emplace;

#if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS
        _storage& operator=(_storage const& rhs) = default;
        _storage& operator=(_storage&& rhs) = default;
#else
        _storage& operator=(_storage const& rhs)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(all_of<pack<
                std::is_nothrow_copy_assignable<Ts>...
              , std::is_nothrow_copy_constructible<Ts>...
            >>::value)
#endif
        {
            base_type::operator=(rhs);
            return *this;
        }

        _storage& operator=(_storage&& rhs)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(all_of<pack<
                std::is_nothrow_move_assignable<Ts>...
              , std::is_nothrow_move_constructible<Ts>...
            >>::value)
#endif
        {
            base_type::operator=(detail::move(rhs));
            return *this;
        }
#endif

        using base_type::swap;

        using base_type::which;
        using base_type::target;

    protected:
        using base_type::_which;
    };

    template <typename ...Ts>
    using storage = _storage<
        pack<empty, Ts...>
      , all_of<pack<is_trivially_copyable<Ts>...>>::value
      , all_of<pack<is_trivially_destructible<Ts>...>>::value
    >;

    struct empty_storage
    {
        EGGS_CXX11_STATIC_CONSTEXPR std::size_t size = 1;

        static EGGS_CXX11_CONSTEXPR std::size_t which()
        {
            return 0;
        }
    };
}}}

#include <eggs/variant/detail/config/suffix.hpp>

#endif /*EGGS_VARIANT_DETAIL_STORAGE_HPP*/
