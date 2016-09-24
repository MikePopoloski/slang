//! \file eggs/variant/variant.hpp
// Eggs.Variant
//
// Copyright Agustin K-ballo Berge, Fusion Fenix 2014-2016
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef EGGS_VARIANT_VARIANT_HPP
#define EGGS_VARIANT_VARIANT_HPP

#include <eggs/variant/detail/apply.hpp>
#include <eggs/variant/detail/pack.hpp>
#include <eggs/variant/detail/storage.hpp>
#include <eggs/variant/detail/utility.hpp>
#include <eggs/variant/detail/visitor.hpp>

#include <eggs/variant/bad_variant_access.hpp>
#include <eggs/variant/in_place.hpp>

#include <cstddef>
#include <functional>
#include <initializer_list>
#include <type_traits>
#include <typeinfo>
#include <utility>

#include <eggs/variant/detail/config/prefix.hpp>

namespace eggs { namespace variants
{
    template <typename ...Ts>
    class variant;

    namespace detail
    {
        ///////////////////////////////////////////////////////////////////////
        std::false_type _is_variant(...);

        template <typename ...Ts>
        std::true_type _is_variant(variant<Ts...> const*);

        template <typename T>
        struct is_variant
          : decltype(_is_variant(static_cast<T*>(nullptr)))
        {};

        template <typename ...Ts>
        struct is_variant<variant<Ts...>>
          : std::true_type
        {};

        template <typename ...Ts>
        struct is_variant<variant<Ts...> const>
          : std::true_type
        {};

        ///////////////////////////////////////////////////////////////////////
        namespace _best_match
        {
            template <typename Ts, std::size_t I = 0>
            struct overloads
            {};

            template <typename T, typename ...Ts, std::size_t I>
            struct overloads<pack<T, Ts...>, I>
              : overloads<pack<Ts...>, I + 1>
            {
                using fun_ptr = index<I>(*)(T);
                operator fun_ptr();
            };

            template <typename F, typename T>
            auto _invoke(F&&, T&&)
             -> decltype(std::declval<F>()(std::declval<T>()));

            struct _fallback {};

            _fallback _invoke(...);

            template <
                typename T, typename U
              , typename R = decltype(_best_match::_invoke(
                    std::declval<T>(), std::declval<U>()))
            >
            struct result_of : R
            {};

            template <typename T, typename U>
            struct result_of<T, U, _fallback>
            {};
        }

        template <typename U, typename ...Ts>
        struct index_of_best_match
          : _best_match::result_of<_best_match::overloads<Ts...>, U>
        {};

        ///////////////////////////////////////////////////////////////////////
#if EGGS_CXX17_STD_HAS_SWAPPABLE_TRAITS
        using std::is_swappable;
        using std::is_nothrow_swappable;
#else
        namespace _swap
        {
            template <typename T>
            typename std::enable_if<
                std::is_move_constructible<T>::value
             && std::is_move_assignable<T>::value
            >::type swap(T&, T&)
#  if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
                EGGS_CXX11_NOEXCEPT_IF(
                    std::is_nothrow_move_constructible<T>::value
                 && std::is_nothrow_move_assignable<T>::value)
#  endif
                ;

            struct _fallback {};

            _fallback swap(...);

            template <
                typename T
              , typename R = decltype(swap(
                    std::declval<T>(), std::declval<T>()))
            >
            struct is_swappable : std::true_type
            {};

            template <typename T>
            struct is_swappable<T, _fallback> : std::false_type
            {};

            template <typename T, bool Swappable = is_swappable<T>::value>
            struct is_nothrow_swappable
            {
                EGGS_CXX11_STATIC_CONSTEXPR bool value =
                    EGGS_CXX11_NOEXCEPT_EXPR(
                        swap(std::declval<T&>(), std::declval<T&>()));
            };

            template <typename T>
            struct is_nothrow_swappable<T, false>
            {
                EGGS_CXX11_STATIC_CONSTEXPR bool value = false;
            };
        }

        template <typename T>
        struct is_swappable
          : std::integral_constant<
                bool
              , _swap::is_swappable<T>::value
            >
        {};

        template <typename T>
        struct is_nothrow_swappable
          : std::integral_constant<
                bool
              , _swap::is_nothrow_swappable<T>::value
            >
        {};
#endif

        ///////////////////////////////////////////////////////////////////////
        struct access
        {
            template <typename ...Ts, typename Storage = detail::storage<Ts...>>
            EGGS_CXX14_CONSTEXPR static Storage& storage(
                variant<Ts...>& v) EGGS_CXX11_NOEXCEPT
            {
                return v._storage;
            }

            EGGS_CXX14_CONSTEXPR static detail::empty_storage storage(
                variant<>& /*v*/) EGGS_CXX11_NOEXCEPT
            {
                return detail::empty_storage();
            }

            template <typename ...Ts, typename Storage = detail::storage<Ts...>>
            EGGS_CXX11_CONSTEXPR static Storage const& storage(
                variant<Ts...> const& v) EGGS_CXX11_NOEXCEPT
            {
                return v._storage;
            }

            EGGS_CXX11_CONSTEXPR static detail::empty_storage storage(
                variant<> const& /*v*/) EGGS_CXX11_NOEXCEPT
            {
                return detail::empty_storage();
            }

            template <typename ...Ts, typename Storage = detail::storage<Ts...>>
            EGGS_CXX14_CONSTEXPR static Storage&& storage(
                variant<Ts...>&& v) EGGS_CXX11_NOEXCEPT
            {
                return detail::move(v._storage);
            }

            EGGS_CXX14_CONSTEXPR static detail::empty_storage storage(
                variant<>&& /*v*/) EGGS_CXX11_NOEXCEPT
            {
                return detail::empty_storage();
            }

            template <
                typename ...Ts, size_t I
              , typename T = typename at_index<I, pack<Ts...>>::type
            >
            EGGS_CXX14_CONSTEXPR static T& get(
                variant<Ts...>& v, index<I>) EGGS_CXX11_NOEXCEPT
            {
                return v._storage.get(index<I + 1>{});
            }

            template <
                typename ...Ts, size_t I
              , typename T = typename at_index<I, pack<Ts...>>::type
            >
            EGGS_CXX11_CONSTEXPR static T const& get(
                variant<Ts...> const& v, index<I>) EGGS_CXX11_NOEXCEPT
            {
                return v._storage.get(index<I + 1>{});
            }
        };

        ///////////////////////////////////////////////////////////////////////
        struct hash
        {
            using result_type = std::size_t;

            template <typename T>
            std::size_t operator()(T const& v) const
            {
                return std::hash<T>{}(v);
            }
        };
    }

    ///////////////////////////////////////////////////////////////////////////
    //! template <class ...Ts> class variant;
    //!
    //! In a `variant`, at most one of the members can be active at any time,
    //! that is, the value of at most one of the members can be stored in a
    //! `variant` at any time.  Implementations are not permitted to use
    //! additional storage, such as dynamic memory, to allocate its contained
    //! value. The contained value shall be allocated in a region of the
    //! `variant<Ts...>` storage suitably aligned for the types `Ts...`.
    //!
    //! All `T` in `Ts...` shall be object types and shall satisfy the
    //! requirements of `Destructible`.
    template <typename ...Ts>
    class variant
    {
        static_assert(
            !detail::any_of<detail::pack<
                std::is_function<Ts>...>>::value
          , "variant member has function type");

        static_assert(
            !detail::any_of<detail::pack<
                std::is_reference<Ts>...>>::value
          , "variant member has reference type");

        static_assert(
            !detail::any_of<detail::pack<
                std::is_void<Ts>...>>::value
          , "variant member has void type");

    public:
        //! static constexpr std::size_t npos = std::size_t(-1);
        EGGS_CXX11_STATIC_CONSTEXPR std::size_t npos = std::size_t(-1);

    public:
        //! constexpr variant() noexcept;
        //!
        //! \postconditions `*this` does not have an active member.
        //!
        //! \remarks No member is initialized. For every object types `Ts...`
        //!  this constructor shall be a `constexpr` constructor.
        EGGS_CXX11_CONSTEXPR variant() EGGS_CXX11_NOEXCEPT
          : _storage{}
        {}

        //! constexpr variant(variant const& rhs);
        //!
        //! \requires `std::is_copy_constructible_v<T>` is `true` for all `T`
        //!  in `Ts...`.
        //!
        //! \effects If `rhs` has an active member of type `T`, initializes
        //!  the active member as if direct-non-list-initializing an object of
        //!  type `T` with the expression `*rhs.target<T>()`; otherwise, no
        //!  member is initialized.
        //!
        //! \postconditions `rhs.which() == this->which()`.
        //!
        //! \throws Any exception thrown by the selected constructor of `T`.
        //!
        //! \remarks If `std::is_trivially_copyable_v<T>` is `true` for all
        //!  `T` in `Ts...`, then this copy constructor shall be a trivial
        //!  `constexpr` constructor.
#if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS
        variant(variant const& rhs) = default;
#endif

        //! constexpr variant(variant&& rhs) noexcept(see below);
        //!
        //! \requires `std::is_move_constructible_v<T>` is `true` for all `T`
        //!  in `Ts...`.
        //!
        //! \effects If `rhs` has an active member of type `T`, initializes
        //!  the active member as if direct-non-list-initializing an object of
        //!  type `T` with the expression `std::move(*rhs.target<T>())`;
        //!  otherwise, no member is initialized. `bool(rhs)` is unchanged.
        //!
        //! \postconditions `rhs.which() == this->which()`.
        //!
        //! \throws Any exception thrown by the selected constructor of `T`.
        //!
        //! \remarks The expression inside `noexcept` is equivalent to the
        //!  logical AND of `std::is_nothrow_move_constructible_v<Ts>...`. If
        //!  `std::is_trivially_copyable_v<T>` is `true` for all `T` in
        //!  `Ts...`, then this move constructor shall be a trivial
        //!  `constexpr` constructor.
#if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS
        variant(variant&& rhs) = default;
#endif

        //! template <class U>
        //! constexpr variant(U&& v);
        //!
        //! Let `T` be one of the types in `Ts...` for which `U&&` is
        //!  unambiguously convertible to by overload resolution rules.
        //!
        //! \requires `std::is_constructible_v<T, U&&>` is `true`.
        //!
        //! \effects Initializes the active member as if direct-non-list-
        //!  initializing an object of type `T` with the expression
        //!  `std::forward<U>(v)`.
        //!
        //! \postconditions `*this` has an active member.
        //!
        //! \throws Any exception thrown by the selected constructor of `T`.
        //!
        //! \remarks This constructor shall not participate in overload
        //!  resolution unless `std::is_same_v<std::decay_t<U>, variant>` is
        //!  `false`, and there is a type `T` in `Ts...` for which `U&&` is
        //!  unambiguously convertible to by overload resolution rules. If
        //!  `T`'s selected constructor is a `constexpr` constructor, this
        //!  constructor shall be a `constexpr` constructor.
        template <
            typename U
          , typename Enable = typename std::enable_if<!std::is_same<
                typename std::decay<U>::type, variant
            >::value>::type
          , std::size_t I = detail::index_of_best_match<
                U&&, detail::pack<Ts...>>::value
          , typename T = typename detail::at_index<
                I, detail::pack<Ts...>>::type
        >
        EGGS_CXX11_CONSTEXPR variant(U&& v)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(
                std::is_nothrow_constructible<T, U&&>::value)
#endif
          : _storage{detail::index<I + 1>{}, detail::forward<U>(v)}
        {}

        //! template <std::size_t I, class ...Args>
        //! constexpr explicit variant(in_place_index_t<I>, Args&&... args);
        //!
        //! Let `T` be the `I`th element in `Ts...`, where indexing is
        //! zero-based.
        //!
        //! \requires `I < sizeof...(Ts)` and `std::is_constructible_v<T,
        //!  Args&&...>` is `true`.
        //!
        //! \effects Initializes the active member as if direct-non-list-
        //!  initializing an object of type `T` with the arguments
        //!  `std::forward<Args>(args)...`.
        //!
        //! \postconditions `*this` has an active member of type `T`.
        //!
        //! \throws Any exception thrown by the selected constructor of `T`.
        //!
        //! \remarks If `T`'s selected constructor is a `constexpr`
        //!  constructor, this constructor shall be a `constexpr` constructor.
        template <
            std::size_t I, typename ...Args
          , typename T = typename detail::at_index<
                I, detail::pack<Ts...>>::type
        >
        EGGS_CXX11_CONSTEXPR explicit variant(
            in_place_index_t<I>, Args&&... args)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(
                std::is_nothrow_constructible<T, Args&&...>::value)
#endif
          : _storage{detail::index<I + 1>{}, detail::forward<Args>(args)...}
        {}

#if EGGS_CXX11_HAS_INITIALIZER_LIST_OVERLOADING
        //! template <std::size_t I, class U, class ...Args>
        //! constexpr explicit variant(in_place_index_t<I>, std::initializer_list<U> il, Args&&... args);
        //!
        //! Let `T` be the `I`th element in `Ts...`, where indexing is
        //! zero-based.
        //!
        //! \requires `I < sizeof...(Ts)` and  `std::is_constructible_v<T,
        //!  initializer_list<U>&, Args&&...>` is `true`.
        //!
        //! \effects Initializes the active member as if direct-non-list-
        //!  initializing an object of type `T` with the arguments `il,
        //!  std::forward<Args>(args)...`.
        //!
        //! \postconditions `*this` has an active member of type `T`.
        //!
        //! \throws Any exception thrown by the selected constructor of `T`.
        //!
        //! \remarks This constructor shall not participate in overload
        //!  resolution unless `std::is_constructible_v<T, std::initializer_list<U>&,
        //!  Args&&...>` is `true`. If `T`'s selected constructor is a
        //!  `constexpr` constructor, this constructor shall be a `constexpr`
        //!  constructor.
        template <
            std::size_t I, typename U, typename ...Args
          , typename T = typename detail::at_index<
                I, detail::pack<Ts...>>::type
          , typename Enable = typename std::enable_if<std::is_constructible<
                T, std::initializer_list<U>&, Args&&...
            >::value>::type
        >
        EGGS_CXX11_CONSTEXPR explicit variant(
            in_place_index_t<I>, std::initializer_list<U> il, Args&&... args)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(std::is_nothrow_constructible<
                T, std::initializer_list<U>&, Args&&...
            >::value)
#endif
          : _storage{detail::index<I + 1>{}, il, detail::forward<Args>(args)...}
        {}
#endif

        //! template <class T, class ...Args>
        //! constexpr explicit variant(in_place_type_t<T>, Args&&... args);
        //!
        //! \requires `T` shall occur exactly once in `Ts...`.
        //!
        //! \effects Equivalent to `variant(in_place<I>,
        //!  std::forward<Args>(args)...)` where `I` is the zero-based index
        //!  of `T` in `Ts...`.
        //!
        //! \remarks If `T`'s selected constructor is a `constexpr`
        //!  constructor, this constructor shall be a `constexpr` constructor.
        template <typename T, typename ...Args>
        EGGS_CXX11_CONSTEXPR explicit variant(
            in_place_type_t<T>, Args&&... args)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(
                std::is_nothrow_constructible<T, Args&&...>::value)
#endif
          : _storage{detail::index_of<T, detail::pack<
                    detail::empty, typename std::remove_cv<Ts>::type...
                >>{}, detail::forward<Args>(args)...}
        {}

#if EGGS_CXX11_HAS_INITIALIZER_LIST_OVERLOADING
        //! template <class T, class U, class ...Args>
        //! constexpr explicit variant(in_place_type_t<T>, std::initializer_list<U> il, Args&&... args);
        //!
        //! \requires `T` shall occur exactly once in `Ts...`.
        //!
        //! \effects Equivalent to `variant(in_place<I>, il,
        //!  std::forward<Args>(args)...)` where `I` is the zero-based index
        //!  of `T` in `Ts...`.
        //!
        //! \remarks This constructor shall not participate in overload
        //!  resolution unless `std::is_constructible_v<T, std::initializer_list<U>&,
        //!  Args&&...>` is `true`. If `T`'s selected constructor is a
        //!  `constexpr` constructor, this constructor shall be a `constexpr`
        //!  constructor.
        template <
            typename T, typename U, typename ...Args
          , typename Enable = typename std::enable_if<std::is_constructible<
                T, std::initializer_list<U>&, Args&&...
            >::value>::type
        >
        EGGS_CXX11_CONSTEXPR explicit variant(
            in_place_type_t<T>, std::initializer_list<U> il, Args&&... args)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(std::is_nothrow_constructible<
                T, std::initializer_list<U>&, Args&&...
            >::value)
#endif
          : _storage{detail::index_of<T, detail::pack<
                    detail::empty, typename std::remove_cv<Ts>::type...
                >>{}, il, detail::forward<Args>(args)...}
        {}
#endif

        //! ~variant();
        //!
        //! \effects If `*this` has an active member of type `T`, destroys the
        //!  active member as if by calling `target<T>()->~T()`.
        //!
        //! \remarks If `std::is_trivially_destructible_v<T>` is `true` for all
        //!  `T` in `Ts...`, then this destructor shall be trivial.
#if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS
        ~variant() = default;
#endif

        //! constexpr variant& operator=(variant const& rhs);
        //!
        //! \requires `std::is_copy_constructible_v<T>` and
        //!  `std::is_copy_assignable_v<T>` is `true` for all `T` in `Ts...`.
        //!
        //! \effects
        //!  - If both `*this` and `rhs` have an active member of type `T`,
        //!    assigns to the active member the expression `*rhs.target<T>()`;
        //!
        //!  - otherwise, if `*this` has an active member of type `U`, destroys
        //!    the active member by calling `target<U>()->~U()`. Then, if `rhs`
        //!    has an active member of type `T`, initializes the active member
        //!    as if direct-non-list-initializing an object of type `T` with
        //!    the expression `*rhs.target<T>()`.
        //!
        //! \returns `*this`.
        //!
        //! \postconditions `rhs.which() == this->which()`.
        //!
        //! \remarks If an exception is thrown during the call to `T`'s copy
        //!  assignment, the state of the active member is as defined by the
        //!  exception safety guarantee of `T`'s copy assignment. If an
        //!  exception is thrown during the call to `T`'s copy constructor,
        //!  `*this` has no active member, and the previous active member (if
        //!  any) has been destroyed. If `std::is_trivially_copyable_v<T>` is
        //!  `true` for all `T` in `Ts...`, then this copy assignment operator
        //!  shall be a trivial `constexpr` assignment operator.
#if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS
        variant& operator=(variant const& rhs) = default;
#endif

        //! constexpr variant& operator=(variant&& rhs) noexcept(see below);
        //!
        //! \requires `std::is_move_constructible_v<T>` and
        //!  `std::is_move_assignable_v<T>` is `true` for all `T` in `Ts...`.
        //!
        //! \effects
        //!  - If both `*this` and `rhs` have an active member of type `T`,
        //!    assigns to the active member the expression
        //!    `std::move(*rhs.target<T>())`;
        //!
        //!  - otherwise, if `*this` has an active member of type `U`, destroys
        //!    the active member by calling `target<U>()->~U()`. Then, if `rhs`
        //!    has an active member of type `T`, initializes the active member
        //!    as if direct-non-list-initializing an object of type `T` with
        //!    the expression `std::move(*rhs.target<T>())`.
        //!
        //!  `bool(rhs)` is unchanged.
        //!
        //! \returns `*this`.
        //!
        //! \postconditions `rhs.which() == this->which()`.
        //!
        //! \remarks If an exception is thrown during the call to `T`'s move
        //!  assignment, the state of both active members is determined by the
        //!  exception safety guarantee of `T`'s move assignment. If an
        //!  exception is thrown during the call to `T`'s move constructor,
        //!  `*this` has no active member, the previous active member (if any)
        //!  has been destroyed, and the state of the active member of `rhs`
        //!  is determined by the exception safety guarantee of `T`'s move
        //!  constructor. The expression inside `noexcept` is equivalent to
        //!  the logical AND of `std::is_nothrow_move_assignable_v<Ts>...` and
        //!  `std::is_nothrow_move_constructible_v<Ts>...`. If
        //!  `std::is_trivially_copyable_v<T>` is `true` for all `T` in
        //!  `Ts...`, then this move assignment operator shall be a trivial
        //!  `constexpr` assignment operator.
#if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS
        variant& operator=(variant&& rhs) = default;
#endif

        //! template <class U>
        //! constexpr variant& operator=(U&& v);
        //!
        //! Let `T` be one of the types in `Ts...` for which `U&&` is
        //!  unambiguously convertible to by overload resolution rules.
        //!
        //! \requires `std::is_constructible_v<T, U&&>` and
        //!  `std::is_assignable_v<T, U&&>` are `true`.
        //!
        //! \effects
        //!  - If `*this` has an active member of type `T`, assigns to the
        //!    active member the expression `std::forward<U>(v)`;
        //!
        //!  - otherwise, calls `*this = {}`. Then, initializes the active
        //!    member as if direct-non-list-initializing an object of
        //!    type `T` with the expression `std::forward<U>(v)`.
        //!
        //! \returns `*this`.
        //!
        //! \postconditions `*this` has an active member.
        //!
        //! \remarks If an exception is thrown during the call to `T`'s
        //!  assignment, the state of the active member is as defined by the
        //!  exception safety guarantee of `T`'s copy assignment. If an
        //!  exception is thrown during the call to `T`'s constructor, `*this`
        //!  has no active member, and the previous active member (if any) has
        //!  been destroyed. This operator shall not participate in overload
        //!  resolution unless `std::is_same_v<std::decay_t<U>, variant>` is
        //!  `false`, and there is a type `T` in `Ts...` for which `U&&`
        //!  is unambiguously convertible to by overload resolution rules. If
        //!  `std::is_trivially_copyable_v<T>` is `true` for all `T` in
        //!  `Ts...` and `T`'s selected constructor is a `constexpr`
        //!  constructor, then this function shall be a `constexpr` function.
        template <
            typename U
          , typename Enable = typename std::enable_if<!std::is_same<
                typename std::decay<U>::type, variant
            >::value>::type
          , std::size_t I = detail::index_of_best_match<
                U&&, detail::pack<Ts...>>::value
          , typename T = typename detail::at_index<
                I, detail::pack<Ts...>>::type
        >
        EGGS_CXX14_CONSTEXPR variant& operator=(U&& v)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(std::is_nothrow_assignable<T, U&&>::value
                  && std::is_nothrow_constructible<T, U&&>::value)
#endif
        {
            if (_storage.which() == I + 1)
            {
                _storage.get(detail::index<I + 1>{}) = detail::forward<U>(v);
            } else {
                _storage.emplace(detail::index<I + 1>{}, detail::forward<U>(v));
            }
            return *this;
        }

        //! template <std::size_t I, class ...Args>
        //! constexpr void emplace(Args&&... args);
        //!
        //! Let `T` be the `I`th element in `Ts...`, where indexing is
        //! zero-based.
        //!
        //! \requires `I < sizeof...(Ts)` and `std::is_constructible_v<T,
        //!  Args&&...>` is `true`.
        //!
        //! \effects Calls `*this = {}`. Then, initializes the active member
        //!  as if direct-non-list-initializing  an object of type `T` with
        //!  the arguments `std::forward<Args>(args)...`.
        //!
        //! \postconditions `*this` has an active member of type `T`.
        //!
        //! \throws Any exception thrown by the selected constructor of `T`.
        //!
        //! \remarks If an exception is thrown during the call to `T`'s
        //!  constructor, `*this` has no active member, and the previous
        //!  active member (if any) has been destroyed. If
        //!  `std::is_trivially_copyable_v<T> && std::is_copy_assignable_v<T>`
        //!  is `true` for all `T` in `Ts...` and `T`'s selected constructor
        //!  is a `constexpr` constructor, then this function shall be a
        //!  `constexpr` function.
        template <
            std::size_t I, typename ...Args
          , typename T = typename detail::at_index<
                I, detail::pack<Ts...>>::type
        >
        EGGS_CXX14_CONSTEXPR void emplace(Args&&... args)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(
                std::is_nothrow_constructible<T, Args&&...>::value)
#endif
        {
            using t_which = detail::index<I + 1>;

            _storage.emplace(t_which{}, detail::forward<Args>(args)...);
        }

#if EGGS_CXX11_HAS_INITIALIZER_LIST_OVERLOADING
        //! template <std::size_t I, class U, class ...Args>
        //! constexpr void emplace(std::initializer_list<U> il, Args&&... args);
        //!
        //! Let `T` be the `I`th element in `Ts...`, where indexing is
        //! zero-based.
        //!
        //! \requires `I < sizeof...(Ts)` and  `std::is_constructible_v<T,
        //!  initializer_list<U>&, Args&&...>` is `true`.
        //!
        //! \effects Calls `*this = {}`. Then, initializes the active member
        //!  as if direct-non-list-initializing an object of type `T` with
        //!  the arguments `il, std::forward<Args>(args)...`.
        //!
        //! \postconditions `*this` has an active member of type `T`.
        //!
        //! \throws Any exception thrown by the selected constructor of `T`.
        //!
        //! \remarks If an exception is thrown during the call to `T`'s
        //!  constructor, `*this` has no active member, and the previous
        //!  active member (if any) has been destroyed. This function shall
        //!  not participate in overload resolution unless
        //!  `std::is_constructible_v<T, std::initializer_list<U>&, Args&&...>`
        //!  is `true`. If `std::is_trivially_copyable_v<T> &&
        //!  std::is_copy_assignable_v<T>` is `true` for all `T` in `Ts...`
        //!  and `T`'s selected constructor is a `constexpr` constructor, then
        //!  this function shall be a `constexpr` function.
        template <
            std::size_t I, typename U, typename ...Args
          , typename T = typename detail::at_index<
                I, detail::pack<Ts...>>::type
          , typename Enable = typename std::enable_if<std::is_constructible<
                T, std::initializer_list<U>&, Args&&...
            >::value>::type
        >
        EGGS_CXX14_CONSTEXPR void emplace(std::initializer_list<U> il, Args&&... args)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(std::is_nothrow_constructible<
                T, std::initializer_list<U>&, Args&&...
            >::value)
#endif
        {
            using t_which = detail::index<I + 1>;

            _storage.emplace(t_which{}, il, detail::forward<Args>(args)...);
        }
#endif

#if EGGS_CXX11_HAS_TEMPLATE_ARGUMENT_OVERLOADING
        //! template <class T, class ...Args>
        //! constexpr void emplace(Args&&... args);
        //!
        //! \requires `T` shall occur exactly once in `Ts...`.
        //!
        //! \effects Equivalent to `emplace<I>(std::forward<Args>(args)...)`
        //!  where `I` is the zero-based index of `T` in `Ts...`.
        //!
        //! \remarks If `std::is_trivially_copyable_v<T> &&
        //!  std::is_copy_assignable_v<T>` is `true` for all `T` in `Ts...`
        //!  and `T`'s selected constructor is a `constexpr` constructor, then
        //!  this function shall be a `constexpr` function.
        template <typename T, typename ...Args>
        EGGS_CXX14_CONSTEXPR void emplace(Args&&... args)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(
                std::is_nothrow_constructible<T, Args&&...>::value)
#endif
        {
            using t_which = detail::index_of<T, detail::pack<
                detail::empty, Ts...>>;

            _storage.emplace(t_which{}, detail::forward<Args>(args)...);
        }

#if EGGS_CXX11_HAS_INITIALIZER_LIST_OVERLOADING
        //! template <class T, class U, class ...Args>
        //! constexpr void emplace(std::initializer_list<U> il, Args&&... args);
        //!
        //! \requires `T` shall occur exactly once in `Ts...`.
        //!
        //! \effects Equivalent to `emplace<I>(il, std::forward<Args>(args)...)`
        //!  where `I` is the zero-based index of `T` in `Ts...`.
        //!
        //! \remarks This function shall not participate in overload resolution
        //!  unless `std::is_constructible_v<T, std::initializer_list<U>&,
        //!  Args&&...>` is `true`. If `std::is_trivially_copyable_v<T> &&
        //!  std::is_copy_assignable_v<T>` is `true` for all `T` in `Ts...` and
        //!  `T`'s selected constructor is a `constexpr` constructor, then this
        //!  function shall be a `constexpr` function.
        template <
            typename T, typename U, typename ...Args
          , typename Enable = typename std::enable_if<std::is_constructible<
                T, std::initializer_list<U>&, Args&&...
            >::value>::type
        >
        EGGS_CXX14_CONSTEXPR void emplace(std::initializer_list<U> il, Args&&... args)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(std::is_nothrow_constructible<
                T, std::initializer_list<U>&, Args&&...
            >::value)
#endif
        {
            using t_which = detail::index_of<T, detail::pack<
                detail::empty, Ts...>>;

            _storage.emplace(t_which{}, il, detail::forward<Args>(args)...);
        }
#endif
#endif

        //! constexpr void swap(variant& rhs) noexcept(see below);
        //!
        //! \requires Lvalues of `T` shall be swappable and
        //!  `std::is_move_constructible_v<T>` is `true` for all `T` in
        //!  `Ts...`.
        //!
        //! \effects
        //!  - If both `*this` and `rhs` have an active member of type `T`,
        //!    calls `swap(*this->target<T>(), *rhs.target<T>())`;
        //!
        //!  - otherwise, calls `std::swap(*this, rhs)`.
        //!
        //! \remarks If an exception is thrown during the call to function
        //!  `swap` the state of the active members of type `T` is determined
        //!  by the exception safety guarantee of `swap` for lvalues of `T`.
        //!  If an exception is thrown during the call to a move constructor,
        //!  the state of `*this` and `rhs` is unspecified. The expression
        //!  inside `noexcept` is equivalent to the logical AND of
        //!  `std::is_nothrow_move_constructible_v<T> &&
        //!  std::is_nothrow_swappable_v<T>` for all `T` in `Ts...`. If
        //!  `std::is_trivially_copyable_v<T> && std::is_copy_assignable_v<T>`
        //!  is  `true` for all `T` in `Ts...`, then this function shall be a
        //!  `constexpr` function.
        EGGS_CXX14_CONSTEXPR void swap(variant& rhs)
#if EGGS_CXX11_STD_HAS_IS_NOTHROW_TRAITS
            EGGS_CXX11_NOEXCEPT_IF(detail::all_of<detail::pack<
                detail::is_nothrow_swappable<Ts>...
              , std::is_nothrow_move_constructible<Ts>...
            >>::value)
#endif
        {
            _storage.swap(rhs._storage);
        }

        //! constexpr explicit operator bool() const noexcept;
        //!
        //! \returns `true` if and only if `*this` has an active member.
        //!
        //! \remarks This function shall be a `constexpr` function.
        EGGS_CXX11_CONSTEXPR explicit operator bool() const EGGS_CXX11_NOEXCEPT
        {
            return _storage.which() != 0;
        }

        //! constexpr std::size_t which() const noexcept;
        //!
        //! \returns The zero-based index of the active member if `*this` has
        //!  one. Otherwise, returns `npos`.
        //!
        //! \remarks This function shall be a `constexpr` function.
        EGGS_CXX11_CONSTEXPR std::size_t which() const EGGS_CXX11_NOEXCEPT
        {
            return _storage.which() != 0 ? _storage.which() - 1 : npos;
        }

#if EGGS_CXX98_HAS_RTTI
        //! constexpr std::type_info const& target_type() const noexcept;
        //!
        //! \returns If `*this` has an active member of type `T`, `typeid(T)`;
        //!  otherwise `typeid(void)`.
        //!
        //! \remarks This function shall be a `constexpr` function.
        EGGS_CXX11_CONSTEXPR std::type_info const& target_type() const EGGS_CXX11_NOEXCEPT
        {
            return _storage.which() != 0
              ? detail::type_id{}(
                    detail::pack<Ts...>{}, _storage.which() - 1
                )
              : typeid(void);
        }
#endif

        //! constexpr void* target() noexcept;
        //!
        //! \returns If `*this` has an active member, a pointer to the active
        //!  member; otherwise a null pointer.
        //!
        //! \remarks This function shall be a `constexpr` function.
        EGGS_CXX14_CONSTEXPR void* target() EGGS_CXX11_NOEXCEPT
        {
            return _storage.which() != 0 ? _storage.target() : nullptr;
        }

        //! constexpr void const* target() const noexcept;
        //!
        //! \returns If `*this` has an active member, a pointer to the active
        //!  member; otherwise a null pointer.
        //!
        //! \remarks This function shall be a `constexpr` function.
        EGGS_CXX11_CONSTEXPR void const* target() const EGGS_CXX11_NOEXCEPT
        {
            return _storage.which() != 0 ? _storage.target() : nullptr;
        }

        //! template <class T>
        //! constexpr T* target() noexcept;
        //!
        //! \returns If `*this` has an active member of type `T`, a pointer to
        //!  the active member; otherwise a null pointer.
        //!
        //! \remarks Unless `T` is a user-defined type with overloaded unary
        //!  `operator&`, this function shall be a `constexpr` function.
        template <typename T>
        EGGS_CXX14_CONSTEXPR T* target() EGGS_CXX11_NOEXCEPT
        {
            return _storage.which() != 0
              ? detail::target<T, detail::storage<Ts...>>{}(
                    detail::typed_index_pack<detail::pack<detail::empty, Ts...>>{}
                  , _storage.which(), _storage
                )
              : nullptr;
        }

        //! template <class T>
        //! constexpr T const* target() const noexcept;
        //!
        //! \returns If `*this` has an active member of type `T`, a pointer to
        //!  the active member; otherwise a null pointer.
        //!
        //! \remarks Unless `T` is a user-defined type with overloaded unary
        //!  `operator&`, this function shall be a `constexpr` function.
        template <typename T>
        EGGS_CXX11_CONSTEXPR T const* target() const EGGS_CXX11_NOEXCEPT
        {
            return _storage.which() != 0
              ? detail::target<T, detail::storage<Ts...> const>{}(
                    detail::typed_index_pack<detail::pack<detail::empty, Ts...>>{}
                  , _storage.which(), _storage
                )
              : nullptr;
        }

    private:
        friend struct detail::access;
        detail::storage<Ts...> _storage;
    };

    template <>
    class variant<>
    {
    public:
        EGGS_CXX11_STATIC_CONSTEXPR std::size_t npos = std::size_t(-1);

    public:
        EGGS_CXX11_CONSTEXPR variant() EGGS_CXX11_NOEXCEPT {}
#if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS
        variant(variant const&) = default;
        variant(variant&&) = default;
#endif

#if EGGS_CXX11_HAS_DEFAULTED_FUNCTIONS
        variant& operator=(variant const&) = default;
        variant& operator=(variant&&) = default;
#endif

        EGGS_CXX14_CONSTEXPR void swap(variant&) EGGS_CXX11_NOEXCEPT {}

        EGGS_CXX11_CONSTEXPR explicit operator bool() const EGGS_CXX11_NOEXCEPT { return false; }
        EGGS_CXX11_CONSTEXPR std::size_t which() const EGGS_CXX11_NOEXCEPT { return npos; }
#if EGGS_CXX98_HAS_RTTI
        EGGS_CXX11_CONSTEXPR std::type_info const& target_type() const EGGS_CXX11_NOEXCEPT { return typeid(void); }
#endif
        EGGS_CXX14_CONSTEXPR void* target() EGGS_CXX11_NOEXCEPT { return nullptr; }
        EGGS_CXX11_CONSTEXPR void const* target() const EGGS_CXX11_NOEXCEPT { return nullptr; }
    };

    ///////////////////////////////////////////////////////////////////////////
    //! template <class T>
    //! struct variant_size;
    //!
    //! \remarks All specializations of `variant_size<T>` shall meet the
    //!  `UnaryTypeTrait` requirements with a `BaseCharacteristic` of
    //!  `std::integral_constant<std::size_t, N>` for some `N` if `T` is a
    //!  variant-like type; otherwise it shall be empty.
    template <typename T>
    struct variant_size
    {};

    //! template <class ...Ts>
    //! struct variant_size<variant<Ts...>>;
    //!
    //! \remarks Has a `BaseCharacteristic` of `std::integral_constant<
    //!  std::size_t, sizeof...(Ts)>`.
    template <typename ...Ts>
    struct variant_size<variant<Ts...>>
      : std::integral_constant<std::size_t, sizeof...(Ts)>
    {};

    //! template <class T>
    //! struct variant_size<T const>;
    //!
    //! \remarks Let `VS` denote `variant_size<T>` of the cv-unqualified type
    //!  `T`. Has a `BaseCharacteristic` of `std::integral_constant<
    //!  std::size_t, VS::value>` if `T` is a variant-like type; otherwise
    //!  it is empty.
    template <typename T>
    struct variant_size<T const>
      : variant_size<T>
    {};

#if EGGS_CXX14_HAS_VARIABLE_TEMPLATES
    //! template <class T>
    //! constexpr std::size_t variant_size_v = variant_size<T>::value;
    template <typename T>
    EGGS_CXX11_CONSTEXPR std::size_t variant_size_v = variant_size<T>::value;
#endif

    //! template <std::size_t I, class T>
    //! struct variant_element; // undefined
    //!
    //! \remarks All specializations of `variant_element<I, T>` shall meet the
    //!  `TransformationTrait` requirements with a member typedef `type` that
    //!  names the `I`th member of `T`, where indexing is zero-based.
    template <std::size_t I, typename T>
    struct variant_element; // undefined

    //! template <std::size_t I, class ...Ts>
    //! struct variant_element<I, variant<Ts...>>;
    //!
    //! \requires `I < sizeof...(Ts)`.
    //!
    //! \remarks The member typedef `type` shall name the type of the `I`th
    //!  element of `Ts...`, where indexing is zero-based.
    template <std::size_t I, typename ...Ts>
    struct variant_element<I, variant<Ts...>>
      : detail::at_index<I, detail::pack<Ts...>>
    {};

    //! template <std::size_t I, class T>
    //! struct variant_element<I, T const>;
    //!
    //! \remarks Let `VE` denote `variant_element<I, T>` of the cv-unqualified
    //!  type `T`. The member typedef `type` names `std::add_const_t<
    //!  typename VE::type>`.
    template <std::size_t I, typename T>
    struct variant_element<I, T const>
      : std::add_const<typename variant_element<I, T>::type>
    {};

    //! template <std::size_t I, class T>
    //! using variant_element_t = class variant_element<I, T>::type;
    template <std::size_t I, typename T>
    using variant_element_t = typename variant_element<I, T>::type;

    ///////////////////////////////////////////////////////////////////////////
    //! template <std::size_t I, class ...Ts>
    //! constexpr variant_element_t<I, variant<Ts...>>& get(variant<Ts...>& v);
    //!
    //! \requires `I < sizeof...(Ts)`.
    //!
    //! \returns A reference to the `I`th member of `v` if it is active, where
    //!  indexing is zero-based.
    //!
    //! \throws `bad_variant_access` if the `I`th member of `v` is not active.
    //!
    //! \remarks This function shall be a `constexpr` function.
    template <
        std::size_t I, typename ...Ts
      , typename T = typename variant_element<I, variant<Ts...>>::type
    >
    EGGS_CXX14_CONSTEXPR T& get(variant<Ts...>& v)
    {
        return v.which() == I
          ? detail::access::get(v, detail::index<I>{})
          : detail::throw_bad_variant_access<T&>();
    }

    //! template <std::size_t I, class ...Ts>
    //! constexpr variant_element_t<I, variant<Ts...>> const& get(variant<Ts...> const& v);
    //!
    //! \requires `I < sizeof...(Ts)`.
    //!
    //! \returns A const reference to the `I`th member of `v` if it is active,
    //!  where indexing is zero-based.
    //!
    //! \throws `bad_variant_access` if the `I`th member of `v` is not active.
    //!
    //! \remarks This function shall be a `constexpr` function.
    template <
        std::size_t I, typename ...Ts
      , typename T = typename variant_element<I, variant<Ts...>>::type
    >
    EGGS_CXX11_CONSTEXPR T const& get(variant<Ts...> const& v)
    {
        return v.which() == I
          ? detail::access::get(v, detail::index<I>{})
          : detail::throw_bad_variant_access<T const&>();
    }

    //! template <std::size_t I, class ...Ts>
    //! constexpr variant_element_t<I, variant<Ts...>>&& get(variant<Ts...>&& v);
    //!
    //! \effects Equivalent to return `std::forward<variant_element_t<I,
    //!  variant<Ts...>>>(get<I>(v))`.
    //!
    //! \remarks This function shall be a `constexpr` function.
    template <
        std::size_t I, typename ...Ts
      , typename T = typename variant_element<I, variant<Ts...>>::type
    >
    EGGS_CXX14_CONSTEXPR T&& get(variant<Ts...>&& v)
    {
        return detail::forward<T>(get<I>(v));
    }

    //! template <std::size_t I, class ...Ts>
    //! constexpr variant_element_t<I, variant<Ts...>> const&& get(variant<Ts...> const&& v);
    //!
    //! \effects Equivalent to return `std::forward<variant_element_t<I,
    //!  variant<Ts...>> const>(get<I>(v))`.
    //!
    //! \remarks This function shall be a `constexpr` function.
    template <
        std::size_t I, typename ...Ts
      , typename T = typename variant_element<I, variant<Ts...>>::type
    >
    EGGS_CXX14_CONSTEXPR T const&& get(variant<Ts...> const&& v)
    {
        return detail::forward<T const>(get<I>(v));
    }

    //! template <class T, class ...Ts>
    //! constexpr T& get(variant<Ts...>& v);
    //!
    //! \requires The type `T` occurs exactly once in `Ts...`.
    //!
    //! \returns A reference to the active member of `v` if it is of type `T`.
    //!
    //! \throws `bad_variant_access` if the active member of `v` is not of
    //!  type `T`.
    //!
    //! \remarks This function shall be a `constexpr` function.
    template <
        typename T, typename ...Ts
      , std::size_t I = detail::index_of<
            T, detail::pack<typename std::remove_cv<Ts>::type...>>::value
    >
    EGGS_CXX14_CONSTEXPR T& get(variant<Ts...>& v)
    {
        return v.which() == I
          ? detail::access::get(v, detail::index<I>{})
          : detail::throw_bad_variant_access<T&>();
    }

    //! template <class T, class ...Ts>
    //! constexpr T const& get(variant<Ts...> const& v);
    //!
    //! \requires The type `T` occurs exactly once in `Ts...`.
    //!
    //! \returns A const reference to the active member of `v` if it is of
    //!  type `T`.
    //!
    //! \throws `bad_variant_access` if the active member of `v` is not of
    //!  type `T`.
    //!
    //! \remarks This function shall be a `constexpr` function.
    template <
        typename T, typename ...Ts
      , std::size_t I = detail::index_of<
            T, detail::pack<typename std::remove_cv<Ts>::type...>>::value
    >
    EGGS_CXX11_CONSTEXPR T const& get(variant<Ts...> const& v)
    {
        return v.which() == I
          ? detail::access::get(v, detail::index<I>{})
          : detail::throw_bad_variant_access<T const&>();
    }

    //! template <class T, class ...Ts>
    //! constexpr T&& get(variant<Ts...>&& v);
    //!
    //! \effects Equivalent to return `std::forward<T>(get<T>(v))`.
    //!
    //! \remarks This function shall be a `constexpr` function.
    template <typename T, typename ...Ts>
    EGGS_CXX14_CONSTEXPR T&& get(variant<Ts...>&& v)
    {
        return detail::forward<T>(get<T>(v));
    }

    //! template <class T, class ...Ts>
    //! constexpr T const&& get(variant<Ts...> const&& v);
    //!
    //! \effects Equivalent to return `std::forward<T const>(get<T>(v))`.
    //!
    //! \remarks This function shall be a `constexpr` function.
    template <typename T, typename ...Ts>
    EGGS_CXX14_CONSTEXPR T const&& get(variant<Ts...> const&& v)
    {
        return detail::forward<T const>(get<T>(v));
    }

    ///////////////////////////////////////////////////////////////////////////
    //! template <class ...Ts>
    //! constexpr bool operator==(variant<Ts...> const& lhs, variant<Ts...> const& rhs);
    //!
    //! \requires `*lhs.target<T>() == *rhs.target<T>()` is a valid expression
    //!  returning a type that is convertible to `bool` for all `T` in `Ts...`.
    //!
    //! \returns If `lhs.which() != rhs.which()`, `false`; otherwise, if
    //!  `!bool(lhs)`, `true`; otherwise, `*lhs.target<T>() == *rhs.target<T>()`
    //!  where `T` is the type of the active member of both `lhs` and `rhs`.
    //!
    //! \remarks This function shall be a `constexpr` function unless
    //!  `lhs.which() == rhs.which()` and `*lhs.target<T>() == *rhs.target<T>()`
    //!  where `T` is the type of the active member of both `lhs` and `rhs` is
    //!  not a constant expression.
    template <typename ...Ts>
    EGGS_CXX11_CONSTEXPR bool operator==(
        variant<Ts...> const& lhs, variant<Ts...> const& rhs)
    {
        return lhs.which() == rhs.which()
          ? detail::equal_to<detail::storage<Ts...>>{}(
                detail::typed_index_pack<detail::pack<detail::empty, Ts...>>{}
              , lhs.which() + 1
              , detail::access::storage(lhs), detail::access::storage(rhs)
            )
          : false;
    }

    EGGS_CXX11_CONSTEXPR inline bool operator==(
        variant<> const& /*lhs*/, variant<> const& /*rhs*/)
    {
        return true;
    }

    //! template <class ...Ts>
    //! constexpr bool operator!=(variant<Ts...> const& lhs, variant<Ts...> const& rhs);
    //!
    //! \requires `*lhs.target<T>() != *rhs.target<T>()` is a valid expression
    //!  returning a type that is convertible to `bool` for all `T` in `Ts...`.
    //!
    //! \returns If `lhs.which() != rhs.which()`, `true`; otherwise, if
    //!  `!bool(lhs)`, `false`; otherwise, `*lhs.target<T>() != *rhs.target<T>()`
    //!  where `T` is the type of the active member of both `lhs` and `rhs`.
    //!
    //! \remarks This function shall be a `constexpr` function unless
    //!  `lhs.which() == rhs.which()` and `*lhs.target<T>() != *rhs.target<T>()`
    //!  where `T` is the type of the active member of both `lhs` and `rhs` is
    //!  not a constant expression.
    template <typename ...Ts>
    EGGS_CXX11_CONSTEXPR bool operator!=(
        variant<Ts...> const& lhs, variant<Ts...> const& rhs)
    {
        return lhs.which() == rhs.which()
          ? detail::not_equal_to<detail::storage<Ts...>>{}(
                detail::typed_index_pack<detail::pack<detail::empty, Ts...>>{}
              , lhs.which() + 1
              , detail::access::storage(lhs), detail::access::storage(rhs)
            )
          : true;
    }

    EGGS_CXX11_CONSTEXPR inline bool operator!=(
        variant<> const& /*lhs*/, variant<> const& /*rhs*/)
    {
        return false;
    }

    //! template <class ...Ts>
    //! constexpr bool operator<(variant<Ts...> const& lhs, variant<Ts...> const& rhs);
    //!
    //! \requires `*lhs.target<T>() < *rhs.target<T>()` is a valid expression
    //!  returning a type that is convertible to `bool` for all `T` in `Ts...`.
    //!
    //! \returns If `!bool(rhs)`, `false`; otherwise, if `!bool(lhs)`, `true`;
    //!  otherwise, if `lhs.which() == rhs.which()`, `*lhs.target<T>() <
    //!  *rhs.target<T>()` where `T` is the type of the active member of both
    //!  `lhs` and `rhs`; otherwise, `lhs.which() < rhs.which()`.
    //!
    //! \remarks This function shall be a `constexpr` function unless
    //!  `lhs.which() == rhs.which()` and `*lhs.target<T>() < *rhs.target<T>()`
    //!  where `T` is the type of the active member of both `lhs` and `rhs` is
    //!  not a constant expression.
    template <typename ...Ts>
    EGGS_CXX11_CONSTEXPR bool operator<(
        variant<Ts...> const& lhs, variant<Ts...> const& rhs)
    {
        return lhs.which() == rhs.which()
          ? detail::less<detail::storage<Ts...>>{}(
                detail::typed_index_pack<detail::pack<detail::empty, Ts...>>{}
              , lhs.which() + 1
              , detail::access::storage(lhs), detail::access::storage(rhs)
            )
          : bool(lhs) == bool(rhs)
              ? lhs.which() < rhs.which()
              : bool(rhs);
    }

    EGGS_CXX11_CONSTEXPR inline bool operator<(
        variant<> const& /*lhs*/, variant<> const& /*rhs*/)
    {
        return false;
    }

    //! template <class ...Ts>
    //! constexpr bool operator>(variant<Ts...> const& lhs, variant<Ts...> const& rhs);
    //!
    //! \requires `*lhs.target<T>() > *rhs.target<T>()` is a valid expression
    //!  returning a type that is convertible to `bool` for all `T` in `Ts...`.
    //!
    //! \returns If `!bool(lhs)`, `false`; otherwise, if `!bool(rhs)`, `true`;
    //!  otherwise, if `lhs.which() == rhs.which()`, `*lhs.target<T>() >
    //!  *rhs.target<T>()` where `T` is the type of the active member of both
    //!  `lhs` and `rhs`; otherwise, `lhs.which() > rhs.which()`.
    //!
    //! \remarks This function shall be a `constexpr` function unless
    //!  `lhs.which() == rhs.which()` and `*lhs.target<T>() > *rhs.target<T>()`
    //!  where `T` is the type of the active member of both `lhs` and `rhs` is
    //!  not a constant expression.
    template <typename ...Ts>
    EGGS_CXX11_CONSTEXPR bool operator>(
        variant<Ts...> const& lhs, variant<Ts...> const& rhs)
    {
        return lhs.which() == rhs.which()
          ? detail::greater<detail::storage<Ts...>>{}(
                detail::typed_index_pack<detail::pack<detail::empty, Ts...>>{}
              , lhs.which() + 1
              , detail::access::storage(lhs), detail::access::storage(rhs)
            )
          : bool(lhs) == bool(rhs)
              ? lhs.which() > rhs.which()
              : bool(lhs);
    }

    EGGS_CXX11_CONSTEXPR inline bool operator>(
        variant<> const& /*lhs*/, variant<> const& /*rhs*/)
    {
        return false;
    }

    //! template <class ...Ts>
    //! constexpr bool operator<=(variant<Ts...> const& lhs, variant<Ts...> const& rhs);
    //!
    //! \requires `*lhs.target<T>() <= *rhs.target<T>()` is a valid expression
    //!  returning a type that is convertible to `bool` for all `T` in `Ts...`.
    //!
    //! \returns If `!bool(lhs)`, `true`; otherwise, if `!bool(rhs)`, `false`;
    //!  otherwise, if `lhs.which() == rhs.which()`, `*lhs.target<T>() <=
    //!  *rhs.target<T>()` where `T` is the type of the active member of both
    //!  `lhs` and `rhs`; otherwise, `lhs.which() < rhs.which()`.
    //!
    //! \remarks This function shall be a `constexpr` function unless
    //!  `lhs.which() == rhs.which()` and `*lhs.target<T>() <= *rhs.target<T>()`
    //!  where `T` is the type of the active member of both `lhs` and `rhs` is
    //!  not a constant expression.
    template <typename ...Ts>
    EGGS_CXX11_CONSTEXPR bool operator<=(
        variant<Ts...> const& lhs, variant<Ts...> const& rhs)
    {
        return lhs.which() == rhs.which()
          ? detail::less_equal<detail::storage<Ts...>>{}(
                detail::typed_index_pack<detail::pack<detail::empty, Ts...>>{}
              , lhs.which() + 1
              , detail::access::storage(lhs), detail::access::storage(rhs)
            )
          : bool(lhs) == bool(rhs)
              ? lhs.which() < rhs.which()
              : bool(rhs);
    }

    EGGS_CXX11_CONSTEXPR inline bool operator<=(
        variant<> const& /*lhs*/, variant<> const& /*rhs*/)
    {
        return true;
    }

    //! template <class ...Ts>
    //! constexpr bool operator>=(variant<Ts...> const& lhs, variant<Ts...> const& rhs);
    //!
    //! \requires `*lhs.target<T>() >= *rhs.target<T>()` is a valid expression
    //!  returning a type that is convertible to `bool` for all `T` in `Ts...`.
    //!
    //! \returns If `!bool(rhs)`, `true`; otherwise, if `!bool(lhs)`, `false`;
    //!  otherwise, if `lhs.which() == rhs.which()`, `*lhs.target<T>() >=
    //!  *rhs.target<T>()` where `T` is the type of the active member of both
    //!  `lhs` and `rhs`; otherwise, `lhs.which() > rhs.which()`.
    //!
    //! \remarks This function shall be a `constexpr` function unless
    //!  `lhs.which() == rhs.which()` and `*lhs.target<T>() >= *rhs.target<T>()`
    //!  where `T` is the type of the active member of both `lhs` and `rhs` is
    //!  not a constant expression.
    template <typename ...Ts>
    EGGS_CXX11_CONSTEXPR bool operator>=(
        variant<Ts...> const& lhs, variant<Ts...> const& rhs)
    {
        return lhs.which() == rhs.which()
          ? detail::greater_equal<detail::storage<Ts...>>{}(
                detail::typed_index_pack<detail::pack<detail::empty, Ts...>>{}
              , lhs.which() + 1
              , detail::access::storage(lhs), detail::access::storage(rhs)
            )
          : bool(lhs) == bool(rhs)
              ? lhs.which() > rhs.which()
              : bool(lhs);
    }

    EGGS_CXX11_CONSTEXPR inline bool operator>=(
        variant<> const& /*lhs*/, variant<> const& /*rhs*/)
    {
        return true;
    }

    ///////////////////////////////////////////////////////////////////////////
    //! template <class ...Ts, class T>
    //! constexpr bool operator==(variant<Ts...> const& lhs, U const& rhs);
    //!
    //! Let `T` be one of the types in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules.
    //!
    //! \requires `*lhs.target<T>() == rhs` is a valid expression returning a
    //!  type that is convertible to `bool`.
    //!
    //! \returns If `lhs` has an active member of type `T`,
    //!  `*lhs.target<T>() == rhs`; otherwise, `false`.
    //!
    //! \remarks This operator shall not participate in overload resolution
    //!  unless there is a type `T` in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules. This
    //!  function shall be a `constexpr` function unless `lhs` has an active
    //!  member of type `T` and `*lhs.target<T>() == rhs` is not a constant
    //!  expression.
    template <
        typename ...Ts, typename U
      , std::size_t I = detail::index_of_best_match<
            U const&, detail::pack<Ts...>>::value
      , typename T = typename detail::at_index<
            I, detail::pack<Ts...>>::type
    >
    EGGS_CXX11_CONSTEXPR bool operator==(
        variant<Ts...> const& lhs, U const& rhs)
    {
        return lhs.which() == I
          ? *lhs.template target<T>() == rhs
          : false;
    }

    //! template <class T, class ...Ts>
    //! constexpr bool operator==(U const& lhs, variant<Ts...> const& rhs);
    //!
    //! Let `T` be one of the types in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules.
    //!
    //! \requires `lhs == *rhs.target<T>()` is a valid expression returning a
    //!  type that is convertible to `bool`.
    //!
    //! \returns If `rhs` has an active member of type `T`,
    //!  `lhs == *rhs.target<T>()`; otherwise, `false`.
    //!
    //! \remarks This operator shall not participate in overload resolution
    //!  unless there is a type `T` in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules. This
    //!  function shall be a `constexpr` function unless `rhs` has an active
    //!  member of type `T` and `lhs == *rhs.target<T>()` is not a constant
    //!  expression.
    template <
        typename U, typename ...Ts
      , std::size_t I = detail::index_of_best_match<
            U const&, detail::pack<Ts...>>::value
      , typename T = typename detail::at_index<
            I, detail::pack<Ts...>>::type
    >
    EGGS_CXX11_CONSTEXPR bool operator==(
        U const& lhs, variant<Ts...> const& rhs)
    {
        return rhs.which() == I
          ? lhs == *rhs.template target<T>()
          : false;
    }

    //! template <class ...Ts, class T>
    //! constexpr bool operator!=(variant<Ts...> const& lhs, U const& rhs);
    //!
    //! Let `T` be one of the types in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules.
    //!
    //! \requires `*lhs.target<T>() != rhs` is a valid expression returning a
    //!  type that is convertible to `bool`.
    //!
    //! \returns If `lhs` has an active member of type `T`,
    //!  `*lhs.target<T>() != rhs`; otherwise, `true`.
    //!
    //! \remarks This operator shall not participate in overload resolution
    //!  unless there is a type `T` in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules. This
    //!  function shall be a `constexpr` function unless `lhs` has an active
    //!  member of type `T` and `*lhs.target<T>() != rhs` is not a constant
    //!  expression.
    template <
        typename ...Ts, typename U
      , std::size_t I = detail::index_of_best_match<
            U const&, detail::pack<Ts...>>::value
      , typename T = typename detail::at_index<
            I, detail::pack<Ts...>>::type
    >
    EGGS_CXX11_CONSTEXPR bool operator!=(
        variant<Ts...> const& lhs, U const& rhs)
    {
        return lhs.which() == I
          ? *lhs.template target<T>() != rhs
          : true;
    }

    //! template <class T, class ...Ts>
    //! constexpr bool operator!=(U const& lhs, variant<Ts...> const& rhs);
    //!
    //! Let `T` be one of the types in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules.
    //!
    //! \requires `lhs != *rhs.target<T>()` is a valid expression returning a
    //!  type that is convertible to `bool`.
    //!
    //! \returns If `rhs` has an active member of type `T`,
    //!  `lhs != *rhs.target<T>()`; otherwise, `true`.
    //!
    //! \remarks This operator shall not participate in overload resolution
    //!  unless there is a type `T` in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules. This
    //!  function shall be a `constexpr` function unless `rhs` has an active
    //!  member of type `T` and `lhs != *rhs.target<T>()` is not a constant
    //!  expression.
    template <
        typename U, typename ...Ts
      , std::size_t I = detail::index_of_best_match<
            U const&, detail::pack<Ts...>>::value
      , typename T = typename detail::at_index<
            I, detail::pack<Ts...>>::type
    >
    EGGS_CXX11_CONSTEXPR bool operator!=(
        U const& lhs, variant<Ts...> const& rhs)
    {
        return rhs.which() == I
          ? lhs != *rhs.template target<T>()
          : true;
    }

    //! template <class ...Ts, class T>
    //! constexpr bool operator<(variant<Ts...> const& lhs, U const& rhs);
    //!
    //! Let `T` be one of the types in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules.
    //!
    //! \requires `*lhs.target<T>() < rhs` is a valid expression returning a
    //!  type that is convertible to `bool`.
    //!
    //! \returns If `!bool(lhs)`, `true`; otherwise, if `lhs` has an active
    //!  member of type `T`, `*lhs.target<T>() < rhs`; otherwise,
    //!  `lhs.which() < I` where `I` is the zero-based index of `T` in `Ts...`.
    //!
    //! \remarks This operator shall not participate in overload resolution
    //!  unless there is a type `T` in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules. This
    //!  function shall be a `constexpr` function unless `lhs` has an active
    //!  member of type `T` and `*lhs.target<T>() < rhs` is not a constant
    //!  expression.
    template <
        typename ...Ts, typename U
      , std::size_t I = detail::index_of_best_match<
            U const&, detail::pack<Ts...>>::value
      , typename T = typename detail::at_index<
            I, detail::pack<Ts...>>::type
    >
    EGGS_CXX11_CONSTEXPR bool operator<(
        variant<Ts...> const& lhs, U const& rhs)
    {
        return lhs.which() == I
          ? *lhs.template target<T>() < rhs
          : bool(lhs)
              ? lhs.which() < I
              : true;
    }

    //! template <class T, class ...Ts>
    //! constexpr bool operator<(U const& lhs, variant<Ts...> const& rhs);
    //!
    //! Let `T` be one of the types in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules.
    //!
    //! \requires `lhs < *rhs.target<T>()` is a valid expression returning a
    //!  type that is convertible to `bool`.
    //!
    //! \returns If `!bool(rhs)`, `false`; otherwise, if `rhs` has an active
    //!  member of type `T`, `lhs < *rhs.target<T>()`; otherwise,
    //!  `I < rhs.which()` where `I` is the zero-based index of `T` in `Ts...`.
    //!
    //! \remarks This operator shall not participate in overload resolution
    //!  unless there is a type `T` in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules. This
    //!  function shall be a `constexpr` function unless `rhs` has an active
    //!  member of type `T` and `lhs < *rhs.target<T>()` is not a constant
    //!  expression.
    template <
        typename U, typename ...Ts
      , std::size_t I = detail::index_of_best_match<
            U const&, detail::pack<Ts...>>::value
      , typename T = typename detail::at_index<
            I, detail::pack<Ts...>>::type
    >
    EGGS_CXX11_CONSTEXPR bool operator<(
        U const& lhs, variant<Ts...> const& rhs)
    {
        return rhs.which() == I
          ? lhs < *rhs.template target<T>()
          : bool(rhs)
              ? I < rhs.which()
              : false;
    }

    //! template <class ...Ts, class T>
    //! constexpr bool operator>(variant<Ts...> const& lhs, U const& rhs);
    //!
    //! Let `T` be one of the types in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules.
    //!
    //! \requires `*lhs.target<T>() > rhs` is a valid expression returning a
    //!  type that is convertible to `bool`.
    //!
    //! \returns If `!bool(lhs)`, `false`; otherwise, if `lhs` has an active
    //!  member of type `T`, `*lhs.target<T>() > rhs`; otherwise,
    //!  `lhs.which() > I` where `I` is the zero-based index of `T` in `Ts...`.
    //!
    //! \remarks This operator shall not participate in overload resolution
    //!  unless there is a type `T` in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules. This
    //!  function shall be a `constexpr` function unless `lhs` has an active
    //!  member of type `T` and `*lhs.target<T>() > rhs` is not a constant
    //!  expression.
    template <
        typename ...Ts, typename U
      , std::size_t I = detail::index_of_best_match<
            U const&, detail::pack<Ts...>>::value
      , typename T = typename detail::at_index<
            I, detail::pack<Ts...>>::type
    >
    EGGS_CXX11_CONSTEXPR bool operator>(
        variant<Ts...> const& lhs, U const& rhs)
    {
        return lhs.which() == I
          ? *lhs.template target<T>() > rhs
          : bool(lhs)
              ? lhs.which() > I
              : false;
    }

    //! template <class T, class ...Ts>
    //! constexpr bool operator>(U const& lhs, variant<Ts...> const& rhs);
    //!
    //! Let `T` be one of the types in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules.
    //!
    //! \requires `lhs > *rhs.target<T>()` is a valid expression returning a
    //!  type that is convertible to `bool`.
    //!
    //! \returns If `!bool(rhs)`, `true`; otherwise, if `rhs` has an active
    //!  member of type `T`, `lhs > *rhs.target<T>()`; otherwise,
    //!  `I > rhs.which()` where `I` is the zero-based index of `T` in `Ts...`.
    //!
    //! \remarks This operator shall not participate in overload resolution
    //!  unless there is a type `T` in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules. This
    //!  function shall be a `constexpr` function unless `rhs` has an active
    //!  member of type `T` and `lhs > *rhs.target<T>()` is not a constant
    //!  expression.
    template <
        typename U, typename ...Ts
      , std::size_t I = detail::index_of_best_match<
            U const&, detail::pack<Ts...>>::value
      , typename T = typename detail::at_index<
            I, detail::pack<Ts...>>::type
    >
    EGGS_CXX11_CONSTEXPR bool operator>(
        U const& lhs, variant<Ts...> const& rhs)
    {
        return rhs.which() == I
          ? lhs > *rhs.template target<T>()
          : bool(rhs)
              ? I > rhs.which()
              : true;
    }

    //! template <class ...Ts, class T>
    //! constexpr bool operator<=(variant<Ts...> const& lhs, U const& rhs);
    //!
    //! Let `T` be one of the types in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules.
    //!
    //! \requires `*lhs.target<T>() <= rhs` is a valid expression returning a
    //!  type that is convertible to `bool`.
    //!
    //! \returns If `!bool(lhs)`, `true`; otherwise, if `lhs` has an active
    //!  member of type `T`, `*lhs.target<T>() <= rhs`; otherwise,
    //!  `lhs.which() < I` where `I` is the zero-based index of `T` in `Ts...`.
    //!
    //! \remarks This operator shall not participate in overload resolution
    //!  unless there is a type `T` in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules. This
    //!  function shall be a `constexpr` function unless `lhs` has an active
    //!  member of type `T` and `*lhs.target<T>() <= rhs` is not a constant
    //!  expression.
    template <
        typename ...Ts, typename U
      , std::size_t I = detail::index_of_best_match<
            U const&, detail::pack<Ts...>>::value
      , typename T = typename detail::at_index<
            I, detail::pack<Ts...>>::type
    >
    EGGS_CXX11_CONSTEXPR bool operator<=(
        variant<Ts...> const& lhs, U const& rhs)
    {
        return lhs.which() == I
          ? *lhs.template target<T>() <= rhs
          : bool(lhs)
              ? lhs.which() < I
              : true;
    }

    //! template <class T, class ...Ts>
    //! constexpr bool operator<=(U const& lhs, variant<Ts...> const& rhs);
    //!
    //! Let `T` be one of the types in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules.
    //!
    //! \requires `lhs <= *rhs.target<T>()` is a valid expression returning a
    //!  type that is convertible to `bool`.
    //!
    //! \returns If `!bool(rhs)`, `false`; otherwise, if `rhs` has an active
    //!  member of type `T`, `lhs <= *rhs.target<T>()`; otherwise,
    //!  `I < rhs.which()` where `I` is the zero-based index of `T` in `Ts...`.
    //!
    //! \remarks This operator shall not participate in overload resolution
    //!  unless there is a type `T` in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules. This
    //!  function shall be a `constexpr` function unless `rhs` has an active
    //!  member of type `T` and `lhs <= *rhs.target<T>()` is not a constant
    //!  expression.
    template <
        typename U, typename ...Ts
      , std::size_t I = detail::index_of_best_match<
            U const&, detail::pack<Ts...>>::value
      , typename T = typename detail::at_index<
            I, detail::pack<Ts...>>::type
    >
    EGGS_CXX11_CONSTEXPR bool operator<=(
        U const& lhs, variant<Ts...> const& rhs)
    {
        return rhs.which() == I
          ? lhs <= *rhs.template target<T>()
          : bool(rhs)
              ? I < rhs.which()
              : false;
    }

    //! template <class ...Ts, class T>
    //! constexpr bool operator>=(variant<Ts...> const& lhs, U const& rhs);
    //!
    //! Let `T` be one of the types in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules.
    //!
    //! \requires `*lhs.target<T>() >= rhs` is a valid expression returning a
    //!  type that is convertible to `bool`.
    //!
    //! \returns If `!bool(lhs)`, `false`; otherwise, if `lhs` has an active
    //!  member of type `T`, `*lhs.target<T>() >= rhs`; otherwise,
    //!  `lhs.which() > I` where `I` is the zero-based index of `T` in `Ts...`.
    //!
    //! \remarks This operator shall not participate in overload resolution
    //!  unless there is a type `T` in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules. This
    //!  function shall be a `constexpr` function unless `lhs` has an active
    //!  member of type `T` and `*lhs.target<T>() >= rhs` is not a constant
    //!  expression.
    template <
        typename ...Ts, typename U
      , std::size_t I = detail::index_of_best_match<
            U const&, detail::pack<Ts...>>::value
      , typename T = typename detail::at_index<
            I, detail::pack<Ts...>>::type
    >
    EGGS_CXX11_CONSTEXPR bool operator>=(
        variant<Ts...> const& lhs, U const& rhs)
    {
        return lhs.which() == I
          ? *lhs.template target<T>() >= rhs
          : bool(lhs)
              ? lhs.which() > I
              : false;
    }

    //! template <class T, class ...Ts>
    //! constexpr bool operator>=(U const& lhs, variant<Ts...> const& rhs);
    //!
    //! Let `T` be one of the types in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules.
    //!
    //! \requires `lhs >= *rhs.target<T>()` is a valid expression returning a
    //!  type that is convertible to `bool`.
    //!
    //! \returns If `!bool(rhs)`, `true`; otherwise, if `rhs` has an active
    //!  member of type `T`, `lhs >= *rhs.target<T>()`; otherwise,
    //!  `I > rhs.which()` where `I` is the zero-based index of `T` in `Ts...`.
    //!
    //! \remarks This operator shall not participate in overload resolution
    //!  unless there is a type `T` in `Ts...` for which `U const&` is
    //!  unambiguously convertible to by overload resolution rules. This
    //!  function shall be a `constexpr` function unless `rhs` has an active
    //!  member of type `T` and `lhs >= *rhs.target<T>()` is not a constant
    //!  expression.
    template <
        typename U, typename ...Ts
      , std::size_t I = detail::index_of_best_match<
            U const&, detail::pack<Ts...>>::value
      , typename T = typename detail::at_index<
            I, detail::pack<Ts...>>::type
    >
    EGGS_CXX11_CONSTEXPR bool operator>=(
        U const& lhs, variant<Ts...> const& rhs)
    {
        return rhs.which() == I
          ? lhs >= *rhs.template target<T>()
          : bool(rhs)
              ? I > rhs.which()
              : true;
    }

    ///////////////////////////////////////////////////////////////////////////
    //! template <class R, class F, class ...Vs>
    //! constexpr R apply(F&& f, Vs&&... vs);
    //!
    //! Let `Vi` be the `i`-th type in `Vs...`, `Ui` be `std::decay_t<Vi>`,
    //! where all indexing is zero-based.
    //!
    //! \requires For all `i`, `Ui` shall be the type `variant<Tsi...>` where
    //!  `Tsi` is the parameter pack representing the element types in `Ui`.
    //!  `INVOKE(std::forward<F>(f), get<Is>(std::forward<Vs>(vs))..., R)`
    //!  shall be a valid expression for all `Is...` in the range `[0u,
    //!  sizeof...(Tsi))...`.
    //!
    //! \effects Equivalent to `INVOKE(std::forward<F>(f), get<Is>(
    //!  std::forward<Vs>(vs))...), R)` where `Is...` are the zero-based
    //!  indices of the active members of `vs...`.
    //!
    //! \throws `bad_variant_access` if any of `vs...` has no active member.
    //!
    //! \remarks If the selected function is a constant expression, then this
    //!  function shall be a `constexpr` function.
    template <
        typename R, typename F, typename ...Vs
      , typename Enable = typename std::enable_if<
            detail::all_of<detail::pack<
                detail::is_variant<typename std::remove_reference<Vs>::type>...
            >>::value
        >::type
    >
    EGGS_CXX11_CONSTEXPR R apply(F&& f, Vs&&... vs)
    {
        return detail::apply<R>(detail::forward<F>(f),
            detail::access::storage(detail::forward<Vs>(vs))...);
    }

    template <typename R, typename F>
    EGGS_CXX11_CONSTEXPR R apply(F&& f)
    {
        return detail::apply<R>(detail::forward<F>(f));
    }

    //! template <class F, class ...Vs>
    //! constexpr R apply(F&& f, Vs&&... vs);
    //!
    //! Let `Ri...` be the return types of every potentially evaluated
    //!  `INVOKE` expression; if every `Ri...` is the same type, then let `R`
    //!  be that type.
    //!
    //! \effects Equivalent to `apply<R>(std::forward<F>(f),
    //!  std::forward<Vs>(vs)...)`.
    //!
    //! \remarks This function shall not participate in overload resolution
    //!  unless the return type of every potentially evaluated `INVOKE`
    //!  expression is the same type. If the selected function is a constant
    //!  expression, then this function shall be a `constexpr` function.
    template <
        int DeductionGuard = 0, typename F, typename ...Vs
      , typename R = typename detail::apply_result<F, detail::pack<
            decltype(detail::access::storage(std::declval<Vs>()))...>>::type
      , typename Enable = typename std::enable_if<
            detail::all_of<detail::pack<
                detail::is_variant<typename std::remove_reference<Vs>::type>...
            >>::value
        >::type
    >
    EGGS_CXX11_CONSTEXPR R apply(F&& f, Vs&&... vs)
    {
        return apply<R>(detail::forward<F>(f), detail::forward<Vs>(vs)...);
    }

    template <
        int DeductionGuard = 0, typename F
      , typename R = typename detail::apply_result<F, detail::pack<>>::type
    >
    EGGS_CXX11_CONSTEXPR R apply(F&& f)
    {
        return apply<R>(detail::forward<F>(f));
    }

    ///////////////////////////////////////////////////////////////////////////
    //! template <class ...Ts>
    //! void swap(variant<Ts...>& x, variant<Ts...>& y)
    //!   noexcept(noexcept(x.swap(y))
    //!
    //! \effects Calls `x.swap(y)`.
    //!
    //! \remarks This function shall be defined as deleted unless
    //!  `std::is_move_constructible_v<T> && std::is_swappable_v<T>` is `true`
    //!  for all `T` in `Ts...`. If `std::is_trivially_copyable_v<T> &&
    //!  std::is_copy_assignable_v<T>` is `true` for all `T` in `Ts...`, then
    //!  this function shall be a `constexpr` function.
    template <
        typename ...Ts
      , typename std::enable_if<detail::all_of<detail::pack<
            detail::is_swappable<Ts>...
          , std::is_move_constructible<Ts>...
        >>::value, bool>::type = true
    >
    EGGS_CXX14_CONSTEXPR void swap(variant<Ts...>& x, variant<Ts...>& y)
        EGGS_CXX11_NOEXCEPT_IF(EGGS_CXX11_NOEXCEPT_EXPR(x.swap(y)))
    {
        x.swap(y);
    }

    template <
        typename ...Ts
      , typename std::enable_if<!detail::all_of<detail::pack<
            detail::is_swappable<Ts>...
          , std::is_move_constructible<Ts>...
        >>::value, bool>::type = false
    >
    EGGS_CXX14_CONSTEXPR void swap(variant<Ts...>& x, variant<Ts...>& y)
#if EGGS_CXX11_HAS_DELETED_FUNCTIONS
        = delete;
#else
        ;
#endif
}}

namespace std
{
    //! template <class ...Ts>
    //! struct hash<::eggs::variants::variant<Ts...>>;
    //!
    //! \requires The template specialization `std::hash<T>` shall meet the
    //!  requirements of class template `std::hash` for all `T` in `Ts...`.
    //!  The template specialization `std::hash<variant<Ts...>>` shall meet
    //!  the requirements of class template `std::hash`. For an object `v` of
    //!  type `variant<Ts...>`, if `v` has an active member of type `T`,
    //!  `std::hash<variant<Ts...>>()(v)` shall evaluate to the same value as
    //!  `std::hash<T>()(*v.target<T>())`; otherwise it evaluates to an
    //!  unspecified value.
    template <typename ...Ts>
    struct hash< ::eggs::variants::variant<Ts...>>
    {
        using argument_type = ::eggs::variants::variant<Ts...>;
        using result_type = std::size_t;

        std::size_t operator()(::eggs::variants::variant<Ts...> const& v) const
        {
            ::eggs::variants::detail::hash h;
            return bool(v)
              ? ::eggs::variants::apply<std::size_t>(h, v)
              : 0u;
        }
    };
}

#include <eggs/variant/detail/config/suffix.hpp>

#endif /*EGGS_VARIANT_VARIANT_HPP*/
