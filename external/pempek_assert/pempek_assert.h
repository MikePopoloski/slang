// see README.md for usage instructions.
// (‑●‑●)> released under the WTFPL v2 license, by Gregory Pakosz (@gpakosz)

// -- usage --------------------------------------------------------------------
/*

  run-time assertions:

    PPK_ASSERT(expression);
    PPK_ASSERT(expression, message, ...);

    PPK_ASSERT_WARNING(expression);
    PPK_ASSERT_WARNING(expression, message, ...);

    PPK_ASSERT_DEBUG(expression);
    PPK_ASSERT_DEBUG(expression, message, ...);

    PPK_ASSERT_ERROR(expression);
    PPK_ASSERT_ERROR(expression, message);

    PPK_ASSERT_FATAL(expression);
    PPK_ASSERT_FATAL(expression, message, ...);

    PPK_ASSERT_CUSTOM(level, expression);
    PPK_ASSERT_CUSTOM(level, expression, message, ...);

    PPK_ASSERT_USED(type)
    PPK_ASSERT_USED_WARNING(type)
    PPK_ASSERT_USED_DEBUG(type)
    PPK_ASSERT_USED_ERROR(type)
    PPK_ASSERT_USED_FATAL(type)
    PPK_ASSERT_USED_CUSTOM(level, type)

    PPK_ASSERT_USED(bool) foo()
    {
      return true;
    }

  compile-time assertions:

    PPK_STATIC_ASSERT(expression)
    PPK_STATIC_ASSERT(expression, message)

*/

#if !defined(PPK_ASSERT_ENABLED)
  #if !defined(NDEBUG) // if we are in debug mode
    #define PPK_ASSERT_ENABLED 1 // enable them
  #endif
#endif

#if !defined(PPK_ASSERT_DEFAULT_LEVEL)
  #define PPK_ASSERT_DEFAULT_LEVEL Debug
#endif

// -- implementation -----------------------------------------------------------

#if (defined(__GNUC__) && ((__GNUC__ * 1000 + __GNUC_MINOR__ * 100) >= 4600)) || defined(__clang__)
  #pragma GCC diagnostic push
  #pragma GCC diagnostic ignored "-Wvariadic-macros"
#endif

#if defined(__clang__)
  #pragma GCC diagnostic ignored "-Wgnu-zero-variadic-macro-arguments"
#endif

#if !defined(PPK_ASSERT_H)
  #define PPK_ASSERT_H

  #define PPK_ASSERT(...)                    PPK_ASSERT_(pempek::assert::implementation::AssertLevel::PPK_ASSERT_DEFAULT_LEVEL, __VA_ARGS__)
  #define PPK_ASSERT_WARNING(...)            PPK_ASSERT_(pempek::assert::implementation::AssertLevel::Warning, __VA_ARGS__)
  #define PPK_ASSERT_DEBUG(...)              PPK_ASSERT_(pempek::assert::implementation::AssertLevel::Debug, __VA_ARGS__)
  #define PPK_ASSERT_ERROR(...)              PPK_ASSERT_(pempek::assert::implementation::AssertLevel::Error, __VA_ARGS__)
  #define PPK_ASSERT_FATAL(...)              PPK_ASSERT_(pempek::assert::implementation::AssertLevel::Fatal, __VA_ARGS__)
  #define PPK_ASSERT_CUSTOM(level, ...)      PPK_ASSERT_(level, __VA_ARGS__)

  #define PPK_ASSERT_USED(...)               PPK_ASSERT_USED_(__VA_ARGS__)
  #define PPK_ASSERT_USED_WARNING(...)       PPK_ASSERT_USED_(pempek::assert::implementation::AssertLevel::Warning, __VA_ARGS__)
  #define PPK_ASSERT_USED_DEBUG(...)         PPK_ASSERT_USED_(pempek::assert::implementation::AssertLevel::Debug, __VA_ARGS__)
  #define PPK_ASSERT_USED_ERROR(...)         PPK_ASSERT_USED_(pempek::assert::implementation::AssertLevel::Error, __VA_ARGS__)
  #define PPK_ASSERT_USED_FATAL(...)         PPK_ASSERT_USED_(pempek::assert::implementation::AssertLevel::Fatal, __VA_ARGS__)
  #define PPK_ASSERT_USED_CUSTOM(level, ...) PPK_ASSERT_USED_(level, __VA_ARGS__)


  #define PPK_ASSERT_JOIN(lhs, rhs)   PPK_ASSERT_JOIN_(lhs, rhs)
  #define PPK_ASSERT_JOIN_(lhs, rhs)  PPK_ASSERT_JOIN__(lhs, rhs)
  #define PPK_ASSERT_JOIN__(lhs, rhs) lhs##rhs

  #define PPK_ASSERT_FILE __FILE__
  #define PPK_ASSERT_LINE __LINE__
  #if defined(__GNUC__) || defined(__clang__)
    #define PPK_ASSERT_FUNCTION __PRETTY_FUNCTION__
  #elif defined(_MSC_VER)
    #define PPK_ASSERT_FUNCTION __FUNCSIG__
  #else
    #define PPK_ASSERT_FUNCTION __FUNCTION__
  #endif

  #if defined(_MSC_VER)
    #define PPK_ASSERT_ALWAYS_INLINE __forceinline
  #elif defined(__GNUC__) || defined(__clang__)
    #define PPK_ASSERT_ALWAYS_INLINE inline __attribute__((always_inline))
  #else
    #define PPK_ASSERT_ALWAYS_INLINE inline
  #endif

  #define PPK_ASSERT_NO_MACRO

  #define PPK_ASSERT_APPLY_VA_ARGS(M, ...) PPK_ASSERT_APPLY_VA_ARGS_(M, (__VA_ARGS__))
  #define PPK_ASSERT_APPLY_VA_ARGS_(M, args) M args

  #define PPK_ASSERT_NARG(...) PPK_ASSERT_APPLY_VA_ARGS(PPK_ASSERT_NARG_, PPK_ASSERT_NO_MACRO,##__VA_ARGS__,\
    32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16,\
    15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, PPK_ASSERT_NO_MACRO)
  #define PPK_ASSERT_NARG_( _0, _1, _2, _3, _4, _5, _6, _7, _8,\
                            _9, _10, _11, _12, _13, _14, _15, _16,\
                            _17, _18, _19, _20, _21, _22, _23, _24,\
                            _25, _26, _27, _28, _29, _30, _31, _32, _33, ...) _33

  #define PPK_ASSERT_HAS_ONE_ARG(...) PPK_ASSERT_APPLY_VA_ARGS(PPK_ASSERT_NARG_, PPK_ASSERT_NO_MACRO,##__VA_ARGS__,\
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,\
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, PPK_ASSERT_NO_MACRO)

  #if defined(__GNUC__) || defined(__clang__)
    #define PPK_ASSERT_LIKELY(arg) __builtin_expect(!!(arg), !0)
    #define PPK_ASSERT_UNLIKELY(arg) __builtin_expect(!!(arg), 0)
  #else
    #define PPK_ASSERT_LIKELY(arg) arg
    #define PPK_ASSERT_UNLIKELY(arg) !arg
  #endif

  #define PPK_ASSERT_UNUSED(expression) (void)(true ? (void)0 : ((void)(expression)))

  #if defined(_WIN32)
    #define PPK_ASSERT_DEBUG_BREAK() __debugbreak()
  #else
    #if defined(__APPLE__)
      #include <TargetConditionals.h>
    #endif
    #if defined(__clang__) && !TARGET_OS_IPHONE || TARGET_IPHONE_SIMULATOR
      #define PPK_ASSERT_DEBUG_BREAK() __builtin_debugtrap()
    #elif defined(linux) || defined(__linux) || defined(__linux__) || defined(__APPLE__)
      #include <signal.h>
      #define PPK_ASSERT_DEBUG_BREAK() raise(SIGTRAP)
    #elif defined(__GNUC__)
      #define PPK_ASSERT_DEBUG_BREAK() __builtin_trap()
    #else
      #define PPK_ASSERT_DEBUG_BREAK() ((void)0)
    #endif
  #endif

  #if (defined (__cplusplus) && (__cplusplus > 199711L)) || (defined(_MSC_FULL_VER) && (_MSC_FULL_VER >= 150020706))
    #define PPK_ASSERT_CXX11
  #endif

  #if defined(PPK_ASSERT_CXX11)
    #define PPK_ASSERT_NULLPTR nullptr
  #else
    #define PPK_ASSERT_NULLPTR 0
  #endif

  #define PPK_ASSERT_(level, ...)          PPK_ASSERT_JOIN(PPK_ASSERT_, PPK_ASSERT_HAS_ONE_ARG(__VA_ARGS__))(level, __VA_ARGS__)
  #define PPK_ASSERT_0(level, ...)         PPK_ASSERT_APPLY_VA_ARGS(PPK_ASSERT_2, level, __VA_ARGS__)
  #define PPK_ASSERT_1(level, expression)  PPK_ASSERT_2(level, expression, PPK_ASSERT_NULLPTR)

  #if defined(_MSC_FULL_VER) && (_MSC_FULL_VER >= 140050215)

    #if defined(PPK_ASSERT_DISABLE_IGNORE_LINE)

      #define PPK_ASSERT_3(level, expression, ...)\
        __pragma(warning(push))\
        __pragma(warning(disable: 4127))\
        do\
        {\
          if (PPK_ASSERT_LIKELY(expression) || pempek::assert::implementation::ignoreAllAsserts());\
          else\
          {\
            if (pempek::assert::implementation::handleAssert(PPK_ASSERT_FILE, PPK_ASSERT_LINE, PPK_ASSERT_FUNCTION, #expression, level, 0, __VA_ARGS__) == pempek::assert::implementation::AssertAction::Break)\
              PPK_ASSERT_DEBUG_BREAK();\
          }\
        }\
        while (false)\
        __pragma(warning(pop))

    #else

      #define PPK_ASSERT_3(level, expression, ...)\
        __pragma(warning(push))\
        __pragma(warning(disable: 4127))\
        do\
        {\
          static bool _ignore = false;\
          if (PPK_ASSERT_LIKELY(expression) || _ignore || pempek::assert::implementation::ignoreAllAsserts());\
          else\
          {\
            if (pempek::assert::implementation::handleAssert(PPK_ASSERT_FILE, PPK_ASSERT_LINE, PPK_ASSERT_FUNCTION, #expression, level, &_ignore, __VA_ARGS__) == pempek::assert::implementation::AssertAction::Break)\
              PPK_ASSERT_DEBUG_BREAK();\
          }\
        }\
        while (false)\
        __pragma(warning(pop))

    #endif

  #else

    #if (defined(__GNUC__) && ((__GNUC__ * 1000 + __GNUC_MINOR__ * 100) >= 4600)) || defined(__clang__)
      #define _pragma(x) _Pragma(#x)
      #define _PPK_ASSERT_WFORMAT_AS_ERROR_BEGIN\
        _pragma(GCC diagnostic push)\
        _pragma(GCC diagnostic error "-Wformat")
      #define _PPK_ASSERT_WFORMAT_AS_ERROR_END\
        _pragma(GCC diagnostic pop)
    #else
      #define _PPK_ASSERT_WFORMAT_AS_ERROR_BEGIN
      #define _PPK_ASSERT_WFORMAT_AS_ERROR_END
    #endif

    #if defined(PPK_ASSERT_DISABLE_IGNORE_LINE)

      #define PPK_ASSERT_3(level, expression, ...)\
        do\
        {\
          if (PPK_ASSERT_LIKELY(expression) || pempek::assert::implementation::ignoreAllAsserts());\
          else\
          {\
            _PPK_ASSERT_WFORMAT_AS_ERROR_BEGIN\
            if (pempek::assert::implementation::handleAssert(PPK_ASSERT_FILE, PPK_ASSERT_LINE, PPK_ASSERT_FUNCTION, #expression, level, 0, __VA_ARGS__) == pempek::assert::implementation::AssertAction::Break)\
              PPK_ASSERT_DEBUG_BREAK();\
            _PPK_ASSERT_WFORMAT_AS_ERROR_END\
          }\
        }\
        while (false)

    #else

      #define PPK_ASSERT_3(level, expression, ...)\
        do\
        {\
          static bool _ignore = false;\
          if (PPK_ASSERT_LIKELY(expression) || _ignore || pempek::assert::implementation::ignoreAllAsserts());\
          else\
          {\
            _PPK_ASSERT_WFORMAT_AS_ERROR_BEGIN\
            if (pempek::assert::implementation::handleAssert(PPK_ASSERT_FILE, PPK_ASSERT_LINE, PPK_ASSERT_FUNCTION, #expression, level, &_ignore, __VA_ARGS__) == pempek::assert::implementation::AssertAction::Break)\
              PPK_ASSERT_DEBUG_BREAK();\
            _PPK_ASSERT_WFORMAT_AS_ERROR_END\
          }\
        }\
        while (false)

    #endif

  #endif

  #define PPK_ASSERT_USED_(...)            PPK_ASSERT_USED_0(PPK_ASSERT_NARG(__VA_ARGS__), __VA_ARGS__)
  #define PPK_ASSERT_USED_0(N, ...)        PPK_ASSERT_JOIN(PPK_ASSERT_USED_, N)(__VA_ARGS__)

  #define PPK_STATIC_ASSERT(...)           PPK_ASSERT_APPLY_VA_ARGS(PPK_ASSERT_JOIN(PPK_STATIC_ASSERT_, PPK_ASSERT_HAS_ONE_ARG(__VA_ARGS__)), __VA_ARGS__)
  #if defined(PPK_ASSERT_CXX11)
    #define PPK_STATIC_ASSERT_0(expression, message) static_assert(expression, message)
  #else
    #define PPK_STATIC_ASSERT_0(expression, message)\
      struct PPK_ASSERT_JOIN(__pempek_assert_static_assertion_at_line_, PPK_ASSERT_LINE)\
      {\
        pempek::assert::implementation::StaticAssertion<static_cast<bool>((expression))> PPK_ASSERT_JOIN(STATIC_ASSERTION_FAILED_AT_LINE_, PPK_ASSERT_LINE);\
      };\
      typedef pempek::assert::implementation::StaticAssertionTest<sizeof(PPK_ASSERT_JOIN(__pempek_assert_static_assertion_at_line_, PPK_ASSERT_LINE))> PPK_ASSERT_JOIN(__pempek_assert_static_assertion_test_at_line_, PPK_ASSERT_LINE)
      // note that we wrap the non existing type inside a struct to avoid warning
      // messages about unused variables when static assertions are used at function
      // scope
      // the use of sizeof makes sure the assertion error is not ignored by SFINAE
  #endif
  #define PPK_STATIC_ASSERT_1(expression)  PPK_STATIC_ASSERT_0(expression, #expression)

  #if !defined (PPK_ASSERT_CXX11)
    namespace pempek {
    namespace assert {
    namespace implementation {

      template <bool>
      struct StaticAssertion;

      template <>
      struct StaticAssertion<true>
      {
      }; // StaticAssertion<true>

      template<int i>
      struct StaticAssertionTest
      {
      }; // StaticAssertionTest<int>

    } // namespace implementation
    } // namespace assert
    } // namespace pempek
  #endif

  #if !defined(PPK_ASSERT_DISABLE_STL)
    #if defined(_MSC_VER)
      #pragma warning(push)
      #pragma warning(disable: 4548)
      #pragma warning(disable: 4710)
    #endif
    #include <stdexcept>
    #if defined(_MSC_VER)
      #pragma warning(pop)
    #endif
  #endif

  #if !defined(PPK_ASSERT_EXCEPTION_MESSAGE_BUFFER_SIZE)
    #define PPK_ASSERT_EXCEPTION_MESSAGE_BUFFER_SIZE 1024
  #endif

  #if defined(PPK_ASSERT_CXX11) && !defined(_MSC_VER)
    #define PPK_ASSERT_EXCEPTION_NO_THROW noexcept(true)
  #else
    #define PPK_ASSERT_EXCEPTION_NO_THROW throw()
  #endif

  #if defined(PPK_ASSERT_CXX11)
    #include <utility>
  #endif

  namespace pempek {
  namespace assert {

  #if !defined(PPK_ASSERT_DISABLE_STL)
    class AssertionException: public std::exception
  #else
    class AssertionException
  #endif
    {
      public:
      explicit AssertionException(const char* file,
                                  int line,
                                  const char* function,
                                  const char* expression,
                                  const char* message);

      AssertionException(const AssertionException& rhs);

      virtual ~AssertionException() PPK_ASSERT_EXCEPTION_NO_THROW;

      AssertionException& operator = (const AssertionException& rhs);

      virtual const char* what() const PPK_ASSERT_EXCEPTION_NO_THROW;

      const char* file() const;
      int line() const;
      const char* function() const;
      const char* expression() const;

      private:
      const char* _file;
      int _line;
      const char* _function;
      const char* _expression;

      enum
      {
        request = PPK_ASSERT_EXCEPTION_MESSAGE_BUFFER_SIZE,
        size = request > sizeof(char*) ? request : sizeof(char*) + 1
      };

      union
      {
        char  _stack[size];
        char* _heap;
      };

      PPK_STATIC_ASSERT(size > sizeof(char*), "invalid_size");
    }; // AssertionException

    PPK_ASSERT_ALWAYS_INLINE const char* AssertionException::file() const
    {
      return _file;
    }

    PPK_ASSERT_ALWAYS_INLINE int AssertionException::line() const
    {
      return _line;
    }

    PPK_ASSERT_ALWAYS_INLINE const char* AssertionException::function() const
    {
      return _function;
    }

    PPK_ASSERT_ALWAYS_INLINE const char* AssertionException::expression() const
    {
      return _expression;
    }

    namespace implementation {

    #if defined(_MSC_VER) && !defined(_CPPUNWIND)
      #if !defined(PPK_ASSERT_DISABLE_EXCEPTIONS)
        #define PPK_ASSERT_DISABLE_EXCEPTIONS
      #endif
    #endif

    #if !defined(PPK_ASSERT_DISABLE_EXCEPTIONS)

      template<typename E>
      inline void throwException(const E& e)
      {
        throw e;
      }

    #else

      // user defined, the behavior is undefined if the function returns
      void throwException(const pempek::assert::AssertionException& e);

    #endif

    namespace AssertLevel {

      enum AssertLevel
      {
        Warning = 32,
        Debug   = 64,
        Error   = 128,
        Fatal   = 256

      }; // AssertLevel

    } // AssertLevel

    namespace AssertAction {

      enum AssertAction
      {
        None,
        Abort,
        Break,
        Ignore,
      #if !defined(PPK_ASSERT_DISABLE_IGNORE_LINE)
        IgnoreLine,
      #endif
        IgnoreAll,
        Throw

      }; // AssertAction

    } // AssertAction

    typedef AssertAction::AssertAction (*AssertHandler)(const char* file,
                                                        int line,
                                                        const char* function,
                                                        const char* expression,
                                                        int level,
                                                        const char* message);


  #if defined(__GNUC__) || defined(__clang__)
    #define PPK_ASSERT_HANDLE_ASSERT_FORMAT __attribute__((format (printf, 7, 8)))
  #else
    #define PPK_ASSERT_HANDLE_ASSERT_FORMAT
  #endif

    AssertAction::AssertAction handleAssert(const char* file,
                                            int line,
                                            const char* function,
                                            const char* expression,
                                            int level,
                                            bool* ignoreLine,
                                            const char* message, ...) PPK_ASSERT_HANDLE_ASSERT_FORMAT;

    AssertHandler setAssertHandler(AssertHandler handler);

    void ignoreAllAsserts(bool value);
    bool ignoreAllAsserts();

  #if defined(PPK_ASSERT_CXX11)

    template<int level, typename T>
    class AssertUsedWrapper
    {
      public:
      AssertUsedWrapper(T&& t);
      ~AssertUsedWrapper() PPK_ASSERT_EXCEPTION_NO_THROW;

      operator T();

      private:
      const AssertUsedWrapper& operator = (const AssertUsedWrapper&); // not implemented on purpose (and only VS2013 supports deleted functions)

      T t;
      mutable bool used;

    }; // AssertUsedWrapper<int, T>

    template<int level, typename T>
    inline AssertUsedWrapper<level, T>::AssertUsedWrapper(T&& t)
      : t(std::forward<T>(t)), used(false)
    {}

    template<int level, typename T>
    inline AssertUsedWrapper<level, T>::operator T()
    {
      used = true;
      return std::move(t);
    }

    template<int level, typename T>
    inline AssertUsedWrapper<level, T>::~AssertUsedWrapper() PPK_ASSERT_EXCEPTION_NO_THROW
    {
      PPK_ASSERT_3(level, used, "unused value");
    }

  #else

    template<int level, typename T>
    class AssertUsedWrapper
    {
      public:
      AssertUsedWrapper(const T& t);
      AssertUsedWrapper(const AssertUsedWrapper& rhs);
      ~AssertUsedWrapper() PPK_ASSERT_EXCEPTION_NO_THROW;

      operator T() const;

      private:
      const AssertUsedWrapper& operator = (const AssertUsedWrapper&); // not implemented on purpose

      T t;
      mutable bool used;

    }; // AssertUsedWrapper<int, T>

    template<int level, typename T>
    PPK_ASSERT_ALWAYS_INLINE AssertUsedWrapper<level, T>::AssertUsedWrapper(const T& t)
      : t(t), used(false)
    {}

    template<int level, typename T>
    PPK_ASSERT_ALWAYS_INLINE AssertUsedWrapper<level, T>::AssertUsedWrapper(const AssertUsedWrapper& rhs)
      : t(rhs.t), used(rhs.used)
    {}

    // /!\ GCC is not so happy if we inline that destructor
    template<int level, typename T>
    AssertUsedWrapper<level, T>::~AssertUsedWrapper() PPK_ASSERT_EXCEPTION_NO_THROW
    {
      PPK_ASSERT_3(level, used, "unused value");
    }

    template<int level, typename T>
    PPK_ASSERT_ALWAYS_INLINE AssertUsedWrapper<level, T>::operator T() const
    {
      used = true;
      return t;
    }

  #endif

  } // namespace implementation

  } // namespace assert
  } // namespace pempek

#endif

#undef PPK_ASSERT_2
#undef PPK_ASSERT_USED_1
#undef PPK_ASSERT_USED_2

#if defined(_MSC_VER) && defined(_PREFAST_)

  #define PPK_ASSERT_2(level, expression, ...) __analysis_assume(!!(expression))
  #define PPK_ASSERT_USED_1(type)              type
  #define PPK_ASSERT_USED_2(level, type)       type

#elif defined(__clang__) && defined(__clang_analyzer__)

  void its_going_to_be_ok(bool expression) __attribute__((analyzer_noreturn));
  #define PPK_ASSERT_2(level, expression, ...) its_going_to_be_ok(!!(expression))
  #define PPK_ASSERT_USED_1(type)              type
  #define PPK_ASSERT_USED_2(level, type)       type

#else

  #if PPK_ASSERT_ENABLED

    #define PPK_ASSERT_2(level, expression, ...) PPK_ASSERT_3(level, expression, __VA_ARGS__)
    #define PPK_ASSERT_USED_1(type)              pempek::assert::implementation::AssertUsedWrapper<pempek::assert::implementation::AssertLevel::PPK_ASSERT_DEFAULT_LEVEL, type>
    #define PPK_ASSERT_USED_2(level, type)       pempek::assert::implementation::AssertUsedWrapper<level, type>

  #else

    #define PPK_ASSERT_2(level, expression, ...) PPK_ASSERT_UNUSED(expression)
    #define PPK_ASSERT_USED_1(type)              type
    #define PPK_ASSERT_USED_2(level, type)       type

  #endif

#endif

#if (defined(__GNUC__) && ((__GNUC__ * 1000 + __GNUC_MINOR__ * 100) >= 4600)) || defined(__clang__)
  #pragma GCC diagnostic pop
#endif
