//------------------------------------------------------------------------------
//! @file Assert.h
//! @brief Contains assert-related utilities
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <stdexcept>

#if !defined(ASSERT_ENABLED)
#    if !defined(NDEBUG)
#        define ASSERT_ENABLED 1
#    endif
#endif

#if ASSERT_ENABLED
#    if defined(__GNUC__) || defined(__clang__)
#        define ASSERT_FUNCTION __PRETTY_FUNCTION__
#    elif defined(_MSC_VER)
#        define ASSERT_FUNCTION __FUNCSIG__
#    elif defined(__SUNPRO_CC)
#        define ASSERT_FUNCTION __func__
#    else
#        define ASSERT_FUNCTION __FUNCTION__
#    endif
#    define ASSERT(cond)                                                                 \
        do {                                                                             \
            if (!(cond))                                                                 \
                slang::assert::assertFailed(#cond, __FILE__, __LINE__, ASSERT_FUNCTION); \
        } while (false)

#else
#    define ASSERT(cond)        \
        do {                    \
            (void)sizeof(cond); \
        } while (false)
#endif

#define THROW_UNREACHABLE                                                                  \
    throw std::logic_error(std::string(__FILE__) + ":" + std::to_string(__LINE__) + ": " + \
                           "Default case should be unreachable!")

// Compiler-specific macros for warnings and suppressions
#ifdef __clang__
#    define NO_SANITIZE(warningName) __attribute__((no_sanitize(warningName)))
#else
#    define NO_SANITIZE(warningName)
#endif

namespace slang::assert {

/// An exception thrown when an ASSERT condition fails.
class AssertionException : public std::logic_error {
public:
    AssertionException(const std::string& message) : std::logic_error(message) {}
};

/// A handler that runs when an ASSERT condition fails; it will unconditionally
/// thrown an exception.
[[noreturn]] void assertFailed(const char* expr, const char* file, int line, const char* func);

} // namespace slang::assert
