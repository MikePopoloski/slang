//------------------------------------------------------------------------------
//! @file Assert.h
//! @brief Contains assert-related utilities
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <stdexcept>

#include "slang/slang_export.h"

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

#    define ASSUME_UNREACHABLE                                                                 \
        throw std::logic_error(std::string(__FILE__) + ":" + std::to_string(__LINE__) + ": " + \
                               "Default case should be unreachable!")

#else
#    define ASSERT(cond)        \
        do {                    \
            (void)sizeof(cond); \
        } while (false)

#    if defined(__GNUC__) || defined(__clang__)
#        define ASSUME_UNREACHABLE __builtin_unreachable()
#    elif defined(_MSC_VER)
#        define ASSUME_UNREACHABLE __assume(false)
#    else
#        define ASSUME_UNREACHABLE
#    endif

#endif

// Compiler-specific macros for warnings and suppressions
#ifdef __clang__
#    define NO_SANITIZE(warningName) __attribute__((no_sanitize(warningName)))
#else
#    define NO_SANITIZE(warningName)
#endif

namespace slang::assert {

/// An exception thrown when an ASSERT condition fails.
class SLANG_EXPORT AssertionException : public std::logic_error {
public:
    AssertionException(const std::string& message) : std::logic_error(message) {}
};

/// A handler that runs when an ASSERT condition fails; it will unconditionally
/// thrown an exception.
[[noreturn]] SLANG_EXPORT void assertFailed(const char* expr, const char* file, int line,
                                            const char* func);

} // namespace slang::assert
