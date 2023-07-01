//------------------------------------------------------------------------------
// Util.cpp
// Various utility functions and basic types used throughout the library
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/util/Util.h"

#include <fmt/core.h>

#if defined(SLANG_USE_MIMALLOC)
#    include <mimalloc-new-delete.h>
#endif

namespace slang::assert {

[[noreturn]] void assertFailed(const char* expr, const char* file, int line, const char* func) {
    auto msg = fmt::format("Assertion '{}' failed\n  in file {}, line {}\n"
                           "  function: {}\n",
                           expr, file, line, func);

#if __cpp_exceptions
    throw AssertionException(msg);
#else
    fprintf(stderr, "%s", msg.c_str());
    std::abort();
#endif
}

#if !__cpp_exceptions
[[noreturn]] void handleThrow(const char* msg, const char* file, int line, const char* func) {
    fprintf(stderr,
            "internal compiler error: '%s'\n  in file %s, line %d\n"
            "  function: %s\n",
            msg, file, line, func);
    std::abort();
}
#endif

[[noreturn]] void handleUnreachable(const char* file, int line, const char* func) {
    auto msg = fmt::format("Supposedly unreachable code was executed\n  in file {}, line {}\n"
                           "  function: {}\n",
                           file, line, func);

#if __cpp_exceptions
    throw std::logic_error(msg);
#else
    fprintf(stderr, "%s", msg.c_str());
    std::abort();
#endif
}

} // namespace slang::assert
