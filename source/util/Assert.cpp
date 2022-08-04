//------------------------------------------------------------------------------
// Assert.cpp
// Contains assert-related utilities
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/util/Assert.h"

#include <fmt/format.h>

namespace slang::assert {

[[noreturn]] void assertFailed(const char* expr, const char* file, int line, const char* func) {
    throw AssertionException(fmt::format("Assertion '{}' failed\n  in file {}, line {}\n"
                                         "  function: {}\n",
                                         expr, file, line, func));
}

} // namespace slang::assert
