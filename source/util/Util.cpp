//------------------------------------------------------------------------------
// Util.h
// Various utility functions and basic types used throughout the library.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/util/Util.h"

#include <fmt/format.h>

#if defined(_MSC_VER)
#    include <Windows.h>
#endif

namespace slang::assert {

[[noreturn]] void assertFailed(const char* expr, const char* file, int line, const char* func) {
    throw AssertionException(fmt::format("Assertion '{}' failed\n  in file {}, line {}\n"
                                         "  function: {}\n",
                                         expr, file, line, func));
}

} // namespace slang::assert

namespace slang {

#if defined(_MSC_VER)

std::wstring widen(string_view str) {
    if (str.empty())
        return L"";

    int sz = MultiByteToWideChar(CP_UTF8, 0, str.data(), (int)str.size(), NULL, 0);
    if (sz <= 0)
        throw std::runtime_error("Failed to convert string to UTF16");

    std::wstring result;
    result.resize(sz);

    MultiByteToWideChar(CP_UTF8, 0, str.data(), (int)str.length(), result.data(), sz);
    return result;
}

std::string narrow(std::wstring_view str) {
    if (str.empty())
        return "";

    int sz = WideCharToMultiByte(CP_UTF8, 0, str.data(), (int)str.size(), NULL, 0, NULL, NULL);
    if (sz <= 0)
        throw std::runtime_error("Failed to convert string to UTF8");

    std::string result;
    result.resize(sz);

    WideCharToMultiByte(CP_UTF8, 0, str.data(), (int)str.size(), result.data(), sz, NULL, NULL);
    return result;
}

#endif

} // namespace slang