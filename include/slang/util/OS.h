//------------------------------------------------------------------------------
//! @file OS.h
//! @brief Operating system-specific utilities
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <fmt/format.h>

#include "slang/util/String.h"

namespace slang {

class OS {
public:
    static bool fileSupportsColors(int fd);
    static bool fileSupportsColors(FILE* file);

#if defined(_MSC_VER)
    template<typename... Args>
    static void print(string_view format, const Args&... args) {
        fmt::vprint(fmt::to_string_view(widen(format)),
                    fmt::make_format_args<fmt::wformat_context>(convert(args)...));
    }
#else
    template<typename... Args>
    static void print(string_view format, const Args&... args) {
        fmt::vprint(format, fmt::make_format_args(args...));
    }
#endif

private:
    OS() = default;

#if defined(_MSC_VER)
    template<typename T>
    static T convert(T&& t) {
        return std::forward<T>(t);
    }

    static std::wstring convert(const std::string& s) { return widen(s); }
    static std::wstring convert(const std::string_view& s) { return widen(s); }
    static std::wstring convert(const char* s) { return widen(s); }
#endif
};

} // namespace slang