//------------------------------------------------------------------------------
//! @file OS.h
//! @brief Operating system-specific utilities
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <fmt/color.h>

#include "slang/util/String.h"

namespace slang {

/// A collection of various OS-specific utility functions.
class OS {
public:
    /// @return true if the given file descriptor supports color text output.
    static bool fileSupportsColors(int fd);

    /// @return true if the given FILE supports color text output.
    static bool fileSupportsColors(FILE* file);

    /// Sets whether color output should be enabled for the print() functions.
    /// This is off by default.
    static void setColorsEnabled(bool enabled) { showColors = enabled; }

#if defined(_MSC_VER)
    /// Prints formatted text to stdout, handling Unicode conversions where necessary.
    template<typename... Args>
    static void print(string_view format, const Args&... args) {
        fmt::vprint(fmt::to_string_view(widen(format)),
                    fmt::make_format_args<fmt::wformat_context>(convert(args)...));
    }

    /// Prints colored formatted text to stdout, handling Unicode conversions where necessary.
    template<typename... Args>
    static void print(const fmt::text_style& style, string_view format, const Args&... args) {
        if (showColors) {
            fmt::vprint(stdout, style, fmt::to_string_view(widen(format)),
                        fmt::make_format_args<fmt::wformat_context>(convert(args)...));
        }
        else {
            fmt::vprint(fmt::to_string_view(widen(format)),
                        fmt::make_format_args<fmt::wformat_context>(convert(args)...));
        }
    }
#else
    /// Prints formatted text to stdout, handling Unicode conversions where necessary.
    template<typename... Args>
    static void print(string_view format, const Args&... args) {
        fmt::vprint(format, fmt::make_format_args(args...));
    }

    /// Prints colored formatted text to stdout, handling Unicode conversions where necessary.
    template<typename... Args>
    static void print(const fmt::text_style& style, string_view format, const Args&... args) {
        if (showColors) {
            fmt::vprint(stdout, style, format, fmt::make_format_args(args...));
        }
        else {
            fmt::vprint(format, fmt::make_format_args(args...));
        }
    }
#endif

private:
    OS() = default;

    static inline bool showColors = false;

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
