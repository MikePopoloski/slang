//------------------------------------------------------------------------------
//! @file OS.h
//! @brief Operating system-specific utilities
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <filesystem>
#include <fmt/color.h>
#include <vector>

#include "slang/util/ScopeGuard.h"
#include "slang/util/String.h"

namespace slang {

/// A collection of various OS-specific utility functions.
class OS {
public:
    /// Tries to enable color output support for stdout and stderr.
    /// @return true if successful and false otherwise.
    static bool tryEnableColors();

    /// @return true if the given file descriptor supports color text output.
    static bool fileSupportsColors(int fd);

    /// @return true if the given FILE supports color text output.
    static bool fileSupportsColors(FILE* file);

    /// Sets whether color output should be enabled for the print() functions.
    /// This is off by default.
    static void setStdoutColorsEnabled(bool enabled) { showColorsStdout = enabled; }
    static void setStderrColorsEnabled(bool enabled) { showColorsStderr = enabled; }

    /// Reads a file from @a path into memory. If successful, the bytes are placed
    /// into @a buffer -- otherwise, returns false.
    /// Note that the buffer will be null-terminated.
    static bool readFile(const std::filesystem::path& path, std::vector<char>& buffer);

    /// Prints formatted text to stdout, handling Unicode conversions where necessary.
    template<typename... Args>
    static void print(string_view format, const Args&... args) {
        if (capturingOutput) {
            capturedStdout += fmt::vformat(format, fmt::make_format_args(args...));
        }
        else {
            fmt::vprint(stdout, format, fmt::make_format_args(args...));
        }
    }

    /// Prints colored formatted text to stdout, handling Unicode conversions where necessary.
    template<typename... Args>
    static void print(const fmt::text_style& style, string_view format, const Args&... args) {
        if (capturingOutput) {
            capturedStdout += fmt::vformat(format, fmt::make_format_args(args...));
        }
        else if (showColorsStdout) {
            fmt::vprint(stdout, style, format, fmt::make_format_args(args...));
        }
        else {
            fmt::vprint(stdout, format, fmt::make_format_args(args...));
        }
    }

    /// Prints formatted text to stderr, handling Unicode conversions where necessary.
    template<typename... Args>
    static void printE(string_view format, const Args&... args) {
        if (capturingOutput) {
            capturedStderr += fmt::vformat(format, fmt::make_format_args(args...));
        }
        else {
            fmt::vprint(stderr, format, fmt::make_format_args(args...));
        }
    }

    /// Prints colored formatted text to stderr, handling Unicode conversions where necessary.
    template<typename... Args>
    static void printE(const fmt::text_style& style, string_view format, const Args&... args) {
        if (capturingOutput) {
            capturedStderr += fmt::vformat(format, fmt::make_format_args(args...));
        }
        else if (showColorsStderr) {
            fmt::vprint(stderr, style, format, fmt::make_format_args(args...));
        }
        else {
            fmt::vprint(stderr, format, fmt::make_format_args(args...));
        }
    }

    static auto captureOutput() {
        capturedStdout.clear();
        capturedStderr.clear();

        capturingOutput = true;
        return ScopeGuard([] { capturingOutput = false; });
    }

    static inline std::string capturedStdout;
    static inline std::string capturedStderr;

private:
    OS() = default;

    static inline bool showColorsStdout = false;
    static inline bool showColorsStderr = false;
    static inline bool capturingOutput = false;
};

} // namespace slang
