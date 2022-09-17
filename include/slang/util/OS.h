//------------------------------------------------------------------------------
//! @file OS.h
//! @brief Operating system-specific utilities
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <filesystem>
#include <vector>

#include "slang/util/ScopeGuard.h"
#include "slang/util/String.h"

namespace fmt {
inline namespace v9 {
class text_style;
}
} // namespace fmt

namespace slang {

/// A collection of various OS-specific utility functions.
class SLANG_EXPORT OS {
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

    /// Prints text to stdout.
    static void print(string_view text);

    /// Prints colored formatted text to stdout.
    static void print(const fmt::text_style& style, string_view text);

    /// Prints formatted text to stderr.
    static void printE(string_view text);

    /// Prints colored formatted text to stderr.
    static void printE(const fmt::text_style& style, string_view text);

    static std::string getEnv(const std::string& name);

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
