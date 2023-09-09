//------------------------------------------------------------------------------
//! @file OS.h
//! @brief Operating system-specific utilities
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <filesystem>
#include <fmt/color.h>

#include "slang/util/ScopeGuard.h"
#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang {

/// A collection of various OS-specific utility functions.
class SLANG_EXPORT OS {
public:
    /// Does initial one-time setup of OS console.
    static void setupConsole();

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
    static std::error_code readFile(const std::filesystem::path& path, SmallVector<char>& buffer);

    /// Writes the given contents to the specified file.
    static void writeFile(const std::filesystem::path& path, std::string_view contents);

    /// Prints text to stdout.
    static void print(std::string_view text);

    /// Prints colored formatted text to stdout.
    static void print(const fmt::text_style& style, std::string_view text);

    /// Prints formatted text to stderr.
    static void printE(std::string_view text);

    /// Prints colored formatted text to stderr.
    static void printE(const fmt::text_style& style, std::string_view text);

    static std::string getEnv(const std::string& name);
    static std::string parseEnvVar(const char*& ptr, const char* end);

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
