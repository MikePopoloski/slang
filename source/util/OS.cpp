//------------------------------------------------------------------------------
// OS.cpp
// Operating system-specific utilities
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/util/OS.h"

#include "slang/text/CharInfo.h"

#if defined(_MSC_VER)
#    ifndef WIN32_LEAN_AND_MEAN
#        define WIN32_LEAN_AND_MEAN
#    endif
#    ifndef NOMINMAX
#        define NOMINMAX
#    endif
#    include <Windows.h>
#    include <fcntl.h>
#    include <io.h>
#else
#    include <unistd.h>
#endif

#include <fmt/color.h>
#include <fstream>

namespace fs = std::filesystem;

namespace slang {

#if defined(_MSC_VER)

bool OS::tryEnableColors() {
    auto tryEnable = [](DWORD handle) {
        HANDLE hOut = GetStdHandle(handle);
        if (hOut != INVALID_HANDLE_VALUE) {
            DWORD mode = 0;
            if (GetConsoleMode(hOut, &mode)) {
                mode |= ENABLE_VIRTUAL_TERMINAL_PROCESSING;
                if (SetConsoleMode(hOut, mode))
                    return true;
            }
        }
        return false;
    };

    bool result = tryEnable(STD_OUTPUT_HANDLE);
    result |= tryEnable(STD_ERROR_HANDLE);
    return result;
}

bool OS::fileSupportsColors(int fd) {
    auto handle = _get_osfhandle(fd);
    if (handle < 0)
        return false;

    DWORD mode = 0;
    if (!GetConsoleMode((HANDLE)handle, &mode))
        return false;

    return (mode & ENABLE_VIRTUAL_TERMINAL_PROCESSING) != 0;
}

bool OS::fileSupportsColors(FILE* file) {
    return fileSupportsColors(_fileno(file));
}

#else

bool OS::tryEnableColors() {
    return true;
}

bool OS::fileSupportsColors(int fd) {
#    ifdef __APPLE__
    return isatty(fd) && std::getenv("TERM") != nullptr;
#    else
    return isatty(fd);
#    endif
}

bool OS::fileSupportsColors(FILE* file) {
    return fileSupportsColors(fileno(file));
}

#endif

static const fs::path devNull("/dev/null");

bool OS::readFile(const fs::path& path, std::vector<char>& buffer) {
    std::error_code ec;
    fs::directory_entry entry(path, ec);
    if (!entry.exists(ec))
        return false;

    uintmax_t size = entry.file_size(ec);
    if (ec) {
        // The path exists but it's not a regular file with a known size.
        // As a special case, support reading from /dev/null (returns 0).
        if (path == devNull)
            size = 0;
        else
            return false;
    }

    // + 1 for null terminator
    buffer.resize((size_t)size + 1);
    std::ifstream stream(path, std::ios::binary);
    if (!stream.read(buffer.data(), (std::streamsize)size))
        return false;

    // null-terminate the buffer while we're at it
    size_t sz = (size_t)stream.gcount();
    buffer.resize(sz + 1);
    buffer[sz] = '\0';

    return true;
}

void OS::print(std::string_view text) {
    if (capturingOutput)
        capturedStdout += text;
    else
        fmt::detail::print(stdout, fmt::detail::to_string_view(text));
}

void OS::print(const fmt::text_style& style, std::string_view text) {
    if (capturingOutput)
        capturedStdout += text;
    else if (showColorsStdout)
        fmt::print(stdout, style, "{}"sv, text);
    else
        fmt::detail::print(stdout, fmt::detail::to_string_view(text));
}

void OS::printE(std::string_view text) {
    if (capturingOutput)
        capturedStderr += text;
    else
        fmt::detail::print(stderr, fmt::detail::to_string_view(text));
}

void OS::printE(const fmt::text_style& style, std::string_view text) {
    if (capturingOutput)
        capturedStderr += text;
    else if (showColorsStderr)
        fmt::print(stderr, style, "{}"sv, text);
    else
        fmt::detail::print(stderr, fmt::detail::to_string_view(text));
}

std::string OS::getEnv(const std::string& name) {
    char* result = getenv(name.c_str());
    if (result)
        return result;
    else
        return {};
}

std::string OS::parseEnvVar(const char*& ptr, const char* end) {
    // Three forms for environment variables to try:
    // $VAR
    // $(VAR)
    // ${VAR}
    char c = *ptr++;
    if (c == '(' || c == '{') {
        char startDelim = c;
        char endDelim = c == '(' ? ')' : '}';
        std::string varName;
        while (ptr != end) {
            c = *ptr++;
            if (c == endDelim)
                return OS::getEnv(varName);

            varName += c;
        }

        // If we reach the end, we didn't find a closing delimiter.
        // Don't try to expand, just return the whole thing we collected.
        return "$"s + startDelim + varName;
    }
    else if (isValidCIdChar(c)) {
        std::string varName;
        varName += c;
        while (ptr != end && isValidCIdChar(*ptr))
            varName += *ptr++;

        return OS::getEnv(varName);
    }
    else {
        // This is not a possible variable name so just return what we have.
        return "$"s + c;
    }
}

} // namespace slang
