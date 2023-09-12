//------------------------------------------------------------------------------
// OS.cpp
// Operating system-specific utilities
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/util/OS.h"

#include <iostream>

#include "slang/text/CharInfo.h"

#if defined(_WIN32)
#    ifndef WIN32_LEAN_AND_MEAN
#        define WIN32_LEAN_AND_MEAN
#    endif
#    ifndef NOMINMAX
#        define NOMINMAX
#    endif
#    ifndef STRICT
#        define STRICT
#    endif
#    include <Windows.h>
#    include <fcntl.h>
#    include <io.h>
#else
#    include <fcntl.h>
#    include <sys/stat.h>
#    include <unistd.h>
#endif

#include <fmt/color.h>
#include <fstream>

namespace fs = std::filesystem;

namespace slang {

#if defined(_WIN32)

void OS::setupConsole() {
    // The application needs to be built with a manifest
    // specifying the ActiveCodePage as UTF-8.
    SLANG_ASSERT(GetACP() == 65001);

    SetConsoleCP(CP_UTF8);
    SetConsoleOutputCP(CP_UTF8);
    setvbuf(stdout, nullptr, _IOFBF, 1000);
}

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

std::error_code OS::readFile(const fs::path& path, SmallVector<char>& buffer) {
    HANDLE handle;
    auto& pathStr = path.native();
    const bool isStdin = pathStr == L"-";

    if (isStdin) {
        _setmode(_fileno(stdin), _O_BINARY);
        handle = ::GetStdHandle(STD_INPUT_HANDLE);
    }
    else {
        handle = ::CreateFileW(pathStr.c_str(), GENERIC_READ,
                               FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, NULL,
                               OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL | FILE_FLAG_SEQUENTIAL_SCAN,
                               NULL);
        if (handle == INVALID_HANDLE_VALUE) {
            // Provide a better error when trying to open directories.
            std::error_code ec;
            DWORD lastErr = ::GetLastError();
            if (lastErr == ERROR_ACCESS_DENIED && fs::is_directory(path, ec))
                return make_error_code(std::errc::is_a_directory);

            return std::error_code(lastErr, std::system_category());
        }
    }

    std::error_code ec;
    DWORD fileType = ::GetFileType(handle);
    if (fileType == FILE_TYPE_DISK) {
        BY_HANDLE_FILE_INFORMATION fileInfo;
        if (!::GetFileInformationByHandle(handle, &fileInfo)) {
            ec.assign(::GetLastError(), std::system_category());
        }
        else {
            size_t fileSize = (size_t(fileInfo.nFileSizeHigh) << 32) + fileInfo.nFileSizeLow;
            buffer.resize_for_overwrite(fileSize + 1);

            char* buf = buffer.data();
            while (fileSize) {
                DWORD bytesToRead = (DWORD)std::min(size_t(std::numeric_limits<DWORD>::max()),
                                                    fileSize);
                DWORD bytesRead = 0;
                if (!::ReadFile(handle, buf, bytesToRead, &bytesRead, NULL)) {
                    ec.assign(::GetLastError(), std::system_category());
                    break;
                }

                buf += bytesRead;
                fileSize -= bytesRead;
                if (bytesRead == 0) {
                    // We reached the end of the file early -- it must have been
                    // truncated by someone else.
                    buffer.resize((buf - buffer.data()) + 1);
                    break;
                }
            }

            buffer.back() = '\0';
        }
    }
    else if (DWORD lastErr = ::GetLastError(); lastErr != NO_ERROR) {
        ec.assign(lastErr, std::system_category());
    }
    else {
        static constexpr DWORD ChunkSize = 4 * 4096;

        size_t currSize = 0;
        while (true) {
            buffer.resize_for_overwrite(currSize + ChunkSize + 1);

            DWORD bytesRead = 0;
            BOOL result = ::ReadFile(handle, buffer.data() + currSize, ChunkSize, &bytesRead, NULL);

            currSize += bytesRead;
            if (!result) {
                lastErr = ::GetLastError();
                if (lastErr != ERROR_BROKEN_PIPE && lastErr != ERROR_HANDLE_EOF)
                    ec.assign(lastErr, std::system_category());
                break;
            }
        }

        buffer.resize(currSize + 1);
        buffer.back() = '\0';
    }

    if (!isStdin) {
        if (!::CloseHandle(handle) && !ec)
            ec.assign(::GetLastError(), std::system_category());
    }

    return ec;
}

#else

void OS::setupConsole() {
    // Nothing to do.
}

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

std::error_code OS::readFile(const fs::path& path, SmallVector<char>& buffer) {
    int fd;
    auto& pathStr = path.native();
    const bool isStdin = pathStr == "-";

    if (isStdin) {
        fd = STDIN_FILENO;
    }
    else {
        while (true) {
            fd = ::open(pathStr.c_str(), O_RDONLY | O_CLOEXEC);
            if (fd >= 0)
                break;

            if (errno != EINTR)
                return std::error_code(errno, std::generic_category());
        }
    }

    std::error_code ec;
    struct stat status;
    if (::fstat(fd, &status) != 0) {
        ec.assign(errno, std::generic_category());
    }
    else if (S_ISREG(status.st_mode) || S_ISBLK(status.st_mode)) {
        auto fileSize = (size_t)status.st_size;
        buffer.resize_for_overwrite(fileSize + 1);

        char* buf = buffer.data();
        while (fileSize) {
            size_t bytesToRead = std::min(fileSize, size_t(INT32_MAX));
            ssize_t numRead = ::read(fd, buf, bytesToRead);
            if (numRead < 0) {
                if (errno == EINTR)
                    continue;

                ec.assign(errno, std::generic_category());
                break;
            }

            buf += numRead;
            fileSize -= (size_t)numRead;
            if (numRead == 0) {
                // We reached the end of the file early -- it must have been
                // truncated by someone else.
                buffer.resize(size_t(buf - buffer.data()) + 1);
                break;
            }
        }

        buffer.back() = '\0';
    }
    else {
        static constexpr size_t ChunkSize = 4 * 4096;

        size_t currSize = 0;
        while (true) {
            buffer.resize_for_overwrite(currSize + ChunkSize + 1);

            ssize_t numRead = ::read(fd, buffer.data() + currSize, ChunkSize);
            if (numRead < 0) {
                if (errno == EINTR)
                    continue;

                ec.assign(errno, std::generic_category());
                break;
            }

            currSize += (size_t)numRead;
            if (numRead == 0)
                break;
        }

        buffer.resize(currSize + 1);
        buffer.back() = '\0';
    }

    if (!isStdin) {
        if (::close(fd) < 0 && !ec)
            ec.assign(errno, std::generic_category());
    }

    return ec;
}

#endif

void OS::writeFile(const fs::path& path, std::string_view contents) {
    if (path == "-") {
        std::cout.write(contents.data(), (std::streamsize)contents.size());
        std::cout.flush();
    }
    else {
        std::ofstream file(path);
        file.exceptions(std::ios::failbit | std::ios::badbit);
        file.write(contents.data(), (std::streamsize)contents.size());
        file.flush();
    }
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
