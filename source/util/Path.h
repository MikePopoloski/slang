//------------------------------------------------------------------------------
// Path.h
// Cross platform file path handling and directory iteration.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <string>
#include <vector>
#include <stdexcept>
#include <sstream>
#include <cctype>
#include <cstdlib>
#include <cerrno>
#include <cstring>

#if defined(_WIN32)
# undef DEFAULT_UNREACHABLE
# define NOMINMAX
# include <windows.h>
# undef interface
# undef DEFAULT_UNREACHABLE
#else
# include <unistd.h>
# include <dirent.h>
#endif
#include <sys/stat.h>

#if defined(__linux)
# include <linux/limits.h>
#endif

#include "Debug.h"
#include "StringRef.h"

namespace slang {

/// Path - Cross platform file path manipulation routines.
/// This is loosely based on C++17 filesystem functionality, which is very
/// new and unimplemented on a bunch of systems.
class Path {
public:
    enum PathType {
        WindowsPath = 0,
        PosixPath = 1,
#if defined(_WIN32)
        NativePath = WindowsPath
#else
        NativePath = PosixPath
#endif
    };

    Path() {}

    Path(const Path& path) :
        pathType(path.pathType), elements(path.elements), absolute(path.absolute)
    {
    }

    Path(Path&& path) noexcept :
        pathType(path.pathType), elements(std::move(path.elements)), absolute(path.absolute)
    {
    }

    Path(const char* string) { set(string); }
    Path(const std::string& string) { set(string); }
    Path(StringRef string) { set(string.toString()); }

    // Paths in Win32 typically need UTF-16 characters
#if defined(_WIN32)
    Path(const std::wstring& wstring) { set(wstring); }
    Path(const wchar_t* wstring) { set(wstring); }
#endif

    /// Number of "elements" in the path, where an element is one directory or filename.
    size_t length() const { return elements.size(); }
    bool empty() const { return elements.empty(); }

    /// Is this an absolute path or a relative one?
    bool isAbsolute() const { return absolute; }

    /// Checks if the file exists; note that there is the typical IO race condition here.
    bool exists() const {
#if defined(_WIN32)
        return GetFileAttributesW(wstr().c_str()) != INVALID_FILE_ATTRIBUTES;
#else
        struct stat sb;
        return stat(str().c_str(), &sb) == 0;
#endif
    }

    size_t fileSize() const {
#if defined(_WIN32)
        struct _stati64 sb;
        if (_wstati64(wstr().c_str(), &sb) != 0)
            throw std::runtime_error("path::file_size(): cannot stat file \"" + str() + "\"!");
#else
        struct stat sb;
        if (stat(str().c_str(), &sb) != 0)
            throw std::runtime_error("path::file_size(): cannot stat file \"" + str() + "\"!");
#endif
        return (size_t)sb.st_size;
    }

    bool isDirectory() const {
#if defined(_WIN32)
        DWORD result = GetFileAttributesW(wstr().c_str());
        if (result == INVALID_FILE_ATTRIBUTES)
            return false;
        return (result & FILE_ATTRIBUTE_DIRECTORY) != 0;
#else
        struct stat sb;
        if (stat(str().c_str(), &sb))
            return false;
        return S_ISDIR(sb.st_mode);
#endif
    }

    bool isFile() const {
#if defined(_WIN32)
        DWORD attr = GetFileAttributesW(wstr().c_str());
        return (attr != INVALID_FILE_ATTRIBUTES && (attr & FILE_ATTRIBUTE_DIRECTORY) == 0);
#else
        struct stat sb;
        if (stat(str().c_str(), &sb))
            return false;
        return S_ISREG(sb.st_mode);
#endif
    }

    std::string extension() const {
        const std::string& name = filename();
        size_t pos = name.find_last_of(".");
        if (pos == std::string::npos)
            return "";
        return name.substr(pos + 1);
    }

    /// Gets the file name (including extension). If this isn't a path to a file,
    /// it returns the most nested directory name.
    std::string filename() const {
        if (empty())
            return "";
        return elements.back();
    }

    /// Goes up one level in the directory hierarchy.
    Path parentPath() const {
        Path result;
        result.absolute = absolute;

        if (elements.empty()) {
            if (!absolute)
                result.elements.push_back("..");
        }
        else {
            size_t until = elements.size() - 1;
            for (size_t i = 0; i < until; ++i)
                result.elements.push_back(elements[i]);
        }
        return result;
    }

    /// Concatenate two paths.
    Path operator+(const Path& other) const {
        if (other.absolute)
            throw std::runtime_error("path::operator+(): expected a relative path!");
        if (pathType != other.pathType)
            throw std::runtime_error("path::operator+(): expected a path of the same type!");

        Path result(*this);
        for (size_t i = 0; i < other.elements.size(); ++i)
            result.elements.push_back(other.elements[i]);

        return result;
    }

    std::string str(PathType type = NativePath) const {
        std::ostringstream oss;

        if (type == PosixPath && absolute)
            oss << "/";

        for (size_t i = 0; i < elements.size(); ++i) {
            oss << elements[i];
            if (i + 1 < elements.size()) {
                if (type == PosixPath)
                    oss << '/';
                else
                    oss << '\\';
            }
        }
        return oss.str();
    }

    void set(const std::string& str, PathType type = NativePath) {
        pathType = type;
        if (type == WindowsPath) {
            elements = tokenize(str, "/\\");
            absolute = str.size() >= 2 && std::isalpha(str[0]) && str[1] == ':';
        }
        else {
            elements = tokenize(str, "/");
            absolute = !str.empty() && str[0] == '/';
        }
    }

    Path& operator=(const Path& path) {
        pathType = path.pathType;
        elements = path.elements;
        absolute = path.absolute;
        return *this;
    }

    Path& operator=(Path&& path) noexcept {
        if (this != &path) {
            pathType = path.pathType;
            elements = std::move(path.elements);
            absolute = path.absolute;
        }
        return *this;
    }

    bool operator==(const Path& p) const { return p.elements == elements; }
    bool operator!=(const Path& p) const { return p.elements != elements; }
    bool operator<(const Path& p) const { return elements < p.elements; }

    friend std::ostream& operator<<(std::ostream& os, const Path& path) {
        os << path.str();
        return os;
    }

    /// Convert a relative path to an absolute one.
    static Path makeAbsolute(const Path& path) {
#if !defined(_WIN32)
        char temp[PATH_MAX];
        if (realpath(path.str().c_str(), temp) == nullptr)
            throw std::runtime_error("Internal error in realpath(): " + std::string(strerror(errno)));
        return Path(temp);
#else
        std::wstring value = path.wstr();
        std::wstring out(MAX_PATH, '\0');
        DWORD length = GetFullPathNameW(value.c_str(), MAX_PATH, &out[0], nullptr);
        if (length == 0)
            throw std::runtime_error("Internal error in GetFullPathNameW(): " + std::to_string(GetLastError()));
        return Path(out.substr(0, length));
#endif
    }

    /// Gets the process's current working directory.
    static Path getCurrentDirectory() {
#if !defined(_WIN32)
        char temp[PATH_MAX];
        if (::getcwd(temp, PATH_MAX) == NULL)
            throw std::runtime_error("Internal error in getcwd(): " + std::string(strerror(errno)));
        return Path(temp);
#else
        std::wstring temp(MAX_PATH, '\0');
        if (!_wgetcwd(&temp[0], MAX_PATH))
            throw std::runtime_error("Internal error in _wgetcwd(): " + std::to_string(GetLastError()));
        return Path(temp.c_str());
#endif
    }

#if defined(_WIN32)
    std::wstring wstr(PathType type = NativePath) const {
        std::string temp = str(type);
        int size = MultiByteToWideChar(CP_UTF8, 0, &temp[0], (int)temp.size(), NULL, 0);
        std::wstring result(size, 0);
        MultiByteToWideChar(CP_UTF8, 0, &temp[0], (int)temp.size(), &result[0], size);
        return result;
    }


    void set(const std::wstring& wstring, PathType type = NativePath) {
        std::string string;
        if (!wstring.empty()) {
            int size = WideCharToMultiByte(CP_UTF8, 0, &wstring[0], (int)wstring.size(),
                NULL, 0, NULL, NULL);
            string.resize(size, 0);
            WideCharToMultiByte(CP_UTF8, 0, &wstring[0], (int)wstring.size(),
                &string[0], size, NULL, NULL);
        }
        set(string, type);
    }

    Path& operator=(const std::wstring& str) { set(str); return *this; }
#endif

private:
    static std::vector<std::string> tokenize(const std::string& string, const std::string& delim) {
        std::string::size_type lastPos = 0, pos = string.find_first_of(delim, lastPos);
        std::vector<std::string> tokens;

        while (lastPos != std::string::npos) {
            if (pos != lastPos)
                tokens.push_back(string.substr(lastPos, pos - lastPos));
            lastPos = pos;
            if (lastPos == std::string::npos || lastPos + 1 == string.length())
                break;
            pos = string.find_first_of(delim, ++lastPos);
        }

        return tokens;
    }

    std::vector<std::string> elements;
    PathType pathType = NativePath;
    bool absolute = false;
};

/// Simple utility method to iterate all of the files in a given directory. Note that the
/// entire set is realized in one go; you may want something smarter if you only need to
/// look at a few entries.
inline std::vector<Path> getFilesInDirectory(const Path& path) {
    std::vector<Path> result;

#if defined(_WIN32)
    WIN32_FIND_DATA ffd;
    std::wstring base = path.wstr() + L"\\";
    HANDLE hFind = FindFirstFile((base + +L"*").c_str(), &ffd);
    if (hFind == INVALID_HANDLE_VALUE)
        throw std::runtime_error("Internal error in FindFirstFile(): " + std::to_string(GetLastError()));

    do {
        if ((ffd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) == 0)
            result.push_back(base + ffd.cFileName);
    } while (FindNextFile(hFind, &ffd) != 0);

    DWORD dwError = GetLastError();
    if (dwError != ERROR_NO_MORE_FILES)
        throw std::runtime_error("Internal error in FindNextFile(): " + std::to_string(dwError));

    FindClose(hFind);
#else
    DIR* d;
    struct dirent* dir;
    std::string base = path.str() + "/";
    d = opendir(base.c_str());
    if (d) {
        while ((dir = readdir(d))) {
            if (dir->d_type == DT_REG)
                result.push_back(base + dir->d_name);
        }
        closedir(d);
    }
#endif

    return result;
}

}
