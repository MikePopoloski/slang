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
#else
# include <unistd.h>
# include <dirent.h>
#endif
#include <sys/stat.h>

#if defined(__linux)
# include <linux/limits.h>
#else
# include <limits.h>
#endif

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
        elements(path.elements), pathType(path.pathType), absolute(path.absolute)
    {
    }

    Path(Path&& path) noexcept :
        elements(std::move(path.elements)), pathType(path.pathType), absolute(path.absolute)
    {
    }

    Path(const char* str) { set(str); }
    Path(const std::string& str) { set(str); }
    Path(string_view str) { set(string(str)); }

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
    bool exists() const;

    size_t fileSize() const;
    bool isDirectory() const;
    bool isFile() const;

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
    static Path makeAbsolute(const Path& path);

    /// Gets the process's current working directory.
    static Path getCurrentDirectory();

#if defined(_WIN32)
    std::wstring wstr(PathType type = NativePath) const;
    void set(const std::wstring& wstring, PathType type = NativePath);

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

/// Simple utility method to iterate all of the files in a given directory,
/// returning any that have the given extension (which should include the leading period).
/// If the extension provided is empty, all files will be returned. If @a recurse is set
/// to true, this will also look in subdirectories recursively.
vector<Path> findFiles(const Path& path, string_view extension = "", bool recurse = false);

}
