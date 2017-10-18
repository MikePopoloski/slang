//------------------------------------------------------------------------------
// Path.cpp
// Cross platform file path handling and directory iteration.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Path.h"

#include <cctype>
#include <cerrno>
#include <fstream>
#include <sstream>
#include <stdexcept>

#if defined(_WIN32)
#include "compat/windows.h"
#else
# include <unistd.h>
# include <dirent.h>
# include <fcntl.h>
#endif
#include <sys/stat.h>

#if defined(__linux)
# include <linux/limits.h>
#else
# include <limits.h>
#endif

namespace slang {

bool Path::exists() const {
#if defined(_WIN32)
    return GetFileAttributesW(wstr().c_str()) != INVALID_FILE_ATTRIBUTES;
#else
    struct stat sb;
    return stat(str().c_str(), &sb) == 0;
#endif
}

size_t Path::fileSize() const {
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

bool Path::isDirectory() const {
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

bool Path::isFile() const {
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

bool Path::readFile(vector<char>& buffer) const {
#if defined(_WIN32)
    size_t size;
    try {
        size = fileSize();
    }
    catch (std::runtime_error&) {
        return false;
    }

    // + 1 for null terminator
    buffer.resize((uint32_t)size + 1);
    std::ifstream stream(str(), std::ios::binary);
    stream.read(buffer.data(), size);

    // null-terminate the buffer while we're at it
    buffer[(uint32_t)size] = '\0';

    return stream.good();
#else

    // TODO: report error
    int fd = open(str().c_str(), O_RDONLY | O_CLOEXEC);
    if (fd == -1)
        return false;

    struct stat sb;
    if (fstat(fd, &sb) != 0) {
        close(fd);
        return false;
    }

    posix_fadvise(fd, 0, 0, POSIX_FADV_SEQUENTIAL);

    // TODO: vector does initialization always, which is dumb
    size_t remaining = sb.st_size;
    buffer.resize(remaining + 1);
    char* buf = buffer.data();

    while (remaining) {
        ssize_t r = ::read(fd, buf, remaining);
        if (r == -1) {
            close(fd);
            return false;
        }
        else if (r == 0) {
            buffer.resize((buf - buffer.data()) + 1);
            break;
        }
        else {
            buf += r;
            remaining -= r;
        }
    }

    close(fd);
    buffer.back() = '\0';
    return true;

#endif
}

string Path::str(PathType type) const {
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

void Path::set(const string& str, PathType type) {
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

Path Path::makeAbsolute(const Path& path) {
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

Path Path::getCurrentDirectory() {
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
std::wstring Path::wstr(PathType type) const {
    std::string temp = str(type);
    int size = MultiByteToWideChar(CP_UTF8, 0, &temp[0], (int)temp.size(), NULL, 0);
    std::wstring result(size, 0);
    MultiByteToWideChar(CP_UTF8, 0, &temp[0], (int)temp.size(), &result[0], size);
    return result;
}

void Path::set(const std::wstring& wstring, PathType type) {
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
#endif

template<typename CharType>
static void findFilesImpl(const Path& path, vector<Path>& results, const CharType* extension, bool recurse) {
    vector<Path> directories;

#if defined(_WIN32)
    WIN32_FIND_DATAW ffd;
    std::wstring base = path.wstr() + L"\\";
    HANDLE hFind = FindFirstFileW((base + L"*").c_str(), &ffd);
    if (hFind == INVALID_HANDLE_VALUE)
        throw std::runtime_error("Internal error in FindFirstFile(): " + std::to_string(GetLastError()));

    do {
        if ((ffd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) == 0) {
            const wchar_t* ext = wcsrchr(ffd.cFileName, '.');
            if (!extension || (ext && wcscmp(ext, extension) == 0))
                results.push_back(base + ffd.cFileName);
        }
        else if (wcscmp(ffd.cFileName, L".") != 0 && wcscmp(ffd.cFileName, L"..") != 0) {
            directories.push_back(base + ffd.cFileName);
        }
    } while (FindNextFileW(hFind, &ffd) != 0);

    DWORD dwError = GetLastError();
    if (dwError != ERROR_NO_MORE_FILES)
        throw std::runtime_error("Internal error in FindNextFile(): " + std::to_string(dwError));
    FindClose(hFind);
#else
    DIR* d;
    struct dirent* dir;
    string base = path.str();
    if (base.back() != '/')
        base += '/';

    d = opendir(base.c_str());
    if (d) {
        while ((dir = readdir(d))) {
            if (dir->d_type == DT_REG) {
                const char* ext = strrchr(dir->d_name, '.');
                if (!extension || (ext && strcmp(ext, extension) == 0))
                    results.push_back(base + dir->d_name);
            }
            else if (strcmp(dir->d_name, ".") != 0 && strcmp(dir->d_name, "..") != 0) {
                directories.push_back(base + dir->d_name);
            }
        }
        closedir(d);
    }
#endif

    if (recurse) {
        for (const auto& dir : directories)
            findFilesImpl(dir, results, extension, recurse);
    }
}

vector<Path> Path::findFiles(const Path& path, string_view extension, bool recurse) {
#if defined(_WIN32)
    std::wstring extensionCheck;
    if (!extension.empty()) {
        int size = MultiByteToWideChar(CP_UTF8, 0, extension.data(), (int)extension.length(), NULL, 0);
        extensionCheck.resize(size, 0);
        MultiByteToWideChar(CP_UTF8, 0, extension.data(), (int)extension.length(), &extensionCheck[0], size);
    }
#else
    string extensionCheck { extension };
#endif

    vector<Path> results;
    findFilesImpl(path, results, extensionCheck.c_str(), recurse);
    return results;
}

}
