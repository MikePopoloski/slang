//------------------------------------------------------------------------------
// OS.cpp
// Operating system-specific utilities
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/util/OS.h"

#if defined(_MSC_VER)
#    include <fcntl.h>
#    include <io.h>
#else
#    include <sys/stat.h>
#    include <unistd.h>
#endif

#include <fstream>

namespace fs = std::filesystem;

namespace slang {

#if defined(_MSC_VER)

bool OS::fileSupportsColors(int fd) {
    return fd == _fileno(stdout) || fd == _fileno(stderr);
}

bool OS::fileSupportsColors(FILE* file) {
    return fileSupportsColors(_fileno(file));
}

#else

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

bool OS::readFile(const fs::path& path, std::vector<char>& buffer) {
#if defined(_MSC_VER)
    std::error_code ec;
    uintmax_t size = fs::file_size(path, ec);
    if (ec)
        return false;
#else
    struct stat s;
    int ec = ::stat(path.string().c_str(), &s);
    if (ec != 0 || s.st_size < 0)
        return false;

    uintmax_t size = uintmax_t(s.st_size);
#endif

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

} // namespace slang
