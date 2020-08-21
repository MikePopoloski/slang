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
#    include <unistd.h>
#endif

namespace slang {

#if defined(_MSC_VER)

bool OS::fileSupportsColors(int fd) {
    return fd == _fileno(stdout);
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

} // namespace slang
