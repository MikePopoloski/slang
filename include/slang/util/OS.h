//------------------------------------------------------------------------------
//! @file OS.h
//! @brief Operating system-specific utilities
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/String.h"

namespace slang {

class OS {
public:
    static bool fileSupportsColors(int fd);
    static bool fileSupportsColors(FILE* file);

private:
    OS() = default;
};

} // namespace slang