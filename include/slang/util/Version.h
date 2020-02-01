//------------------------------------------------------------------------------
//! @file Version.h
//! @brief Library build-time version information
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <string_view>

namespace slang {

class VersionInfo {
public:
    static int getMajor();
    static int getMinor();
    static std::string_view getRevision();
};

} // namespace slang