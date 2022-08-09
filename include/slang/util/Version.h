//------------------------------------------------------------------------------
//! @file Version.h
//! @brief Library build-time version information
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <string_view>

namespace slang {

/// Provides access to compile-time generated version info about the library.
class VersionInfo {
public:
    /// Gets the major version number of the library.
    static int getMajor();

    /// Gets the minor version number of the library.
    static int getMinor();

    /// Gets the patch version number of the library.
    static int getPatch();

    /// Gets a string describing the git hash of the library.
    static std::string_view getHash();
};

} // namespace slang
