//------------------------------------------------------------------------------
//! @file VersionInfo.h
//! @brief Library build-time version information
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <string>
#include <string_view>

#include "slang/slang_export.h"

namespace slang {

/// Provides access to compile-time generated version info about the library.
class SLANG_EXPORT VersionInfo {
public:
    /// Gets the major version number of the library.
    static int getMajor();

    /// Gets the minor version number of the library.
    static int getMinor();

    /// Gets the patch version number of the library.
    static int getPatch();

    /// Gets the pre-release version segment of the library, or an empty
    /// string if this is not a pre-release build.
    static std::string_view getPrerelease();

    /// Gets a string describing the git hash of the library.
    static std::string_view getHash();

    /// Gets the full version string of the library, formatted as
    /// `major.minor.patch[-prerelease]+hash`.
    static std::string getVersionString();
};

} // namespace slang
