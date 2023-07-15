//------------------------------------------------------------------------------
//! @file Glob.h
//! @brief File name pattern globbing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <filesystem>

#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang {

/// @brief Classifies the ranking of a glob pattern
///
/// The LRM specifies that files that match patterns of a given
/// rank are preferred over those that match later ranks.
enum class GlobRank {
    /// A full match of an exact path without any wildcards.
    ExactPath,

    /// A plain textual name match.
    SimpleName,

    /// A name with wildcards.
    WildcardName,

    /// A directory name (and therefore all files
    /// within that directory implicitly included).
    Directory
};

/// The type of search to perform with a file system glob operation.
enum class GlobMode {
    /// Search for files
    Files,

    /// Search for directories
    Directories
};

/// Performs a file system "glob" operation to return all files underneath
/// @a basePath that match the given @a pattern string. The pattern is in
/// the format described by the LRM 33.3.1, which mostly matches other
/// glob implementations except for the use of '...' to mean recursive
/// directory match.
SLANG_EXPORT GlobRank svGlob(const std::filesystem::path& basePath, std::string_view pattern,
                             GlobMode mode, SmallVector<std::filesystem::path>& results,
                             bool expandEnvVars);

} // namespace slang
