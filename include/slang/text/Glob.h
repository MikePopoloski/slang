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

/// @brief Performs a file system "glob" operation to find paths matching
/// the given pattern.
///
/// The pattern is in the format described by the LRM 33.3.1, which follows
/// normal path syntax but allows for '?' and '*' wildcards, along with
/// '...' to mean recursive directory search.
///
/// @param basePath The path in which to search. If empty, uses the current working directory.
/// @param pattern The pattern to match against paths
/// @param mode The type of search to perform (either for files or for directories)
/// @param results The list of paths that matched the given pattern
/// @param expandEnvVars If true, environment variables references in the pattern will
///                      be expanded before searching. References can be of the form $VAR,
///                      $(VAR), and ${VAR}.
/// @param ec An error code that will be cleared on success and set to a value on failure.
///           Failure to match is only indicated when the pattern is an exact path with no
///           wildcards.
/// @returns A rank that indicates the strength of the match result.
///
SLANG_EXPORT GlobRank svGlob(const std::filesystem::path& basePath, std::string_view pattern,
                             GlobMode mode, SmallVector<std::filesystem::path>& results,
                             bool expandEnvVars, std::error_code& ec);

/// Checks whether the given path matches the supplied pattern.
SLANG_EXPORT bool svGlobMatches(const std::filesystem::path& path,
                                const std::filesystem::path& pattern);

} // namespace slang
