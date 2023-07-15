//------------------------------------------------------------------------------
// Glob.cpp
// File name pattern globbing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/text/Glob.h"

#include "slang/util/Hash.h"
#include "slang/util/OS.h"
#include "slang/util/String.h"

namespace fs = std::filesystem;

namespace slang {

static bool matches(std::string_view str, std::string_view pattern) {
    while (true) {
        // Empty pattern matches empty string.
        if (pattern.empty())
            return str.empty();

        // If next pattern char is '*' try to match pattern[1..] against
        // all possible tail strings of str to see if at least one succeeds.
        if (pattern[0] == '*') {
            // Simple case: if pattern is just '*' it matches anything.
            pattern = pattern.substr(1);
            if (pattern.empty())
                return true;

            for (size_t i = 0, end = str.size(); i < end; i++) {
                if (matches(str.substr(i), pattern))
                    return true;
            }
            return false;
        }

        // If pattern char isn't '*' then it must consume one character.
        if (str.empty())
            return false;

        // '?' matches any character, otherwise we need exact match.
        if (str[0] != pattern[0] && pattern[0] != '?')
            return false;

        str = str.substr(1);
        pattern = pattern.substr(1);
    }
}

static void iterDirectory(const fs::path& path, SmallVector<fs::path>& results, GlobMode mode) {
    std::error_code ec;
    for (auto it = fs::directory_iterator(path.empty() ? "." : path,
                                          fs::directory_options::follow_directory_symlink |
                                              fs::directory_options::skip_permission_denied,
                                          ec);
         it != fs::directory_iterator(); it.increment(ec)) {
        auto status = it->status(ec);
        if ((mode == GlobMode::Files && it->is_regular_file(ec)) ||
            (mode == GlobMode::Directories && it->is_directory(ec))) {
            results.emplace_back(it->path());
        }
    }
}

static void iterDirectoriesRecursive(const fs::path& path, SmallVector<fs::path>& results,
                                     flat_hash_set<std::string>& visited) {
    SmallVector<fs::path> local;
    iterDirectory(path, local, GlobMode::Directories);

    results.reserve(results.size() + local.size());
    for (auto& p : local) {
        // Avoid recursing into directories we've already visited (via symlinks).
        std::error_code ec;
        fs::path canonical = fs::weakly_canonical(p, ec);

        if (visited.emplace(getU8Str(canonical)).second) {
            iterDirectoriesRecursive(canonical, results, visited);
            results.emplace_back(std::move(canonical));
        }
    }
}

static void globDir(const fs::path& path, std::string_view pattern, SmallVector<fs::path>& results,
                    GlobMode mode) {
    SmallVector<fs::path> local;
    iterDirectory(path, local, mode);

    results.reserve(results.size() + local.size());
    for (auto&& p : local) {
        if (matches(narrow(p.filename().native()), pattern))
            results.emplace_back(std::move(p));
    }
}

GlobRank svGlobInternal(const fs::path& basePath, std::string_view pattern, GlobMode mode,
                        SmallVector<fs::path>& results) {
    // Parse the pattern. Consume directories in chunks until
    // we find one that has wildcards for us to handle.
    auto currPath = basePath;
    while (!pattern.empty()) {
        // The '...' pattern only applies at the start of a segment,
        // and means to recursively pull all directories.
        if (pattern.starts_with("..."sv)) {
            SmallVector<fs::path> dirs;
            flat_hash_set<std::string> visited;
            iterDirectoriesRecursive(currPath, dirs, visited);
            dirs.emplace_back(std::move(currPath));

            pattern = pattern.substr(3);

            auto rank = GlobRank::Directory;
            for (auto& dir : dirs)
                rank = svGlobInternal(dir, pattern, mode, results);
            return rank;
        }

        bool hasWildcards = false;
        bool foundDir = false;
        for (size_t i = 0; i < pattern.size(); i++) {
            char c = pattern[i];
            hasWildcards |= (c == '?' || c == '*');
            if (c == fs::path::preferred_separator) {
                auto subPattern = pattern.substr(0, i);
                pattern = pattern.substr(i + 1);

                // If this directory entry had wildcards we need to expand them
                // and recursively search within each expanded directory.
                if (hasWildcards) {
                    SmallVector<fs::path> dirs;
                    globDir(currPath, subPattern, dirs, GlobMode::Directories);

                    auto rank = GlobRank::Directory;
                    for (auto& dir : dirs)
                        rank = svGlobInternal(dir, pattern, mode, results);
                    return rank;
                }

                // Otherwise just record this directory and move on to the next.
                foundDir = true;
                currPath /= subPattern;
                break;
            }
        }

        // We didn't find a directory separator, so we're going to consume
        // the remainder of the pattern and search for files/directories with
        // that pattern.
        if (!foundDir) {
            if (hasWildcards) {
                globDir(currPath, pattern, results, mode);
                return GlobRank::WildcardName;
            }

            // Check for an exact match and add the target if we find it.
            std::error_code ec;
            currPath /= pattern;

            if (!pattern.empty() && mode == GlobMode::Directories)
                currPath /= "";

            if ((mode == GlobMode::Files && fs::is_regular_file(currPath, ec)) ||
                (mode == GlobMode::Directories && fs::is_directory(currPath, ec))) {
                results.emplace_back(std::move(currPath));
            }

            return GlobRank::ExactName;
        }
    }

    // If we reach this point, we either had an empty pattern to
    // begin with or we consumed the whole pattern and it had a trailing
    // directory separator. If we are search for files we want to include
    // all files underneath the directory pointed to by currPath, and if
    // we're searching for directories we'll just take this directory.
    if (mode == GlobMode::Files)
        iterDirectory(currPath, results, GlobMode::Files);
    else {
        if (pattern.empty())
            currPath /= "";
        results.emplace_back(std::move(currPath));
    }
    return GlobRank::Directory;
}

SLANG_EXPORT GlobRank svGlob(const fs::path& basePath, std::string_view pattern, GlobMode mode,
                             SmallVector<fs::path>& results, bool expandEnvVars) {
    fs::path patternPath;
    if (expandEnvVars) {
        std::string patternStr;
        patternStr.reserve(pattern.size());

        auto ptr = pattern.data();
        auto end = ptr + pattern.size();
        while (ptr != end) {
            char c = *ptr++;
            if (c == '$' && ptr != end)
                patternStr.append(OS::parseEnvVar(ptr, end));
            else
                patternStr.push_back(c);
        }

        patternPath = fs::path(widen(patternStr));
    }
    else {
        patternPath = fs::path(widen(pattern));
    }

    // Normalize the path to remove duplicate separators, figure out
    // whether we have an absolute path, etc.
    patternPath = patternPath.lexically_normal();

    SmallVector<fs::path> local;
    GlobRank rank;
    if (patternPath.has_root_path()) {
        rank = svGlobInternal(patternPath.root_path(), narrow(patternPath.relative_path().native()),
                              mode, local);
    }
    else {
        rank = svGlobInternal(basePath, narrow(patternPath.native()), mode, local);
    }

    // Results paths are always made canonical.
    std::error_code ec;
    results.reserve(local.size());
    for (auto& p : local)
        results.emplace_back(fs::weakly_canonical(p, ec));

    return rank;
}

} // namespace slang
