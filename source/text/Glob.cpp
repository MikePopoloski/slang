//------------------------------------------------------------------------------
// Glob.cpp
// File name pattern globbing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
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

enum class SearchMode { Files, Directories };

static void iterDirectory(const fs::path& path, SmallVector<fs::path>& results,
                          SearchMode searchMode) {
    std::error_code ec;
    for (auto& entry : fs::directory_iterator(path.empty() ? "." : path,
                                              fs::directory_options::follow_directory_symlink |
                                                  fs::directory_options::skip_permission_denied,
                                              ec)) {
        if ((searchMode == SearchMode::Files && entry.is_regular_file(ec)) ||
            (searchMode == SearchMode::Directories && entry.is_directory(ec))) {
            results.emplace_back(entry.path());
        }
    }
}

static void iterDirectoriesRecursive(const fs::path& path, SmallVector<fs::path>& results) {
    SmallVector<fs::path> local;
    iterDirectory(path, local, SearchMode::Directories);

    for (auto&& p : local) {
        iterDirectoriesRecursive(p, results);
        results.emplace_back(std::move(p));
    }
}

static void globDir(const fs::path& path, std::string_view pattern, SmallVector<fs::path>& results,
                    SearchMode searchMode) {
    SmallVector<fs::path> local;
    iterDirectory(path, local, searchMode);

    for (auto&& p : local) {
        if (matches(narrow(p.filename().native()), pattern))
            results.emplace_back(std::move(p));
    }
}

void svGlobInternal(const fs::path& basePath, std::string_view pattern,
                    SmallVector<fs::path>& results) {
    // Parse the pattern. Consume directories in chunks until
    // we find one that has wildcards for us to handle.
    auto currPath = basePath;
    while (!pattern.empty()) {
        // The '...' pattern only applies at the start of a segment,
        // and means to recursively pull all directories.
        if (pattern.starts_with("..."sv)) {
            SmallVector<fs::path> dirs;
            iterDirectoriesRecursive(currPath, dirs);
            dirs.emplace_back(std::move(currPath));

            pattern = pattern.substr(3);
            for (auto& dir : dirs)
                svGlobInternal(dir, pattern, results);
            return;
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
                    globDir(currPath, subPattern, dirs, SearchMode::Directories);
                    for (auto& dir : dirs)
                        svGlobInternal(dir, pattern, results);
                    return;
                }

                // Otherwise just record this directory and move on to the next.
                foundDir = true;
                currPath /= subPattern;
                break;
            }
        }

        // We didn't find a directory separator, so we're going to consume
        // the remainder of the pattern and search for files with that pattern.
        if (!foundDir) {
            if (hasWildcards) {
                globDir(currPath, pattern, results, SearchMode::Files);
            }
            else {
                // Check for an exact match and add the file if we find it.
                std::error_code ec;
                currPath /= pattern;
                if (fs::is_regular_file(currPath, ec))
                    results.emplace_back(std::move(currPath));
            }
            return;
        }
    }

    // If we reach this point, we either had an empty pattern to
    // begin with or we consumed the whole pattern and it had a trailing
    // directory separator. In this case we want to include all files
    // underneath the directory pointed to by currPath.
    iterDirectory(currPath, results, SearchMode::Files);
}

void svGlob(const fs::path& basePath, std::string_view pattern, SmallVector<fs::path>& results) {
    // Expand any environment variable references in the pattern.
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

    // Normalize the path to remove duplicate separators, figure out
    // whether we have an absolute path, etc.
    auto patternPath = fs::path(widen(patternStr)).lexically_normal();
    if (patternPath.has_root_path()) {
        svGlobInternal(patternPath.root_path(), narrow(patternPath.relative_path().native()),
                       results);
    }
    else {
        svGlobInternal(basePath, narrow(patternPath.native()), results);
    }
}

} // namespace slang
