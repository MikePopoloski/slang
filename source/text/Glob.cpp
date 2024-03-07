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

        if (!ec && visited.emplace(getU8Str(canonical)).second) {
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
        if (matches(getU8Str(p.filename()), pattern))
            results.emplace_back(std::move(p));
    }
}

GlobRank svGlobInternal(const fs::path& basePath, std::string_view pattern, GlobMode mode,
                        SmallVector<fs::path>& results, bool& anyWildcards) {
    // Parse the pattern. Consume directories in chunks until
    // we find one that has wildcards for us to handle.
    auto currPath = basePath;
    const auto originalPattern = pattern;
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
                rank = svGlobInternal(dir, pattern, mode, results, anyWildcards);

            anyWildcards = true;
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
                        rank = svGlobInternal(dir, pattern, mode, results, anyWildcards);

                    anyWildcards = true;
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
                anyWildcards = true;
                return GlobRank::WildcardName;
            }

            // Check for an exact match and add the target if we find it.
            std::error_code ec;
            currPath /= pattern;

            if ((mode == GlobMode::Files && fs::is_regular_file(currPath, ec)) ||
                (mode == GlobMode::Directories && fs::is_directory(currPath, ec))) {
                results.emplace_back(std::move(currPath));
            }

            return GlobRank::SimpleName;
        }
    }

    // If we reach this point, we either had an empty pattern to
    // begin with or we consumed the whole pattern and it had a trailing
    // directory separator. If we are searching for files we want to include
    // all files underneath the directory pointed to by currPath, and if
    // we're searching for directories we'll just take this directory.
    if (mode == GlobMode::Files) {
        iterDirectory(currPath, results, GlobMode::Files);
        return GlobRank::Directory;
    }
    else {
        std::error_code ec;
        if (fs::is_directory(currPath, ec))
            results.emplace_back(std::move(currPath));

        if (originalPattern.empty() ||
            (originalPattern.size() == 1 && originalPattern[0] == fs::path::preferred_separator)) {
            return GlobRank::Directory;
        }
        else {
            return GlobRank::SimpleName;
        }
    }
}

SLANG_EXPORT GlobRank svGlob(const fs::path& basePath, std::string_view pattern, GlobMode mode,
                             SmallVector<fs::path>& results, bool expandEnvVars,
                             std::error_code& ec) {
    ec.clear();
    if (pattern == "-"sv && mode == GlobMode::Files) {
        // This is interpretted as trying to read stdin.
        results.emplace_back("-");
        return GlobRank::ExactPath;
    }

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

        patternPath = fs::path(patternStr);
    }
    else {
        patternPath = fs::path(pattern);
    }

    // Normalize the path to remove duplicate separators, figure out
    // whether we have an absolute path, etc.
    patternPath = patternPath.lexically_normal();

    SmallVector<fs::path> local;
    GlobRank rank;
    bool anyWildcards = false;
    if (patternPath.has_root_path()) {
        rank = svGlobInternal(patternPath.root_path(), getU8Str(patternPath.relative_path()), mode,
                              local, anyWildcards);
    }
    else {
        rank = svGlobInternal(basePath, getU8Str(patternPath), mode, local, anyWildcards);
    }

    // Results paths are always made canonical.
    std::error_code localEc;
    results.reserve(local.size());
    for (auto& p : local) {
        auto canonical = fs::weakly_canonical(p, localEc);
        if (!localEc)
            results.emplace_back(std::move(canonical));
    }

    if (!anyWildcards && rank == GlobRank::SimpleName) {
        // If there were no wildcards at all and we had a simple name match,
        // promote the rank to an exact path match.
        rank = GlobRank::ExactPath;
        if (results.empty()) {
            if (!patternPath.has_root_path())
                patternPath = basePath / patternPath;

            auto status = fs::status(patternPath, ec);
            if (!ec) {
                switch (status.type()) {
                    case fs::file_type::directory:
                        ec = make_error_code(std::errc::is_a_directory);
                        break;
                    case fs::file_type::not_found:
                        ec = make_error_code(std::errc::no_such_file_or_directory);
                        break;
                    case fs::file_type::unknown:
                        ec = make_error_code(std::errc::permission_denied);
                        break;
                    default:
                        if (mode == GlobMode::Directories)
                            ec = make_error_code(std::errc::not_a_directory);
                        else
                            ec = make_error_code(std::errc::not_supported);
                        break;
                }
            }
        }
    }

    return rank;
}

static std::string_view nextSegment(std::string_view& path) {
    for (size_t i = 0; i < path.size(); i++) {
        // NOLINTNEXTLINE
        if (path[i] == fs::path::preferred_separator || path[i] == '/') {
            auto result = path.substr(0, i);
            path = path.substr(i + 1);
            return result;
        }
    }

    auto result = path;
    path = {};
    return result;
}

static bool svGlobMatchesInternal(std::string_view path, std::string_view pattern) {
    while (!pattern.empty() && !path.empty()) {
        // Special case for recursive directory search.
        if (pattern.starts_with("..."sv)) {
            pattern = pattern.substr(3);
            do {
                if (svGlobMatchesInternal(path, pattern))
                    return true;

                nextSegment(path);
            } while (!path.empty());

            return false;
        }

        // If the next segments don't match then we don't match overall.
        if (!matches(nextSegment(path), nextSegment(pattern))) {
            return false;
        }
    }

    // We match if:
    // 1) we used up the whole pattern
    // 2) pattern ended in a separator and the next path segment is the last (i.e. the file name)
    //    -- OR --
    //    pattern didn't end in a separator and we matched the whole path (so it's empty now)
    nextSegment(path);
    return pattern.empty() && path.empty();
}

bool svGlobMatches(const fs::path& path, const fs::path& pattern) {
    return svGlobMatchesInternal(getU8Str(path), getU8Str(pattern));
}

} // namespace slang
