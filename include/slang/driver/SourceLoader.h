//------------------------------------------------------------------------------
//! @file SourceLoader.h
//! @brief High-level source file loading, library mapping, and parsing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <filesystem>
#include <memory>
#include <optional>
#include <span>
#include <vector>

#include "slang/syntax/SyntaxFwd.h"
#include "slang/text/Glob.h"
#include "slang/util/Hash.h"
#include "slang/util/Util.h"

namespace slang {

class Bag;
class SourceManager;
struct SourceBuffer;

} // namespace slang

namespace slang::syntax {
class SyntaxTree;
}

namespace slang::driver {

/// Specifies options used when loading source files.
struct SLANG_EXPORT SourceOptions {
    /// The number of threads to use for loading and parsing.
    std::optional<uint32_t> numThreads;

    /// If set to true, all source files will be treated as part of a single
    /// compilation unit, meaning all of their text will be merged together.
    bool singleUnit;

    /// If true, only perform linting of code, don't try to elaborate a full hierarchy.
    bool onlyLint;

    /// If true, library files will inherit macro definitions from primary source files.
    bool librariesInheritMacros;
};

/// @brief Handles loading and parsing of groups of source files
///
/// This class handles high-level descriptions of how to load and parse source files,
/// such as via library mapping files or search directories to look in. The actual
/// loading and parsing are delegated to classes like @a SourceManager and @a SyntaxTree.
class SLANG_EXPORT SourceLoader {
public:
    using SyntaxTreeList = std::vector<std::shared_ptr<syntax::SyntaxTree>>;
    using ErrorCallback = std::function<void(const std::string&)>;

    /// Constructs a new instance of the SourceLoader class.
    SourceLoader(SourceManager& sourceManager, const Bag& optionBag, ErrorCallback errorCallback);

    /// @brief Adds files to be loaded, specified via the given @a pattern.
    ///
    /// All of the files that match the pattern will be added for loading.
    /// If no files match and the pattern is actually just a specific filename
    /// an error will be issued.
    void addFiles(std::string_view pattern);

    /// @brief Adds library files to be loaded, specified via the given @a pattern.
    ///
    /// All of the files that match the pattern will be added for loading.
    /// If no files match and the pattern is actually just a specific filename
    /// an error will be issued.
    ///
    /// Library files differ from regular source files in that they are only
    /// considered "used" if referenced in the main source and their modules
    /// are not automatically instantiated.
    void addLibraryFiles(std::string_view libraryName, std::string_view pattern);

    /// @brief Adds directories in which to search for library module files.
    ///
    /// A search for a library module occurs when there are instantiations found
    /// for unknown modules (or interfaces or programs). The given directories
    /// will be searched for files with the missing module's name plus any registered
    /// search extensions.
    void addSearchDirectories(std::span<const std::string> directories);

    /// @brief Adds extensions used to search for library module files.
    ///
    /// A search for a library module occurs when there are instantiations found
    /// for unknown modules (or interfaces or programs). The search will be for
    /// files with the given @a extensions.
    ///
    /// Note that the extensions ".v" and ".sv" are always automatically included
    /// in the search set.
    void addSearchExtensions(std::span<const std::string> extensions);

    bool addLibraryMaps(std::string_view pattern);
    const SyntaxTreeList& getLibraryMaps() const { return libraryMaps; }

    /// Loads and parses all of the source files that have been added to the loader.
    SyntaxTreeList loadAndParseSources();

private:
    struct Library {
        std::string_view name;
        std::vector<std::pair<std::filesystem::path, GlobRank>> files;
    };

    void createLibrary(const syntax::LibraryDeclarationSyntax& syntax);
    void loadSource(const std::filesystem::path& path, bool isLibrary,
                    std::vector<SourceBuffer>& singleUnitBuffers,
                    std::vector<SourceBuffer>& deferredLibBuffers, SyntaxTreeList& syntaxTrees);

    SourceManager& sourceManager;
    const Bag& optionBag;
    SourceOptions srcOptions;

    std::vector<std::pair<std::filesystem::path, bool>> filePaths;
    flat_hash_map<std::filesystem::path, std::vector<std::pair<Library, GlobRank>>> fileToLibMap;
    flat_hash_map<std::string_view, Library> libraries;
    std::vector<std::filesystem::path> searchDirectories;
    std::vector<std::filesystem::path> searchExtensions;
    flat_hash_set<std::string_view> uniqueExtensions;
    SyntaxTreeList libraryMaps;
    ErrorCallback errorCallback;

    static constexpr int MinFilesForThreading = 4;
};

} // namespace slang::driver
