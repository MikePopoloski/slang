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
struct SourceLibrary;

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
    SourceLoader(SourceManager& sourceManager, ErrorCallback errorCallback);

    SourceLoader(const SourceLoader& other) = delete;
    SourceLoader(SourceLoader&& other) = default;

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

    /// Returns true if there is at least one source file to load,
    /// and false if none have been added to the loader.
    bool hasFiles() const { return !fileEntries.empty(); }

    bool addLibraryMaps(std::string_view pattern, const Bag& optionBag);
    const SyntaxTreeList& getLibraryMaps() const { return libraryMapTrees; }

    /// Loads all of the sources that have been added to the loader,
    /// but does not parse them. Returns the loaded buffers.
    std::vector<SourceBuffer> loadSources();

    /// Loads and parses all of the source files that have been added to the loader.
    SyntaxTreeList loadAndParseSources(const Bag& optionBag);

private:
    // One entry per unique file path added to the loader.
    struct FileEntry {
        // The filesystem path (as specified by the user).
        std::filesystem::path path;

        // The library to which the file belongs, if any.
        const SourceLibrary* library = nullptr;

        // A second library that can lay claim to this file,
        // at the same glob rank as the first library. It's an
        // error if we end up in this state for any file but
        // we can temporarily be here if two libraries match at
        // the same rank but another library we haven't seen yet
        // matches at an even higher rank.
        const SourceLibrary* secondLib = nullptr;

        // A measure of how strongly this file belongs to the library.
        GlobRank libraryRank;

        // True if the file is intended to be part of a library
        // (because it was specified via addLibraryFiles or via a
        // library map) and false if not. Non-library files (which set
        // this to false) can still map to a SourceLibrary but get
        // treated differently (such as modules within them being
        // eligible for automatic instantiation).
        bool isLibraryFile = false;

        FileEntry(std::filesystem::path&& path, bool isLibraryFile, const SourceLibrary* library,
                  GlobRank libraryRank) :
            path(std::move(path)),
            library(library), libraryRank(libraryRank), isLibraryFile(isLibraryFile) {}
    };

    const SourceLibrary* getOrAddLibrary(std::string_view name);
    void addFilesInternal(std::string_view pattern, bool isLibraryFile,
                          const SourceLibrary* library);
    void createLibrary(const syntax::LibraryDeclarationSyntax& syntax);
    void loadAndParse(const FileEntry& fileEntry, const Bag& optionBag,
                      const SourceOptions& srcOptions, std::vector<SourceBuffer>& singleUnitBuffers,
                      std::vector<SourceBuffer>& deferredLibBuffers, SyntaxTreeList& syntaxTrees);

    SourceManager& sourceManager;

    std::vector<FileEntry> fileEntries;
    flat_hash_map<std::filesystem::path, size_t> fileIndex;
    flat_hash_map<std::string, std::unique_ptr<SourceLibrary>> libraries;
    std::vector<std::filesystem::path> searchDirectories;
    std::vector<std::filesystem::path> searchExtensions;
    flat_hash_set<std::string_view> uniqueExtensions;
    SyntaxTreeList libraryMapTrees;
    ErrorCallback errorCallback;

    static constexpr int MinFilesForThreading = 4;
};

} // namespace slang::driver
