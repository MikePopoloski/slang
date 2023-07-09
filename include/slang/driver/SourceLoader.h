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

} // namespace slang

namespace slang::syntax {
class SyntaxTree;
}

namespace slang::driver {

struct SourceOptions {
    std::optional<uint32_t> numThreads;
    bool singleUnit;
    bool onlyLint;
    bool librariesInheritMacros;
};

class SLANG_EXPORT SourceLoader {
public:
    using SyntaxTreeList = std::vector<std::shared_ptr<syntax::SyntaxTree>>;
    using ErrorCallback = std::function<void(const std::string&)>;

    SourceLoader(SourceManager& sourceManager, const Bag& optionBag, ErrorCallback errorCallback);

    void addFiles(std::string_view pattern);
    bool addLibraryMaps(std::string_view pattern);
    void addLibraryFiles(std::string_view libraryName, std::string_view pattern);
    void addSearchDirectories(std::span<const std::string> directories);
    void addSearchExtensions(std::span<const std::string> extensions);

    const SyntaxTreeList& getLibraryMaps() const { return libraryMaps; }

    SyntaxTreeList loadAndParseSources();

private:
    struct Library {
        std::string_view name;
        std::vector<std::pair<std::filesystem::path, GlobRank>> files;
    };

    void createLibrary(const syntax::LibraryDeclarationSyntax& syntax);

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
};

} // namespace slang::driver
