//------------------------------------------------------------------------------
// SourceLoader.cpp
// High-level source file loading, library mapping, and parsing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/driver/SourceLoader.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"
#include "slang/util/String.h"
#include "slang/util/ThreadPool.h"

namespace fs = std::filesystem;

namespace slang::driver {

using namespace syntax;

SourceLoader::SourceLoader(SourceManager& sourceManager, const Bag& optionBag,
                           ErrorCallback errorCallback) :
    sourceManager(sourceManager),
    optionBag(optionBag), srcOptions(optionBag.getOrDefault<SourceOptions>()),
    errorCallback(std::move(errorCallback)) {

    // When searching for library modules we will always include these extensions
    // in addition to anything the user provides.
    uniqueExtensions.emplace(".v"sv);
    uniqueExtensions.emplace(".sv"sv);
    for (auto ext : uniqueExtensions)
        searchExtensions.emplace_back(widen(ext));
}

void SourceLoader::addFiles(std::string_view pattern) {
    SmallVector<fs::path> files;
    svGlob("", pattern, GlobMode::Files, files);

    filePaths.reserve(filePaths.size() + files.size());
    for (auto&& path : files)
        filePaths.emplace_back(std::move(path), /* isLibrary */ false);
}

bool SourceLoader::addLibraryMaps(std::string_view pattern) {
    // TODO: should this allow patterns / multiple maps?

    // Load and parse the map file right away; we need it to
    // figure out what other sources to load.
    // TODO: make readSource take a fs::path?
    auto buffer = sourceManager.readSource(widen(pattern), /* library */ nullptr);
    if (!buffer)
        return false;

    auto tree = SyntaxTree::fromLibraryMapBuffer(buffer, sourceManager, optionBag);
    libraryMaps.push_back(tree);

    for (auto member : tree->root().as<LibraryMapSyntax>().members) {
        switch (member->kind) {
            case SyntaxKind::ConfigDeclaration:
            case SyntaxKind::EmptyMember:
                break;
            case SyntaxKind::LibraryIncludeStatement: {
                auto token = member->as<FilePathSpecSyntax>().path;
                if (!token.isMissing()) {
                    // TODO: error handling if file(s) don't exist
                    // TODO: infinite include detection
                    // TODO: set current path to this file
                    auto spec = token.valueText();
                    if (!spec.empty())
                        addLibraryMaps(spec);
                }
                break;
            }
            case SyntaxKind::LibraryDeclaration:
                createLibrary(member->as<LibraryDeclarationSyntax>());
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    return true;
}

void SourceLoader::addLibraryFiles(std::string_view, std::string_view pattern) {
    // TODO: lookup library

    SmallVector<fs::path> files;
    svGlob("", pattern, GlobMode::Files, files);

    filePaths.reserve(filePaths.size() + files.size());
    for (auto&& path : files)
        filePaths.emplace_back(std::move(path), /* isLibrary */ true);
}

void SourceLoader::addSearchDirectories(std::span<const std::string> directories) {
    searchDirectories.reserve(searchDirectories.size() + directories.size());
    for (auto& dir : directories)
        searchDirectories.emplace_back(widen(dir));
}

void SourceLoader::addSearchExtensions(std::span<const std::string> extensions) {
    for (auto& ext : extensions) {
        if (uniqueExtensions.emplace(ext).second)
            searchExtensions.emplace_back(widen(ext));
    }
}

SourceLoader::SyntaxTreeList SourceLoader::loadAndParseSources() {
    auto loadSource = [this](const std::filesystem::path& path, bool isLibrary,
                             std::vector<SourceBuffer>& singleUnitBuffers,
                             std::vector<SourceBuffer>& deferredLibBuffers,
                             SyntaxTreeList& results) {
        // TODO: Figure out which library this file is in.
        const SourceLibrary* library = nullptr;

        // Load into memory.
        auto buffer = sourceManager.readSource(path, library);
        if (!buffer) {
            // TODO: error checking
        }

        if (!isLibrary && srcOptions.singleUnit) {
            // If this file was directly specified (i.e. not via
            // a library mapping) and we're in single-unit mode,
            // collect it for later parsing.
            singleUnitBuffers.push_back(buffer);
        }
        else if (srcOptions.librariesInheritMacros) {
            // If libraries inherit macros then we can't parse here,
            // we need to wait for the main compilation unit to be
            // parsed.
            SLANG_ASSERT(isLibrary);
            deferredLibBuffers.push_back(buffer);
        }
        else {
            // Otherwise we can parse right away.
            auto tree = SyntaxTree::fromBuffer(buffer, sourceManager, optionBag);
            if (isLibrary || srcOptions.onlyLint)
                tree->isLibrary = true;

            results.emplace_back(std::move(tree));
        }
    };

    SyntaxTreeList syntaxTrees;
    std::span<const DefineDirectiveSyntax* const> inheritedMacros;

    if (filePaths.size() > 4 && srcOptions.numThreads != 1u) {
        // If there are enough files to parse and the user hasn't disabled
        // the use of threads, do the parsing via a thread pool.
        ThreadPool threadPool(srcOptions.numThreads.value_or(0u));

        // TODO:
    }
    else {
        std::vector<SourceBuffer> singleUnitBuffers;
        std::vector<SourceBuffer> deferredLibBuffers;

        // Load all source files that were specified on the command line
        // or via library maps.
        for (auto& [path, isLibrary] : filePaths)
            loadSource(path, isLibrary, singleUnitBuffers, deferredLibBuffers, syntaxTrees);

        // If we waited to parse direct buffers due to wanting a single unit, parse that unit now.
        if (!singleUnitBuffers.empty()) {
            auto tree = SyntaxTree::fromBuffers(singleUnitBuffers, sourceManager, optionBag);
            if (srcOptions.onlyLint)
                tree->isLibrary = true;

            syntaxTrees.emplace_back(std::move(tree));
        }

        // If we deferred libraries due to wanting to inherit macros, parse them now.
        if (!deferredLibBuffers.empty()) {
            inheritedMacros = syntaxTrees.back()->getDefinedMacros();
            for (auto& buffer : deferredLibBuffers) {
                auto tree = SyntaxTree::fromBuffer(buffer, sourceManager, optionBag,
                                                   inheritedMacros);
                tree->isLibrary = true;
                syntaxTrees.emplace_back(std::move(tree));
            }
        }
    }

    if (!searchDirectories.empty()) {
        // If library directories are specified, see if we have any unknown instantiations
        // or package names for which we should search for additional source files to load.
        flat_hash_set<std::string_view> knownNames;
        auto addKnownNames = [&](const std::shared_ptr<SyntaxTree>& tree) {
            auto& meta = tree->getMetadata();
            for (auto& [n, _] : meta.nodeMap) {
                auto decl = &n->as<ModuleDeclarationSyntax>();
                std::string_view name = decl->header->name.valueText();
                if (!name.empty())
                    knownNames.emplace(name);
            }

            for (auto classDecl : meta.classDecls) {
                std::string_view name = classDecl->name.valueText();
                if (!name.empty())
                    knownNames.emplace(name);
            }
        };

        auto findMissingNames = [&](const std::shared_ptr<SyntaxTree>& tree,
                                    flat_hash_set<std::string_view>& missing) {
            auto& meta = tree->getMetadata();
            for (auto name : meta.globalInstances) {
                if (knownNames.find(name) == knownNames.end())
                    missing.emplace(name);
            }

            for (auto idName : meta.classPackageNames) {
                std::string_view name = idName->identifier.valueText();
                if (!name.empty() && knownNames.find(name) == knownNames.end())
                    missing.emplace(name);
            }

            for (auto importDecl : meta.packageImports) {
                for (auto importItem : importDecl->items) {
                    std::string_view name = importItem->package.valueText();
                    if (!name.empty() && knownNames.find(name) == knownNames.end())
                        missing.emplace(name);
                }
            }

            for (auto intf : meta.interfacePorts) {
                std::string_view name = intf->nameOrKeyword.valueText();
                if (knownNames.find(name) == knownNames.end())
                    missing.emplace(name);
            }
        };

        for (auto& tree : syntaxTrees)
            addKnownNames(tree);

        flat_hash_set<std::string_view> missingNames;
        for (auto& tree : syntaxTrees)
            findMissingNames(tree, missingNames);

        // Keep loading new files as long as we are making forward progress.
        flat_hash_set<std::string_view> nextMissingNames;
        while (true) {
            for (auto name : missingNames) {
                SourceBuffer buffer;
                for (auto& dir : searchDirectories) {
                    fs::path path(dir);
                    path /= name;

                    for (auto& ext : searchExtensions) {
                        path.replace_extension(ext);
                        if (!sourceManager.isCached(path)) {
                            // TODO: figure out which library this is
                            const SourceLibrary* library = nullptr;
                            buffer = sourceManager.readSource(path, library);
                            if (buffer)
                                break;
                        }
                    }

                    if (buffer)
                        break;
                }

                if (buffer) {
                    auto tree = SyntaxTree::fromBuffer(buffer, sourceManager, optionBag,
                                                       inheritedMacros);
                    tree->isLibrary = true;
                    syntaxTrees.emplace_back(tree);

                    addKnownNames(tree);
                    findMissingNames(tree, nextMissingNames);
                }
            }

            if (nextMissingNames.empty())
                break;

            missingNames = std::move(nextMissingNames);
            nextMissingNames = {};
        }
    }

    return syntaxTrees;
}

void SourceLoader::createLibrary(const LibraryDeclarationSyntax& syntax) {
    auto libName = syntax.name.valueText();
    if (libName.empty())
        return;

    std::vector<std::pair<std::filesystem::path, GlobRank>> files;
    for (auto filePath : syntax.filePaths) {
        auto spec = filePath->path.valueText();
        if (!spec.empty()) {
            // TODO: base path?
            SmallVector<fs::path> globFiles;
            auto rank = svGlob("", spec, GlobMode::Files, globFiles);

            files.reserve(files.size() + globFiles.size());
            for (auto& path : globFiles)
                files.emplace_back(std::move(path), rank);
        }
    }

    // TODO: incdirs

    // TODO: check dups
    libraries.emplace(libName, Library{libName, std::move(files)});
}

} // namespace slang::driver
