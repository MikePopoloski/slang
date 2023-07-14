//------------------------------------------------------------------------------
// SourceLoader.cpp
// High-level source file loading, library mapping, and parsing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/driver/SourceLoader.h"

#include <fmt/core.h>

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"
#include "slang/util/String.h"
#include "slang/util/ThreadPool.h"

namespace fs = std::filesystem;

namespace slang::driver {

using namespace syntax;

SourceLoader::SourceLoader(SourceManager& sourceManager, ErrorCallback errorCallback) :
    sourceManager(sourceManager), errorCallback(std::move(errorCallback)) {

    // When searching for library modules we will always include these extensions
    // in addition to anything the user provides.
    uniqueExtensions.emplace(".v"sv);
    uniqueExtensions.emplace(".sv"sv);
    for (auto ext : uniqueExtensions)
        searchExtensions.emplace_back(widen(ext));
}

void SourceLoader::addFiles(std::string_view pattern) {
    addFilesInternal(pattern, /* isLibraryFile */ false, /* library */ nullptr);
}

void SourceLoader::addLibraryFiles(std::string_view libName, std::string_view pattern) {
    addFilesInternal(pattern, /* isLibraryFile */ true, getOrAddLibrary(libName));
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

bool SourceLoader::addLibraryMaps(std::string_view pattern, const Bag& optionBag) {
    // TODO: should this allow patterns / multiple maps?

    // Load and parse the map file right away; we need it to
    // figure out what other sources to load.
    auto buffer = sourceManager.readSource(widen(pattern), /* library */ nullptr);
    if (!buffer)
        return false;

    auto tree = SyntaxTree::fromLibraryMapBuffer(buffer, sourceManager, optionBag);
    libraryMapTrees.push_back(tree);

    for (auto member : tree->root().as<LibraryMapSyntax>().members) {
        switch (member->kind) {
            case SyntaxKind::ConfigDeclaration:
            case SyntaxKind::EmptyMember:
                break;
            case SyntaxKind::LibraryIncludeStatement: {
                auto token = member->as<FilePathSpecSyntax>().path;
                // TODO: error handling if file(s) don't exist
                // TODO: infinite include detection
                // TODO: set current path to this file
                auto spec = token.valueText();
                if (!spec.empty())
                    addLibraryMaps(spec, optionBag);
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

std::vector<SourceBuffer> SourceLoader::loadSources() {
    std::vector<SourceBuffer> results;
    results.reserve(fileEntries.size());

    for (auto& entry : fileEntries) {
        auto buffer = sourceManager.readSource(entry.path, entry.library);
        if (!buffer)
            errorCallback(fmt::format("unable to open file: '{}'", getU8Str(entry.path)));
        else
            results.push_back(buffer);
    }

    return results;
}

SourceLoader::SyntaxTreeList SourceLoader::loadAndParseSources(const Bag& optionBag) {
    SyntaxTreeList syntaxTrees;
    std::span<const DefineDirectiveSyntax* const> inheritedMacros;

    auto srcOptions = optionBag.getOrDefault<SourceOptions>();

    auto parseSingleUnit = [&](std::span<const SourceBuffer> buffers) {
        // If we waited to parse direct buffers due to wanting a single unit, parse that unit now.
        if (!buffers.empty()) {
            auto tree = SyntaxTree::fromBuffers(buffers, sourceManager, optionBag);
            if (srcOptions.onlyLint)
                tree->isLibrary = true;

            syntaxTrees.emplace_back(std::move(tree));
            inheritedMacros = syntaxTrees.back()->getDefinedMacros();
        }
    };

    if (fileEntries.size() >= MinFilesForThreading && srcOptions.numThreads != 1u) {
        // If there are enough files to parse and the user hasn't disabled
        // the use of threads, do the parsing via a thread pool.
        ThreadPool threadPool(srcOptions.numThreads.value_or(0u));

        std::vector<SourceBuffer> singleUnitBuffers;
        std::vector<SourceBuffer> deferredLibBuffers;
        std::mutex mut;

        // Load all source files that were specified on the command line
        // or via library maps.
        threadPool.pushLoop(size_t(0), fileEntries.size(), [&](size_t start, size_t end) {
            SyntaxTreeList localTrees;
            std::vector<SourceBuffer> localSingleUnitBufs;
            std::vector<SourceBuffer> localDeferredLibBufs;

            const size_t count = end - start;
            localTrees.reserve(count);
            localSingleUnitBufs.reserve(count);
            localDeferredLibBufs.reserve(count);

            for (size_t i = start; i < end; i++) {
                auto& entry = fileEntries[i];
                loadAndParse(entry, optionBag, srcOptions, localSingleUnitBufs,
                             localDeferredLibBufs, localTrees);
            }

            // Merge our local results into the shared lists.
            std::unique_lock lock(mut);
            syntaxTrees.insert(syntaxTrees.end(), localTrees.begin(), localTrees.end());
            singleUnitBuffers.insert(singleUnitBuffers.end(), localSingleUnitBufs.begin(),
                                     localSingleUnitBufs.end());
            deferredLibBuffers.insert(deferredLibBuffers.end(), localDeferredLibBufs.begin(),
                                      localDeferredLibBufs.end());
        });
        threadPool.waitForAll();

        parseSingleUnit(singleUnitBuffers);

        // If we deferred libraries due to wanting to inherit macros, parse them now.
        threadPool.pushLoop(size_t(0), deferredLibBuffers.size(), [&](size_t start, size_t end) {
            SyntaxTreeList localTrees;
            localTrees.reserve(end - start);

            for (size_t i = start; i < end; i++) {
                auto tree = SyntaxTree::fromBuffer(deferredLibBuffers[i], sourceManager, optionBag,
                                                   inheritedMacros);
                tree->isLibrary = true;
                localTrees.emplace_back(std::move(tree));
            }

            std::unique_lock lock(mut);
            syntaxTrees.insert(syntaxTrees.end(), localTrees.begin(), localTrees.end());
        });
        threadPool.waitForAll();
    }
    else {
        std::vector<SourceBuffer> singleUnitBuffers;
        std::vector<SourceBuffer> deferredLibBuffers;

        const size_t count = fileEntries.size();
        syntaxTrees.reserve(count);
        singleUnitBuffers.reserve(count);
        deferredLibBuffers.reserve(count);

        // Load all source files that were specified on the command line
        // or via library maps.
        for (auto& entry : fileEntries) {
            loadAndParse(entry, optionBag, srcOptions, singleUnitBuffers, deferredLibBuffers,
                         syntaxTrees);
        }

        parseSingleUnit(singleUnitBuffers);

        // If we deferred libraries due to wanting to inherit macros, parse them now.
        if (!deferredLibBuffers.empty()) {
            syntaxTrees.reserve(syntaxTrees.size() + deferredLibBuffers.size());
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
                            // This file is never part of a library because if
                            // it was we would have already loaded it earlier.
                            buffer = sourceManager.readSource(path, /* library */ nullptr);
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

const SourceLibrary* SourceLoader::getOrAddLibrary(std::string_view name) {
    if (name.empty())
        return nullptr;

    auto nameStr = std::string(name);
    auto& lib = libraries[nameStr];
    if (!lib)
        lib = std::make_unique<SourceLibrary>(std::move(nameStr));

    return lib.get();
}

void SourceLoader::addFilesInternal(std::string_view pattern, bool isLibraryFile,
                                    const SourceLibrary* library) {
    // TODO: basePath?
    SmallVector<fs::path> files;
    auto rank = svGlob("", pattern, GlobMode::Files, files);

    if (files.empty()) {
        if (rank == GlobRank::ExactName)
            errorCallback(fmt::format("no such file: '{}'", pattern));
        return;
    }

    fileEntries.reserve(fileEntries.size() + files.size());
    for (auto&& path : files) {
        std::error_code ec;
        auto [it, inserted] = fileIndex.try_emplace(fs::weakly_canonical(path, ec),
                                                    fileEntries.size());
        if (inserted) {
            fileEntries.emplace_back(std::move(path), isLibraryFile, library, rank);
        }
        else {
            // If any of the times we see this is entry is for a non-library file,
            // then it's always a non-library file, hence the &=.
            auto& entry = fileEntries[it->second];
            entry.isLibraryFile &= isLibraryFile;

            if (library) {
                // If there is already a library for this entry and our rank is lower,
                // we overrule it. If it's higher, we ignore. If it's a tie, we remember
                // that fact for now and later we will issue an error if the tie is
                // never resolved.
                if (!entry.library || rank < entry.libraryRank) {
                    entry.library = library;
                    entry.libraryRank = rank;
                }
                else if (rank == entry.libraryRank) {
                    entry.secondLib = library;
                }
            }
        }
    }
}

void SourceLoader::createLibrary(const LibraryDeclarationSyntax& syntax) {
    auto libName = syntax.name.valueText();
    if (libName.empty())
        return;

    auto library = getOrAddLibrary(libName);
    for (auto filePath : syntax.filePaths) {
        auto spec = filePath->path.valueText();
        if (!spec.empty())
            addFilesInternal(spec, /* isLibraryFile */ true, library);
    }

    // TODO: incdirs
}

void SourceLoader::loadAndParse(const FileEntry& entry, const Bag& optionBag,
                                const SourceOptions& srcOptions,
                                std::vector<SourceBuffer>& singleUnitBuffers,
                                std::vector<SourceBuffer>& deferredLibBuffers,
                                SyntaxTreeList& syntaxTrees) {
    // TODO: error if secondLib is set

    // Load into memory.
    auto buffer = sourceManager.readSource(entry.path, entry.library);
    if (!buffer) {
        errorCallback(fmt::format("unable to open file: '{}'", getU8Str(entry.path)));
        return;
    }

    if (!entry.isLibraryFile && srcOptions.singleUnit) {
        // If this file was directly specified (i.e. not via
        // a library mapping) and we're in single-unit mode,
        // collect it for later parsing.
        singleUnitBuffers.push_back(buffer);
    }
    else if (srcOptions.librariesInheritMacros) {
        // If libraries inherit macros then we can't parse here,
        // we need to wait for the main compilation unit to be
        // parsed.
        SLANG_ASSERT(entry.isLibraryFile);
        deferredLibBuffers.push_back(buffer);
    }
    else {
        // Otherwise we can parse right away.
        auto tree = SyntaxTree::fromBuffer(buffer, sourceManager, optionBag);
        if (entry.isLibraryFile || srcOptions.onlyLint)
            tree->isLibrary = true;

        syntaxTrees.emplace_back(std::move(tree));
    }
};

} // namespace slang::driver
