//------------------------------------------------------------------------------
// SourceLoader.cpp
// High-level source file loading, library mapping, and parsing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/driver/SourceLoader.h"

#include <fmt/core.h>

#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"
#include "slang/util/String.h"
#include "slang/util/ThreadPool.h"

namespace fs = std::filesystem;

namespace slang::driver {

using namespace syntax;

SourceLoader::SourceLoader(SourceManager& sourceManager) : sourceManager(sourceManager) {
    // When searching for library modules we will always include these extensions
    // in addition to anything the user provides.
    uniqueExtensions.emplace(".v"sv);
    uniqueExtensions.emplace(".sv"sv);
    for (auto ext : uniqueExtensions)
        searchExtensions.emplace_back(ext);
}

void SourceLoader::addBuffer(SourceBuffer buffer) {
    fileEntries.emplace_back(buffer);
}

void SourceLoader::addFiles(std::string_view pattern) {
    addFilesInternal(pattern, {}, /* isLibraryFile */ false, /* library */ nullptr,
                     /* unit */ nullptr,
                     /* expandEnvVars */ false);
}

void SourceLoader::addLibraryFiles(std::string_view libName, std::string_view pattern) {
    addFilesInternal(pattern, {}, /* isLibraryFile */ true, getOrAddLibrary(libName),
                     /* unit */ nullptr,
                     /* expandEnvVars */ false);
}

void SourceLoader::addSearchDirectories(std::string_view pattern) {
    SmallVector<fs::path> directories;
    std::error_code ec;
    svGlob({}, pattern, GlobMode::Directories, directories, /* expandEnvVars */ false, ec);
    if (ec) {
        addError(pattern, ec);
        return;
    }

    searchDirectories.insert(searchDirectories.end(), directories.begin(), directories.end());
}

void SourceLoader::addSearchExtension(std::string_view extension) {
    if (uniqueExtensions.emplace(extension).second)
        searchExtensions.emplace_back(extension);
}

static std::string_view getPathFromSpec(const FilePathSpecSyntax& syntax) {
    auto path = syntax.path.valueText();
    if (path.length() < 3)
        return {};

    return path.substr(1, path.length() - 2);
}

void SourceLoader::addLibraryMaps(std::string_view pattern, const fs::path& basePath,
                                  const Bag& optionBag) {
    flat_hash_set<fs::path> seenMaps;
    addLibraryMapsInternal(pattern, basePath, optionBag, /* expandEnvVars */ false, seenMaps);
}

void SourceLoader::addSeparateUnit(std::span<const std::string> filePatterns,
                                   const std::vector<std::string>& includePaths,
                                   std::vector<std::string> defines,
                                   const std::string& libraryName) {
    std::error_code ec;
    SmallVector<fs::path> includeDirs;
    for (auto& str : includePaths)
        svGlob({}, str, GlobMode::Directories, includeDirs, /* expandEnvVars */ false, ec);

    auto& unit = unitEntries.emplace_back();
    unit.defines = std::move(defines);
    unit.library = getOrAddLibrary(libraryName);

    for (auto&& path : includeDirs)
        unit.includePaths.emplace_back(std::move(path));

    const bool isLibraryFile = unit.library != nullptr;
    for (auto& pattern : filePatterns) {
        addFilesInternal(pattern, {}, isLibraryFile, unit.library, &unit,
                         /* expandEnvVars */ false);
    }
}

void SourceLoader::addLibraryMapsInternal(std::string_view pattern, const fs::path& basePath,
                                          const Bag& optionBag, bool expandEnvVars,
                                          flat_hash_set<fs::path>& seenMaps) {
    SmallVector<fs::path> files;
    std::error_code ec;
    svGlob(basePath, pattern, GlobMode::Files, files, expandEnvVars, ec);

    if (ec) {
        addError(pattern, ec);
        return;
    }

    for (auto& path : files) {
        auto buffer = sourceManager.readSource(path, /* library */ nullptr);
        if (!buffer) {
            addError(path, buffer.error());
            continue;
        }

        if (!seenMaps.insert(path).second) {
            errors.emplace_back(
                fmt::format("library map '{}' includes itself recursively", getU8Str(path)));
            continue;
        }

        auto tree = SyntaxTree::fromLibraryMapBuffer(*buffer, sourceManager, optionBag);
        libraryMapTrees.push_back(tree);

        auto parentPath = path.parent_path();
        for (auto member : tree->root().as<LibraryMapSyntax>().members) {
            switch (member->kind) {
                case SyntaxKind::ConfigDeclaration:
                case SyntaxKind::EmptyMember:
                    break;
                case SyntaxKind::LibraryIncludeStatement: {
                    auto spec = getPathFromSpec(
                        *member->as<LibraryIncludeStatementSyntax>().filePath);
                    if (!spec.empty()) {
                        addLibraryMapsInternal(spec, parentPath, optionBag,
                                               /* expandEnvVars */ true, seenMaps);
                    }
                    break;
                }
                case SyntaxKind::LibraryDeclaration:
                    createLibrary(member->as<LibraryDeclarationSyntax>(), parentPath);
                    break;
                default:
                    SLANG_UNREACHABLE;
            }
        }

        seenMaps.erase(path);
    }
}

std::vector<SourceBuffer> SourceLoader::loadSources() {
    std::vector<SourceBuffer> results;
    results.reserve(fileEntries.size());

    for (auto& entry : fileEntries) {
        SourceManager::BufferOrError buffer;
        if (!entry.preloadedBuffer)
            buffer = sourceManager.readSource(entry.path, entry.library);
        else
            buffer = entry.preloadedBuffer;

        if (!buffer)
            addError(entry.path, buffer.error());
        else
            results.push_back(*buffer);
    }

    return results;
}

SourceLoader::SyntaxTreeList SourceLoader::loadAndParseSources(const Bag& optionBag) {
    SyntaxTreeList syntaxTrees;
    std::vector<SourceBuffer> singleUnitBuffers;
    std::vector<SourceBuffer> deferredLibBuffers;
    std::span<const DefineDirectiveSyntax* const> inheritedMacros;
    flat_hash_map<const UnitEntry*, std::vector<SourceBuffer>> unitToBufferMap;

    const size_t fileEntryCount = fileEntries.size();
    syntaxTrees.reserve(fileEntryCount);
    singleUnitBuffers.reserve(fileEntryCount);
    deferredLibBuffers.reserve(fileEntryCount);

    auto srcOptions = optionBag.getOrDefault<SourceOptions>();

    auto handleLoadResult = [&](LoadResult&& result) {
        switch (result.index()) {
            case 0:
                // File was loaded and parsed independently.
                syntaxTrees.emplace_back(std::get<0>(std::move(result)));
                break;
            case 1: {
                // File was loaded but it's a library file and we
                // need to wait to include it in a parse operation.
                auto [buffer, isDeferredLib] = std::get<1>(result);
                if (isDeferredLib)
                    deferredLibBuffers.push_back(buffer);
                else
                    singleUnitBuffers.push_back(buffer);
                break;
            }
            case 2: {
                // Error occurred.
                auto [entry, code] = std::get<2>(result);
                addError(entry->path, code);
                break;
            }
            case 3: {
                // File is part of a separate unit.
                auto [buffer, unit] = std::get<3>(result);
                SLANG_ASSERT(unit != nullptr);
                unitToBufferMap[unit].push_back(buffer);
                break;
            }
        }
    };

    auto parseSingleUnit = [&](std::span<const SourceBuffer> buffers) {
        // If we waited to parse direct buffers due to wanting a single unit, parse that unit now.
        if (!buffers.empty()) {
            auto tree = SyntaxTree::fromBuffers(buffers, sourceManager, optionBag);
            if (srcOptions.onlyLint)
                tree->isLibraryUnit = true;

            syntaxTrees.emplace_back(std::move(tree));
            inheritedMacros = syntaxTrees.back()->getDefinedMacros();
        }
    };

    auto parseSeparateUnit = [&](const UnitEntry& unit, const std::vector<SourceBuffer>& buffers) {
        auto unitOptions = optionBag;
        auto& ppOptions = unitOptions.insertOrGet<parsing::PreprocessorOptions>();
        ppOptions.predefines.insert(ppOptions.predefines.end(), unit.defines.begin(),
                                    unit.defines.end());
        ppOptions.additionalIncludePaths.insert(ppOptions.additionalIncludePaths.end(),
                                                unit.includePaths.begin(), unit.includePaths.end());

        auto tree = SyntaxTree::fromBuffers(buffers, sourceManager, unitOptions, inheritedMacros);
        tree->isLibraryUnit = srcOptions.onlyLint || unit.library != nullptr;
        return tree;
    };

    if (fileEntries.size() >= MinFilesForThreading && srcOptions.numThreads != 1u) {
        // If there are enough files to parse and the user hasn't disabled
        // the use of threads, do the parsing via a thread pool.
        ThreadPool threadPool(srcOptions.numThreads.value_or(0u));

        std::vector<LoadResult> loadResults;
        loadResults.resize(fileEntries.size());

        // Load all source files that were specified on the command line
        // or via library maps.
        threadPool.pushLoop(size_t(0), fileEntries.size(), [&](size_t start, size_t end) {
            for (size_t i = start; i < end; i++)
                loadResults[i] = loadAndParse(fileEntries[i], optionBag, srcOptions, i);
        });
        threadPool.waitForAll();

        for (auto&& result : loadResults)
            handleLoadResult(std::move(result));

        parseSingleUnit(singleUnitBuffers);

        // Parse separate unit groups into their own syntax trees.
        if (!unitToBufferMap.empty()) {
            std::vector<std::pair<const UnitEntry* const, std::vector<SourceBuffer>>*> unitList;
            unitList.reserve(unitToBufferMap.size());
            for (auto& pair : unitToBufferMap)
                unitList.push_back(&pair);

            const size_t numTrees = syntaxTrees.size();
            syntaxTrees.resize(numTrees + unitList.size());

            threadPool.pushLoop(size_t(0), unitList.size(), [&](size_t start, size_t end) {
                for (size_t i = start; i < end; i++) {
                    syntaxTrees[i + numTrees] = parseSeparateUnit(*unitList[i]->first,
                                                                  unitList[i]->second);
                }
            });
            threadPool.waitForAll();
        }

        // If we deferred libraries due to wanting to inherit macros, parse them now.
        if (!deferredLibBuffers.empty()) {
            const size_t numTrees = syntaxTrees.size();
            syntaxTrees.resize(numTrees + deferredLibBuffers.size());

            threadPool.pushLoop(size_t(0), deferredLibBuffers.size(),
                                [&](size_t start, size_t end) {
                                    for (size_t i = start; i < end; i++) {
                                        auto tree = SyntaxTree::fromBuffer(deferredLibBuffers[i],
                                                                           sourceManager, optionBag,
                                                                           inheritedMacros);
                                        tree->isLibraryUnit = true;
                                        syntaxTrees[i + numTrees] = std::move(tree);
                                    }
                                });
            threadPool.waitForAll();
        }
    }
    else {
        // Load all source files that were specified on the command line
        // or via library maps.
        for (auto& entry : fileEntries)
            handleLoadResult(loadAndParse(entry, optionBag, srcOptions));

        parseSingleUnit(singleUnitBuffers);

        // Parse separate unit groups into their own syntax trees.
        if (!unitToBufferMap.empty()) {
            for (auto& [unit, buffers] : unitToBufferMap)
                syntaxTrees.emplace_back(parseSeparateUnit(*unit, buffers));
        }

        // If we deferred libraries due to wanting to inherit macros, parse them now.
        if (!deferredLibBuffers.empty()) {
            for (auto& buffer : deferredLibBuffers) {
                auto tree = SyntaxTree::fromBuffer(buffer, sourceManager, optionBag,
                                                   inheritedMacros);
                tree->isLibraryUnit = true;
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
                            auto readResult = sourceManager.readSource(path, /* library */ nullptr);
                            if (readResult) {
                                buffer = *readResult;
                                break;
                            }
                        }
                    }

                    if (buffer)
                        break;
                }

                if (buffer) {
                    auto tree = SyntaxTree::fromBuffer(buffer, sourceManager, optionBag,
                                                       inheritedMacros);
                    tree->isLibraryUnit = true;
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

SourceLibrary* SourceLoader::getOrAddLibrary(std::string_view name) {
    if (name.empty())
        return nullptr;

    auto nameStr = std::string(name);
    auto& lib = libraries[nameStr];
    if (!lib)
        lib = std::make_unique<SourceLibrary>(std::move(nameStr), (int)libraries.size());

    return lib.get();
}

void SourceLoader::addFilesInternal(std::string_view pattern, const fs::path& basePath,
                                    bool isLibraryFile, const SourceLibrary* library,
                                    const UnitEntry* unit, bool expandEnvVars) {
    SmallVector<fs::path> files;
    std::error_code ec;
    auto rank = svGlob(basePath, pattern, GlobMode::Files, files, expandEnvVars, ec);
    if (ec) {
        addError(pattern, ec);
        return;
    }

    fileEntries.reserve(fileEntries.size() + files.size());
    for (auto&& path : files) {
        auto [it, inserted] = fileIndex.try_emplace(path, fileEntries.size());
        if (inserted) {
            fileEntries.emplace_back(std::move(path), isLibraryFile, library, unit, rank);
        }
        else {
            // If this file is supposed to be in a separate unit but is already
            // included elsewhere we should error.
            auto& entry = fileEntries[it->second];
            if (unit || entry.unit) {
                errors.emplace_back(
                    fmt::format("'{}': included in multiple compilation units", getU8Str(path)));
                continue;
            }

            // If any of the times we see this is entry is for a non-library file,
            // then it's always a non-library file, hence the &=.
            entry.isLibraryFile &= isLibraryFile;

            if (library) {
                // If there is already a library for this entry and our rank is lower,
                // we overrule it. If it's higher, we ignore. If it's a tie, we remember
                // that fact for now and later we will issue an error if the tie is
                // never resolved.
                if (!entry.library || rank < entry.libraryRank) {
                    entry.library = library;
                    entry.libraryRank = rank;
                    entry.secondLib = nullptr;
                }
                else if (rank == entry.libraryRank) {
                    entry.secondLib = library;
                }
            }
        }
    }
}

void SourceLoader::createLibrary(const LibraryDeclarationSyntax& syntax, const fs::path& basePath) {
    auto libName = syntax.name.valueText();
    if (libName.empty())
        return;

    auto library = getOrAddLibrary(libName);
    for (auto filePath : syntax.filePaths) {
        auto spec = getPathFromSpec(*filePath);
        if (!spec.empty()) {
            addFilesInternal(spec, basePath, /* isLibraryFile */ true, library, nullptr,
                             /* expandEnvVars */ true);
        }
    }

    if (syntax.incDirClause) {
        for (auto filePath : syntax.incDirClause->filePaths) {
            auto spec = getPathFromSpec(*filePath);
            if (!spec.empty()) {
                SmallVector<fs::path> dirs;
                std::error_code ec;
                svGlob(basePath, spec, GlobMode::Directories, dirs,
                       /* expandEnvVars */ true, ec);

                if (ec) {
                    addError(spec, ec);
                }
                else {
                    auto& lid = library->includeDirs;
                    lid.reserve(lid.size() + dirs.size());
                    lid.insert(lid.end(), dirs.begin(), dirs.end());
                }
            }
        }
    }
}

SourceLoader::LoadResult SourceLoader::loadAndParse(const FileEntry& entry, const Bag& optionBag,
                                                    const SourceOptions& srcOptions,
                                                    uint64_t fileSortKey) {
    // TODO: error if secondLib is set

    SourceManager::BufferOrError buffer;
    if (entry.preloadedBuffer)
        buffer = entry.preloadedBuffer;
    else
        buffer = sourceManager.readSource(entry.path, entry.library, fileSortKey);

    if (!buffer)
        return std::pair{&entry, buffer.error()};

    if (entry.unit) {
        return std::pair{*buffer, entry.unit};
    }
    else if (!entry.isLibraryFile && srcOptions.singleUnit) {
        // If this file was directly specified (i.e. not via
        // a library mapping) and we're in single-unit mode,
        // collect it for later parsing.
        return std::pair{*buffer, false};
    }
    else if (srcOptions.librariesInheritMacros) {
        // If libraries inherit macros then we can't parse here,
        // we need to wait for the main compilation unit to be parsed.
        SLANG_ASSERT(entry.isLibraryFile);
        return std::pair{*buffer, true};
    }
    else {
        // Otherwise we can parse right away.
        auto tree = SyntaxTree::fromBuffer(*buffer, sourceManager, optionBag);
        if (entry.isLibraryFile || srcOptions.onlyLint)
            tree->isLibraryUnit = true;

        return tree;
    }
}

void SourceLoader::addError(const std::filesystem::path& path, std::error_code ec) {
    errors.emplace_back(fmt::format("'{}': {}", getU8Str(path), ec.message()));
}

} // namespace slang::driver
