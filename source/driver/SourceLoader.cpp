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

void SourceLoader::addFiles(std::string_view pattern) {
    SmallVector<fs::path> files;
    svGlob("", pattern, GlobMode::Files, files);

    directFiles.insert(directFiles.end(), files.begin(), files.end());
}

bool SourceLoader::addLibraryMaps(std::string_view pattern) {
    // TODO: should this allow patterns / multiple maps?

    // Load and parse the map file right away; we need it to
    // figure out what other sources to load.
    // TODO: make readSource take a fs::path?
    auto buffer = sourceManager.readSource(widen(pattern));
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

SourceLoader::SyntaxTreeList SourceLoader::loadAndParseSources() {
    // SyntaxTreeList results;
    // if (srcOptions.singleUnit) {
    //     auto tree = SyntaxTree::fromBuffers(buffers, sourceManager, optionBag);
    //     if (srcOptions.onlyLint)
    //         tree->isLibrary = true;

    //    results.emplace_back(std::move(tree));
    //}
    // else {
    //    auto parse = [&](const SourceBuffer& buffer) {
    //        auto tree = SyntaxTree::fromBuffer(buffer, sourceManager, optionBag);
    //        if (srcOptions.onlyLint)
    //            tree->isLibrary = true;

    //        return tree;
    //    };

    //    // If there are enough buffers to parse and the user hasn't disabled
    //    // the use of threads, do the parsing via a thread pool.
    //    if (buffers.size() > 4 && srcOptions.numThreads != 1u) {
    //        ThreadPool threadPool(srcOptions.numThreads.value_or(0u));

    //        std::vector<std::future<std::shared_ptr<SyntaxTree>>> tasks;
    //        tasks.reserve(buffers.size());
    //        for (auto& buffer : buffers)
    //            tasks.emplace_back(threadPool.submit(parse, buffer));

    //        threadPool.waitForAll();
    //        for (auto& task : tasks)
    //            results.emplace_back(task.get());
    //    }
    //    else {
    //        for (auto& buffer : buffers)
    //            results.emplace_back(parse(buffer));
    //    }
    //}

    // std::span<const DefineDirectiveSyntax* const> inheritedMacros;
    // if (srcOptions.librariesInheritMacros)
    //     inheritedMacros = results.back()->getDefinedMacros();

    // bool ok = true;
    // for (auto& file : options.libraryFiles) {
    //     SourceBuffer buffer = readSource(file);
    //     if (!buffer) {
    //         ok = false;
    //         continue;
    //     }

    //    auto tree = SyntaxTree::fromBuffer(buffer, sourceManager, optionBag, inheritedMacros);
    //    tree->isLibrary = true;
    //    syntaxTrees.emplace_back(std::move(tree));
    //}

    // if (!options.libDirs.empty()) {
    //     std::vector<fs::path> directories;
    //     directories.reserve(options.libDirs.size());
    //     for (auto& dir : options.libDirs)
    //         directories.emplace_back(widen(dir));

    //    flat_hash_set<std::string_view> uniqueExtensions;
    //    uniqueExtensions.emplace(".v"sv);
    //    uniqueExtensions.emplace(".sv"sv);
    //    for (auto& ext : options.libExts)
    //        uniqueExtensions.emplace(ext);

    //    std::vector<fs::path> extensions;
    //    for (auto ext : uniqueExtensions)
    //        extensions.emplace_back(widen(ext));

    //    // If library directories are specified, see if we have any unknown instantiations
    //    // or package names for which we should search for additional source files to load.
    //    flat_hash_set<std::string_view> knownNames;
    //    auto addKnownNames = [&](const std::shared_ptr<SyntaxTree>& tree) {
    //        auto& meta = tree->getMetadata();
    //        for (auto& [n, _] : meta.nodeMap) {
    //            auto decl = &n->as<ModuleDeclarationSyntax>();
    //            std::string_view name = decl->header->name.valueText();
    //            if (!name.empty())
    //                knownNames.emplace(name);
    //        }

    //        for (auto classDecl : meta.classDecls) {
    //            std::string_view name = classDecl->name.valueText();
    //            if (!name.empty())
    //                knownNames.emplace(name);
    //        }
    //    };

    //    auto findMissingNames = [&](const std::shared_ptr<SyntaxTree>& tree,
    //                                flat_hash_set<std::string_view>& missing) {
    //        auto& meta = tree->getMetadata();
    //        for (auto name : meta.globalInstances) {
    //            if (knownNames.find(name) == knownNames.end())
    //                missing.emplace(name);
    //        }

    //        for (auto idName : meta.classPackageNames) {
    //            std::string_view name = idName->identifier.valueText();
    //            if (!name.empty() && knownNames.find(name) == knownNames.end())
    //                missing.emplace(name);
    //        }

    //        for (auto importDecl : meta.packageImports) {
    //            for (auto importItem : importDecl->items) {
    //                std::string_view name = importItem->package.valueText();
    //                if (!name.empty() && knownNames.find(name) == knownNames.end())
    //                    missing.emplace(name);
    //            }
    //        }

    //        for (auto intf : meta.interfacePorts) {
    //            std::string_view name = intf->nameOrKeyword.valueText();
    //            if (knownNames.find(name) == knownNames.end())
    //                missing.emplace(name);
    //        }
    //    };

    //    for (auto& tree : syntaxTrees)
    //        addKnownNames(tree);

    //    flat_hash_set<std::string_view> missingNames;
    //    for (auto& tree : syntaxTrees)
    //        findMissingNames(tree, missingNames);

    //    // Keep loading new files as long as we are making forward progress.
    //    flat_hash_set<std::string_view> nextMissingNames;
    //    while (true) {
    //        for (auto name : missingNames) {
    //            SourceBuffer buffer;
    //            for (auto& dir : directories) {
    //                fs::path path(dir);
    //                path /= name;

    //                for (auto& ext : extensions) {
    //                    path.replace_extension(ext);
    //                    if (!sourceManager.isCached(path)) {
    //                        buffer = sourceManager.readSource(path);
    //                        if (buffer)
    //                            break;
    //                    }
    //                }

    //                if (buffer)
    //                    break;
    //            }

    //            if (buffer) {
    //                auto tree = SyntaxTree::fromBuffer(buffer, sourceManager, optionBag,
    //                                                   inheritedMacros);
    //                tree->isLibrary = true;
    //                syntaxTrees.emplace_back(tree);

    //                addKnownNames(tree);
    //                findMissingNames(tree, nextMissingNames);
    //            }
    //        }

    //        if (nextMissingNames.empty())
    //            break;

    //        missingNames = std::move(nextMissingNames);
    //        nextMissingNames = {};
    //    }
    //}

    // if (ok) {
    //     Diagnostics pragmaDiags = diagEngine.setMappingsFromPragmas();
    //     for (auto& diag : pragmaDiags)
    //         diagEngine.issue(diag);
    // }

    // return results;
    return {};
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
