//------------------------------------------------------------------------------
// SyntaxTree.cpp
// Top-level parser interface
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/SyntaxTree.h"

#include "slang/parsing/Parser.h"
#include "slang/parsing/ParserMetadata.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/text/SourceManager.h"
#include "slang/util/TimeTrace.h"

namespace slang::syntax {

using namespace parsing;

SyntaxTree::SyntaxTree(SyntaxNode* root, SourceManager& sourceManager, BumpAllocator&& alloc,
                       const SourceLibrary* library, const std::shared_ptr<SyntaxTree>& parent) :
    rootNode(root), library(library), sourceMan(sourceManager), alloc(std::move(alloc)) {
    metadata = std::make_unique<ParserMetadata>(ParserMetadata::fromSyntax(*root));
    if (parent) { // copy parent's info
        for (size_t i = 0; i < parent->macros.size(); ++i) {
            auto macro = parent->macros[i];
            if (macro)
                macro = deepClone(*macro, this->alloc);
            macros.push_back(macro);
        }
        if (!metadata->eofToken)
            metadata->eofToken = parent->getMetadata().eofToken.deepClone(this->alloc);
    }
}

SyntaxTree::~SyntaxTree() = default;

SyntaxTree::TreeOrError SyntaxTree::fromFile(std::string_view path) {
    return fromFile(path, getDefaultSourceManager());
}

SyntaxTree::TreeOrError SyntaxTree::fromFile(std::string_view path, SourceManager& sourceManager,
                                             const Bag& options) {
    auto buffer = sourceManager.readSource(path, /* library */ nullptr);
    if (!buffer)
        return nonstd::make_unexpected(std::pair{buffer.error(), path});
    return create(sourceManager, std::span(&buffer.value(), 1), options, {}, false);
}

SyntaxTree::TreeOrError SyntaxTree::fromFiles(std::span<const std::string_view> paths) {
    return fromFiles(paths, getDefaultSourceManager());
}

SyntaxTree::TreeOrError SyntaxTree::fromFiles(std::span<const std::string_view> paths,
                                              SourceManager& sourceManager, const Bag& options) {
    SmallVector<SourceBuffer, 4> buffers(paths.size(), UninitializedTag());
    for (auto path : paths) {
        auto buffer = sourceManager.readSource(path, /* library */ nullptr);
        if (!buffer)
            return nonstd::make_unexpected(std::pair{buffer.error(), path});

        buffers.push_back(*buffer);
    }

    return create(sourceManager, buffers, options, {}, false);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromText(std::string_view text, std::string_view name,
                                                 std::string_view path) {
    return fromText(text, getDefaultSourceManager(), name, path);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromText(std::string_view text, const Bag& options,
                                                 std::string_view name, std::string_view path) {
    return fromText(text, getDefaultSourceManager(), name, path, options);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromText(std::string_view text,
                                                 SourceManager& sourceManager,
                                                 std::string_view name, std::string_view path,
                                                 const Bag& options, const SourceLibrary* library) {
    SourceBuffer buffer = sourceManager.assignText(path, text, {}, library);
    if (!buffer)
        return nullptr;

    if (!name.empty())
        sourceManager.addLineDirective(SourceLocation(buffer.id, 0), 2, name, 0);

    return create(sourceManager, std::span(&buffer, 1), options, {}, true);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromFileInMemory(std::string_view text,
                                                         SourceManager& sourceManager,
                                                         std::string_view name,
                                                         std::string_view path,
                                                         const Bag& options) {
    SourceBuffer buffer = sourceManager.assignText(path, text);
    if (!buffer)
        return nullptr;

    if (!name.empty())
        sourceManager.addLineDirective(SourceLocation(buffer.id, 0), 2, name, 0);

    return create(sourceManager, std::span(&buffer, 1), options, {}, false);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromBuffer(const SourceBuffer& buffer,
                                                   SourceManager& sourceManager, const Bag& options,
                                                   MacroList inheritedMacros) {
    return create(sourceManager, std::span(&buffer, 1), options, inheritedMacros, false);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromBuffers(std::span<const SourceBuffer> buffers,
                                                    SourceManager& sourceManager,
                                                    const Bag& options, MacroList inheritedMacros) {
    return create(sourceManager, buffers, options, inheritedMacros, false);
}

SourceManager& SyntaxTree::getDefaultSourceManager() {
    static SourceManager instance;
    return instance;
}

SyntaxTree::SyntaxTree(SyntaxNode* root, const SourceLibrary* library, SourceManager& sourceManager,
                       BumpAllocator&& alloc, Diagnostics&& diagnostics, ParserMetadata&& metadata,
                       std::vector<const DefineDirectiveSyntax*>&& macros, Bag options) :
    rootNode(root), library(library), sourceMan(sourceManager), alloc(std::move(alloc)),
    diagnosticsBuffer(std::move(diagnostics)), options_(std::move(options)),
    metadata(std::make_unique<ParserMetadata>(std::move(metadata))), macros(std::move(macros)) {
}

std::shared_ptr<SyntaxTree> SyntaxTree::create(SourceManager& sourceManager,
                                               std::span<const SourceBuffer> sources,
                                               const Bag& options, MacroList inheritedMacros,
                                               bool guess) {
    if (sources.empty())
        SLANG_THROW(std::invalid_argument("sources cannot be empty"));

    TimeTraceScope timeScope("parseFile"sv, [&] {
        if (sources.size() == 1)
            return std::string(sourceManager.getRawFileName(sources[0].id));
        else
            return "<multi-buffer>"s;
    });

    BumpAllocator alloc;
    Diagnostics diagnostics;
    Preprocessor preprocessor(sourceManager, alloc, diagnostics, options, inheritedMacros);

    const SourceLibrary* library = nullptr;
    for (auto it = sources.rbegin(); it != sources.rend(); it++) {
        preprocessor.pushSource(*it);

        if (it != sources.rbegin() && library != it->library) {
            SLANG_THROW(std::invalid_argument("All sources provided to a single SyntaxTree must be "
                                              "from the same source library"));
        }

        library = it->library;
    }

    Parser parser(preprocessor, options);

    SyntaxNode* root;
    if (!guess)
        root = &parser.parseCompilationUnit();
    else {
        root = &parser.parseGuess();
        if (!parser.isDone())
            return create(sourceManager, sources, options, inheritedMacros, false);
    }

    return std::shared_ptr<SyntaxTree>(
        new SyntaxTree(root, library, sourceManager, std::move(alloc), std::move(diagnostics),
                       parser.getMetadata(), preprocessor.getDefinedMacros(), options));
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromLibraryMapFile(std::string_view path,
                                                           SourceManager& sourceManager,
                                                           const Bag& options) {
    auto buffer = sourceManager.readSource(path, /* library */ nullptr);
    if (!buffer)
        return nullptr;

    return fromLibraryMapBuffer(*buffer, sourceManager, options);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromLibraryMapText(std::string_view text,
                                                           SourceManager& sourceManager,
                                                           std::string_view name,
                                                           std::string_view path,
                                                           const Bag& options) {
    SourceBuffer buffer = sourceManager.assignText(path, text);
    if (!buffer)
        return nullptr;

    if (!name.empty())
        sourceManager.addLineDirective(SourceLocation(buffer.id, 0), 2, name, 0);

    return fromLibraryMapBuffer(buffer, sourceManager, options);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromLibraryMapBuffer(const SourceBuffer& buffer,
                                                             SourceManager& sourceManager,
                                                             const Bag& options) {
    BumpAllocator alloc;
    Diagnostics diagnostics;
    Preprocessor preprocessor(sourceManager, alloc, diagnostics, options);
    preprocessor.pushSource(buffer);

    Parser parser(preprocessor, options);
    auto& root = parser.parseLibraryMap();

    return std::shared_ptr<SyntaxTree>(
        new SyntaxTree(&root, nullptr, sourceManager, std::move(alloc), std::move(diagnostics),
                       parser.getMetadata(), preprocessor.getDefinedMacros(), options));
}

} // namespace slang::syntax
