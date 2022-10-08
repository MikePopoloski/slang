//------------------------------------------------------------------------------
// SyntaxTree.cpp
// Top-level parser interface
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/SyntaxTree.h"

#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/text/SourceManager.h"
#include "slang/util/TimeTrace.h"

namespace slang::syntax {

using namespace parsing;

SyntaxTree::SyntaxTree(SyntaxNode* root, SourceManager& sourceManager, BumpAllocator&& alloc,
                       std::shared_ptr<SyntaxTree> parent) :
    rootNode(root),
    sourceMan(sourceManager), alloc(std::move(alloc)), parentTree(std::move(parent)) {
    metadata = std::make_unique<ParserMetadata>(ParserMetadata::fromSyntax(*root));
    if (!metadata->eofToken && parentTree)
        metadata->eofToken = parentTree->getMetadata().eofToken;
}

SyntaxTree::~SyntaxTree() = default;

std::shared_ptr<SyntaxTree> SyntaxTree::fromFile(string_view path) {
    return fromFile(path, getDefaultSourceManager());
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromFile(string_view path, SourceManager& sourceManager,
                                                 const Bag& options) {
    SourceBuffer buffer = sourceManager.readSource(path);
    if (!buffer)
        return nullptr;
    return create(sourceManager, span(&buffer, 1), options, {}, false);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromFiles(span<const string_view> paths) {
    return fromFiles(paths, getDefaultSourceManager());
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromFiles(span<const string_view> paths,
                                                  SourceManager& sourceManager,
                                                  const Bag& options) {
    SmallVector<SourceBuffer, 4> buffers(paths.size(), UninitializedTag());
    for (auto path : paths) {
        SourceBuffer buffer = sourceManager.readSource(path);
        if (!buffer)
            return nullptr;

        buffers.push_back(buffer);
    }

    return create(sourceManager, buffers, options, {}, false);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromText(string_view text, string_view name,
                                                 string_view path) {
    return fromText(text, getDefaultSourceManager(), name, path);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromText(string_view text, SourceManager& sourceManager,
                                                 string_view name, string_view path,
                                                 const Bag& options) {
    SourceBuffer buffer = sourceManager.assignText(path, text);
    if (!buffer)
        return nullptr;

    if (!name.empty())
        sourceManager.addLineDirective(SourceLocation(buffer.id, 0), 2, name, 0);

    return create(sourceManager, span(&buffer, 1), options, {}, true);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromFileInMemory(string_view text,
                                                         SourceManager& sourceManager,
                                                         string_view name, string_view path,
                                                         const Bag& options) {
    SourceBuffer buffer = sourceManager.assignText(path, text);
    if (!buffer)
        return nullptr;

    if (!name.empty())
        sourceManager.addLineDirective(SourceLocation(buffer.id, 0), 2, name, 0);

    return create(sourceManager, span(&buffer, 1), options, {}, false);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromBuffer(const SourceBuffer& buffer,
                                                   SourceManager& sourceManager, const Bag& options,
                                                   MacroList inheritedMacros) {
    return create(sourceManager, span(&buffer, 1), options, inheritedMacros, false);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromBuffers(span<const SourceBuffer> buffers,
                                                    SourceManager& sourceManager,
                                                    const Bag& options, MacroList inheritedMacros) {
    return create(sourceManager, buffers, options, inheritedMacros, false);
}

SourceManager& SyntaxTree::getDefaultSourceManager() {
    static SourceManager instance;
    return instance;
}

SyntaxTree::SyntaxTree(SyntaxNode* root, SourceManager& sourceManager, BumpAllocator&& alloc,
                       Diagnostics&& diagnostics, ParserMetadata&& metadata,
                       std::vector<const DefineDirectiveSyntax*>&& macros, Bag options) :
    rootNode(root),
    sourceMan(sourceManager), alloc(std::move(alloc)), diagnosticsBuffer(std::move(diagnostics)),
    options_(std::move(options)), metadata(std::make_unique<ParserMetadata>(std::move(metadata))),
    macros(std::move(macros)) {
}

std::shared_ptr<SyntaxTree> SyntaxTree::create(SourceManager& sourceManager,
                                               span<const SourceBuffer> sources, const Bag& options,
                                               MacroList inheritedMacros, bool guess) {
    TimeTraceScope timeScope("parseFile"sv, [&] {
        if (sources.size() == 1)
            return std::string(sourceManager.getRawFileName(sources[0].id));
        else
            return "<multi-buffer>"s;
    });

    BumpAllocator alloc;
    Diagnostics diagnostics;
    Preprocessor preprocessor(sourceManager, alloc, diagnostics, options, inheritedMacros);

    for (auto it = sources.rbegin(); it != sources.rend(); it++)
        preprocessor.pushSource(*it);

    Parser parser(preprocessor, options);

    SyntaxNode* root;
    if (!guess)
        root = &parser.parseCompilationUnit();
    else {
        root = &parser.parseGuess();
        if (!parser.isDone())
            return create(sourceManager, sources, options, inheritedMacros, false);
    }

    return std::shared_ptr<SyntaxTree>(new SyntaxTree(root, sourceManager, std::move(alloc),
                                                      std::move(diagnostics), parser.getMetadata(),
                                                      preprocessor.getDefinedMacros(), options));
}

} // namespace slang::syntax
