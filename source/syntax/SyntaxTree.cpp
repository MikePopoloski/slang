//------------------------------------------------------------------------------
// SyntaxTree.cpp
// Top-level parser interface
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/syntax/SyntaxTree.h"

#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/text/SourceManager.h"

namespace slang {

SyntaxTree::SyntaxTree(SyntaxNode* root, SourceManager& sourceManager, BumpAllocator&& alloc,
                       std::shared_ptr<SyntaxTree> parent) :
    rootNode(root),
    sourceMan(sourceManager), alloc(std::move(alloc)), parentTree(std::move(parent)) {
    if (parentTree)
        eof = parentTree->eof;
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromFile(string_view path) {
    return fromFile(path, getDefaultSourceManager());
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromText(string_view text, string_view name) {
    return fromText(text, getDefaultSourceManager(), name);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromFile(string_view path, SourceManager& sourceManager,
                                                 const Bag& options) {
    SourceBuffer buffer = sourceManager.readSource(path);
    if (!buffer)
        return nullptr;
    return create(sourceManager, span(&buffer, 1), options, false);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromText(string_view text, SourceManager& sourceManager,
                                                 string_view name, const Bag& options) {
    SourceBuffer buffer = sourceManager.assignText(name, text);
    if (!buffer)
        return nullptr;
    return create(sourceManager, span(&buffer, 1), options, true);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromBuffer(const SourceBuffer& buffer,
                                                   SourceManager& sourceManager,
                                                   const Bag& options) {
    return create(sourceManager, span(&buffer, 1), options, false);
}

std::shared_ptr<SyntaxTree> SyntaxTree::fromBuffers(span<const SourceBuffer> buffers,
                                                    SourceManager& sourceManager,
                                                    const Bag& options) {
    return create(sourceManager, buffers, options, false);
}

SourceManager& SyntaxTree::getDefaultSourceManager() {
    static SourceManager instance;
    return instance;
}

SyntaxTree::SyntaxTree(SyntaxNode* root, SourceManager& sourceManager, BumpAllocator&& alloc,
                       Diagnostics&& diagnostics, Parser::Metadata&& metadata, Bag options,
                       Token eof) :
    rootNode(root),
    sourceMan(sourceManager), metadata(std::move(metadata)), alloc(std::move(alloc)),
    diagnosticsBuffer(std::move(diagnostics)), options_(std::move(options)), eof(eof) {
}

std::shared_ptr<SyntaxTree> SyntaxTree::create(SourceManager& sourceManager,
                                               span<const SourceBuffer> sources, const Bag& options,
                                               bool guess) {
    BumpAllocator alloc;
    Diagnostics diagnostics;
    Preprocessor preprocessor(sourceManager, alloc, diagnostics, options);

    for (auto it = sources.rbegin(); it != sources.rend(); it++)
        preprocessor.pushSource(*it);

    Parser parser(preprocessor, options);

    SyntaxNode* root;
    if (!guess)
        root = &parser.parseCompilationUnit();
    else {
        root = &parser.parseGuess();
        if (!parser.isDone())
            return create(sourceManager, sources, options, false);
    }

    return std::shared_ptr<SyntaxTree>(new SyntaxTree(root, sourceManager, std::move(alloc),
                                                      std::move(diagnostics), parser.getMetadata(),
                                                      options, parser.getEOFToken()));
}

} // namespace slang
