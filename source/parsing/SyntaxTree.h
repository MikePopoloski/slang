//------------------------------------------------------------------------------
// SyntaxTree.h
// Top-level parser interface.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <memory>

#include "diagnostics/Diagnostics.h"
#include "lexing/Preprocessor.h"
#include "text/SourceManager.h"
#include "util/Bag.h"
#include "util/BumpAllocator.h"

#include "Parser.h"

namespace slang {

/// The SyntaxTree is the easiest way to interface with the lexer / preprocessor /
/// parser stack. Give it some source text and it produces a parse tree.
///
/// The SyntaxTree object owns all of the memory for the parse tree, so it must
/// live for as long as you need to access its syntax nodes.
class SyntaxTree {
public:
    SyntaxTree(SyntaxNode* root, SourceManager& sourceManager, BumpAllocator&& alloc,
               std::shared_ptr<SyntaxTree> parent = nullptr) :
        rootNode(root), sourceMan(sourceManager), alloc(std::move(alloc)), parentTree(std::move(parent)) {
        if (parentTree)
            eof = parentTree->eof;
    }

    SyntaxTree(SyntaxTree&& other) = default;
    SyntaxTree& operator=(SyntaxTree&&) = default;

    /// Creates a syntax tree from a full compilation unit.
    static std::shared_ptr<SyntaxTree> fromFile(string_view path) {
        return fromFile(path, getDefaultSourceManager());
    }

    /// Creates a syntax tree by guessing at what might be in the given source snippet.
    static std::shared_ptr<SyntaxTree> fromText(string_view text, string_view name = "") {
        return fromText(text, getDefaultSourceManager(), name);
    }

    static std::shared_ptr<SyntaxTree> fromFile(string_view path, SourceManager& sourceManager,
                                                const Bag& options = {}) {
        SourceBuffer buffer = sourceManager.readSource(path);
        if (!buffer)
            return nullptr;
        return create(sourceManager, buffer, options, false);
    }

    static std::shared_ptr<SyntaxTree> fromText(string_view text, SourceManager& sourceManager,
                                                string_view name = "",
                                                const Bag& options = {}) {
        return create(sourceManager, sourceManager.assignText(name, text), options, true);
    }

    static std::shared_ptr<SyntaxTree> fromBuffer(const SourceBuffer& buffer, SourceManager& sourceManager,
                                                  const Bag& options = {}) {
        return create(sourceManager, buffer, options, false);
    }

    /// Gets any diagnostics generated while parsing.
    Diagnostics& diagnostics() { return diagnosticsBuffer; }

    /// Gets the allocator containing the memory for the parse tree.
    BumpAllocator& allocator() { return alloc; }

    /// Gets the source manager used to build the syntax tree.
    SourceManager& sourceManager() { return sourceMan; }
    const SourceManager& sourceManager() const { return sourceMan; }

    /// Gets the root of the syntax tree.
    SyntaxNode& root() { return *rootNode; }
    const SyntaxNode& root() const { return *rootNode; }

    /// Gets the EndOfFile token marking the end of the input source text.
    /// This is useful if, for example, the tree doesn't represent a whole
    /// compilation unit and you still want to see the trailing trivia.
    Token getEOFToken() const { return eof; }

    /// The options used to construct the syntax tree.
    const Bag& options() const { return options_; }

    /// Gets the parent syntax tree, if there is one. Otherwise returns nullptr.
    /// Most syntax trees don't have a parent; this is for cases where a given tree is
    /// derived from another and relies on the parent tree's memory remaining valid for
    /// the lifetime of the child tree.
    const SyntaxTree* getParentTree() const { return parentTree.get(); }

    /// This is a shared default source manager for cases where the user doesn't
    /// care about managing the lifetime of loaded source. Note that all of
    /// the source loaded by this thing will live in memory for the lifetime of
    /// the process.
    static SourceManager& getDefaultSourceManager() {
        static SourceManager instance;
        return instance;
    }

private:
    SyntaxTree(SyntaxNode* root, SourceManager& sourceManager,
               BumpAllocator&& alloc, Diagnostics&& diagnostics,
               const Bag& options, Token eof) :
        rootNode(root), sourceMan(sourceManager),
        alloc(std::move(alloc)), diagnosticsBuffer(std::move(diagnostics)),
        options_(options), eof(eof) {}

    static std::shared_ptr<SyntaxTree> create(SourceManager& sourceManager, SourceBuffer source,
                                              const Bag& options, bool guess) {
        BumpAllocator alloc;
        Diagnostics diagnostics;
        Preprocessor preprocessor(sourceManager, alloc, diagnostics, options);
        preprocessor.pushSource(source);

        Parser parser(preprocessor, options);

        SyntaxNode* root;
        if (!guess)
            root = &parser.parseCompilationUnit();
        else {
            root = &parser.parseGuess();
            if (!parser.isDone()) {
                throw std::logic_error("Source passed to SyntaxTree::fromText represents "
                                       "more than one logical node.");
            }
        }

        return std::shared_ptr<SyntaxTree>(new SyntaxTree(
            root, sourceManager, std::move(alloc),
            std::move(diagnostics), options, parser.getEOFToken()));
    }

    SyntaxNode* rootNode;
    SourceManager& sourceMan;
    BumpAllocator alloc;
    Diagnostics diagnosticsBuffer;
    Bag options_;
    std::shared_ptr<SyntaxTree> parentTree;
    Token eof;
};

}
