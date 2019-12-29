//------------------------------------------------------------------------------
// SyntaxTree.h
// Top-level parser interface.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <memory>

#include "slang/diagnostics/Diagnostics.h"
#include "slang/parsing/Parser.h"
#include "slang/util/Bag.h"
#include "slang/util/BumpAllocator.h"

namespace slang {

class SourceManager;
struct SourceBuffer;

/// The SyntaxTree is the easiest way to interface with the lexer / preprocessor /
/// parser stack. Give it some source text and it produces a parse tree.
///
/// The SyntaxTree object owns all of the memory for the parse tree, so it must
/// live for as long as you need to access its syntax nodes.
class SyntaxTree {
public:
    SyntaxTree(SyntaxNode* root, SourceManager& sourceManager, BumpAllocator&& alloc,
               std::shared_ptr<SyntaxTree> parent = nullptr);

    SyntaxTree(SyntaxTree&& other) = default;

    /// Creates a syntax tree from a full compilation unit.
    static std::shared_ptr<SyntaxTree> fromFile(string_view path);

    /// Creates a syntax tree by guessing at what might be in the given source snippet.
    static std::shared_ptr<SyntaxTree> fromText(string_view text, string_view name = "");

    static std::shared_ptr<SyntaxTree> fromFile(string_view path, SourceManager& sourceManager,
                                                const Bag& options = {});

    static std::shared_ptr<SyntaxTree> fromText(string_view text, SourceManager& sourceManager,
                                                string_view name = "", const Bag& options = {});

    static std::shared_ptr<SyntaxTree> fromBuffer(const SourceBuffer& buffer,
                                                  SourceManager& sourceManager,
                                                  const Bag& options = {});

    static std::shared_ptr<SyntaxTree> fromBuffers(span<const SourceBuffer> buffers,
                                                   SourceManager& sourceManager,
                                                   const Bag& options = {});

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

    /// Gets metadata that was in effect when various syntax nodes were parsed (such as various
    /// bits of preprocessor state).
    const Parser::MetadataMap& getMetadataMap() const { return metadataMap; }

    /// This is a shared default source manager for cases where the user doesn't
    /// care about managing the lifetime of loaded source. Note that all of
    /// the source loaded by this thing will live in memory for the lifetime of
    /// the process.
    static SourceManager& getDefaultSourceManager();

private:
    SyntaxTree(SyntaxNode* root, SourceManager& sourceManager, BumpAllocator&& alloc,
               Diagnostics&& diagnostics, Parser::MetadataMap&& metadataMap, Bag options,
               Token eof);

    static std::shared_ptr<SyntaxTree> create(SourceManager& sourceManager,
                                              span<const SourceBuffer> source, const Bag& options,
                                              bool guess);

    SyntaxNode* rootNode;
    SourceManager& sourceMan;
    Parser::MetadataMap metadataMap;
    BumpAllocator alloc;
    Diagnostics diagnosticsBuffer;
    Bag options_;
    std::shared_ptr<SyntaxTree> parentTree;
    Token eof;
};

} // namespace slang
