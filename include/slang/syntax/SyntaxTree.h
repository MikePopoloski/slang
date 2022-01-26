//------------------------------------------------------------------------------
//! @file SyntaxTree.h
//! @brief Top-level parser interface
//
// File is under the MIT license; see LICENSE for details
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
    /// Indicates whether this syntax tree represents a "library" compilation unit,
    /// which means that modules declared within it are not automatically instantiated.
    bool isLibrary = false;

    SyntaxTree(SyntaxNode* root, SourceManager& sourceManager, BumpAllocator&& alloc,
               std::shared_ptr<SyntaxTree> parent = nullptr);

    SyntaxTree(SyntaxTree&& other) = default;

    /// Creates a syntax tree from a full compilation unit.
    /// @a path is the path to the source file on disk.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromFile(string_view path);

    /// Creates a syntax tree by guessing at what might be in the given source snippet.
    /// @a text is the actual source code text.
    /// @a name is an optional name to give to the loaded source buffer.
    /// @a path is an optional path to give to the loaded source buffer.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromText(string_view text, string_view name = "source",
                                                string_view path = "");

    /// Creates a syntax tree from a full compilation unit.
    /// @a path is the path to the source file on disk.
    /// @a sourceManager is the manager that owns all of the loaded source code.
    /// @a options is an optional bag of lexer, preprocessor, and parser options.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromFile(string_view path, SourceManager& sourceManager,
                                                const Bag& options = {});

    /// Creates a syntax tree by guessing at what might be in the given source snippet.
    /// @a text is the actual source code text.
    /// @a sourceManager is the manager that owns all of the loaded source code.
    /// @a name is an optional name to give to the loaded source buffer.
    /// @a path is an optional path to give to the loaded source buffer.
    /// @a options is an optional bag of lexer, preprocessor, and parser options.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromText(string_view text, SourceManager& sourceManager,
                                                string_view name = "source"sv,
                                                string_view path = "", const Bag& options = {});

    /// Creates a syntax tree from an already loaded source buffer.
    /// @a buffer is the loaded source buffer.
    /// @a sourceManager is the manager that owns the buffer.
    /// @a options is an optional bag of lexer, preprocessor, and parser options.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromBuffer(const SourceBuffer& buffer,
                                                  SourceManager& sourceManager,
                                                  const Bag& options = {});

    /// Creates a syntax tree by concatenating several loaded source buffers.
    /// @a buffers is the list of buffers that should be concatenated to form
    /// the compilation unit to parse.
    /// @a sourceManager is the manager that owns the buffers.
    /// @a options is an optional bag of lexer, preprocessor, and parser options.
    /// @return the created and parsed syntax tree.
    static std::shared_ptr<SyntaxTree> fromBuffers(span<const SourceBuffer> buffers,
                                                   SourceManager& sourceManager,
                                                   const Bag& options = {});

    /// Gets any diagnostics generated while parsing.
    Diagnostics& diagnostics() { return diagnosticsBuffer; }

    /// Gets the allocator containing the memory for the parse tree.
    BumpAllocator& allocator() { return alloc; }

    /// Gets the source manager used to build the syntax tree.
    SourceManager& sourceManager() { return sourceMan; }

    /// Gets the source manager used to build the syntax tree.
    const SourceManager& sourceManager() const { return sourceMan; }

    /// Gets the root of the syntax tree.
    SyntaxNode& root() { return *rootNode; }

    /// Gets the root of the syntax tree.
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

    /// Gets various bits of metadata collected during parsing.
    const Parser::Metadata& getMetadata() const { return metadata; }

    /// This is a shared default source manager for cases where the user doesn't
    /// care about managing the lifetime of loaded source. Note that all of
    /// the source loaded by this thing will live in memory for the lifetime of
    /// the process.
    static SourceManager& getDefaultSourceManager();

private:
    SyntaxTree(SyntaxNode* root, SourceManager& sourceManager, BumpAllocator&& alloc,
               Diagnostics&& diagnostics, Parser::Metadata&& metadata, Bag options, Token eof);

    static std::shared_ptr<SyntaxTree> create(SourceManager& sourceManager,
                                              span<const SourceBuffer> source, const Bag& options,
                                              bool guess);

    SyntaxNode* rootNode;
    SourceManager& sourceMan;
    Parser::Metadata metadata;
    BumpAllocator alloc;
    Diagnostics diagnosticsBuffer;
    Bag options_;
    std::shared_ptr<SyntaxTree> parentTree;
    Token eof;
};

} // namespace slang
