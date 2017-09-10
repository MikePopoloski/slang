//------------------------------------------------------------------------------
// SyntaxTree.h
// Top-level parser interface.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "diagnostics/Diagnostics.h"
#include "lexing/Preprocessor.h"
#include "text/SourceManager.h"
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
    SyntaxTree(SyntaxTree&& other) = default;
    SyntaxTree& operator=(SyntaxTree&&) = default;

    // not copyable
    SyntaxTree(const SyntaxTree&) = delete;
    SyntaxTree& operator=(const SyntaxTree&) = delete;

    /// Creates a syntax tree from a full compilation unit.
    static SyntaxTree fromFile(string_view path) {
        return fromFile(path, getDefaultSourceManager());
    }

    /// Creates a syntax tree by guessing at what might be in the given source snippet.
    static SyntaxTree fromText(string_view text, BufferID existingBuffer = BufferID()) {
        return fromText(text, getDefaultSourceManager(), existingBuffer);
    }

    static SyntaxTree fromFile(string_view path, SourceManager& sourceManager) {
        return create(sourceManager, sourceManager.readSource(path), false);
    }

    static SyntaxTree fromText(string_view text, SourceManager& sourceManager,
                               BufferID existingBuffer = BufferID()) {
        SourceBuffer buffer = existingBuffer ?
            sourceManager.appendText(existingBuffer, text) : sourceManager.assignText(text);

        return create(sourceManager, buffer, true);
    }

    /// Gets any diagnostics generated while parsing.
    Diagnostics& diagnostics() { return diagnosticsBuffer; }

    /// Helper function to get the set of diagnostics as a human-friendly string.
    std::string reportDiagnostics() {
        return DiagnosticWriter(sourceMan).report(diagnosticsBuffer);
    }

    /// Gets the allocator containing the memory for the parse tree.
    BumpAllocator& allocator() { return alloc; }

    /// Gets the source manager used to build the syntax tree.
    SourceManager& sourceManager() { return sourceMan; }
    const SourceManager& sourceManager() const { return sourceMan; }

    /// Gets the root of the syntax tree.
    const SyntaxNode& root() const { return *rootNode; }

    /// The ID of the source buffer used to create the syntax tree.
    BufferID bufferID() const { return bufferID_; }

    /// This is a shared default source manager for cases where the user doesn't
    /// care about managing the lifetime of loaded source. Note that all of
    /// the source loaded by this thing will live in memory for the lifetime of
    /// the process.
    static SourceManager& getDefaultSourceManager() {
        static SourceManager instance;
        return instance;
    }

private:
    SyntaxTree(const SyntaxNode* root, SourceManager& sourceManager,
               BumpAllocator&& alloc, Diagnostics&& diagnostics, BufferID bufferID) :
        rootNode(root), sourceMan(sourceManager),
        alloc(std::move(alloc)), diagnosticsBuffer(std::move(diagnostics)), bufferID_(bufferID) {}

    static SyntaxTree create(SourceManager& sourceManager, SourceBuffer source, bool guess) {
        BumpAllocator alloc;
        Diagnostics diagnostics;
        Preprocessor preprocessor(sourceManager, alloc, diagnostics);
        preprocessor.pushSource(source);

        Parser parser(preprocessor);
        return SyntaxTree(guess ? &parser.parseGuess() : &parser.parseCompilationUnit(),
                          sourceManager, std::move(alloc), std::move(diagnostics), source.id);
    }

    const SyntaxNode* rootNode;
    SourceManager& sourceMan;
    BumpAllocator alloc;
    Diagnostics diagnosticsBuffer;
    BufferID bufferID_;
};

}
