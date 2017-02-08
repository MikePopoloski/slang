//------------------------------------------------------------------------------
// SyntaxTree.h
// Top-level parser interface.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "BumpAllocator.h"
#include "Diagnostics.h"
#include "Parser.h"
#include "Preprocessor.h"
#include "SourceManager.h"
#include "StringRef.h"

namespace slang {


/// The SyntaxTree is the easiest way to interface with the lexer / preprocessor /
/// parser stack. Give it some source text and it produces a parse tree.
///
/// The template argument specifies the kind of syntax node you're expecting to parse.
/// The only types you can use here are the ones that have a corresponding template
/// specialization in the Parser class.
///
/// The SyntaxTree object owns all of the memory for the parse tree, so it must
/// live for as long as you need to access that.
class SyntaxTree {
public:
    SyntaxTree(SyntaxTree&& other) = default;
    SyntaxTree& operator=(SyntaxTree&&) = default;

    // not copyable
    SyntaxTree(const SyntaxTree&) = delete;
    SyntaxTree& operator=(const SyntaxTree&) = delete;

    /// Creates a specialized syntax tree from text in memory.
    template<typename T>
    static SyntaxTree fromText(StringRef text) {
        return fromText<T>(text, getDefaultSourceManager());
    }

    template<typename T>
    static SyntaxTree fromText(StringRef text, SourceManager& sourceManager) {
        return create<T>(sourceManager, sourceManager.assignText(text));
    }

    /// Creates a syntax tree from a full compilation unit.
    static SyntaxTree fromFile(StringRef path) {
        return fromFile(path, getDefaultSourceManager());
    }

    static SyntaxTree fromText(StringRef text) {
        return fromText(text, getDefaultSourceManager());
    }

    static SyntaxTree fromFile(StringRef path, SourceManager& sourceManager) {
        return create<CompilationUnitSyntax>(sourceManager, sourceManager.readSource(path));
    }

    static SyntaxTree fromText(StringRef text, SourceManager& sourceManager) {
        return create<CompilationUnitSyntax>(sourceManager, sourceManager.assignText(text));
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

    const SyntaxNode* root() const { return rootNode; }

private:
    SyntaxTree(const SyntaxNode* root, SourceManager& sourceManager,
               BumpAllocator&& alloc, Diagnostics&& diagnostics) :
        rootNode(root), sourceMan(sourceManager),
        alloc(std::move(alloc)), diagnosticsBuffer(std::move(diagnostics)) {}

    template<typename T>
    static SyntaxTree create(SourceManager& sourceManager, SourceBuffer source) {
        BumpAllocator alloc;
        Diagnostics diagnostics;
        Preprocessor preprocessor(sourceManager, alloc, diagnostics);
        preprocessor.pushSource(source);

        Parser parser(preprocessor);
        return SyntaxTree(parser.parse<T>(), sourceManager,
                          std::move(alloc), std::move(diagnostics));
    }

    const SyntaxNode* rootNode;
    SourceManager& sourceMan;
    BumpAllocator alloc;
    Diagnostics diagnosticsBuffer;

    // This is a shared default source manager for cases where the user doesn't
    // care about managing the lifetime of loaded source. Note that all of
    // the source loaded by this thing will live in memory for the lifetime of
    // the process.
    static SourceManager& getDefaultSourceManager() {
        static SourceManager instance;
        return instance;
    }
};

}
