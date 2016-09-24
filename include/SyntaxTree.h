//------------------------------------------------------------------------------
// SyntaxTree.h
// Top-level parser interface.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "BumpAllocator.h"
#include "Diagnostics.h"
#include "StringRef.h"

namespace slang {

class SourceManager;
struct CompilationUnitSyntax;
struct SourceBuffer;

/// The SyntaxTree is the easiest way to interface with the lexer / preprocessor /
/// parser stack. Give it some source text and it produces a parse tree.
///
/// The SyntaxTree object owns all of the memory for the parse tree, so it must
/// live for as long as you need to access that.
class SyntaxTree {
public:
    SyntaxTree(SyntaxTree&& other);
    SyntaxTree& operator=(SyntaxTree&& other);

    // not copyable
    SyntaxTree(const SyntaxTree&) = delete;
    SyntaxTree& operator=(const SyntaxTree&) = delete;

    /// Creates a syntax tree from file on disk or text in memory.
    static SyntaxTree fromFile(SourceManager& sourceManager, StringRef path);
    static SyntaxTree fromText(SourceManager& sourceManager, StringRef text);

	/// Gets the root of the syntax tree.
    const CompilationUnitSyntax* root() const { return rootNode; }

	/// Gets any diagnostics generated while parsing.
    Diagnostics& diagnostics() { return diagnosticsBuffer; }

private:
    SyntaxTree(SourceManager& sourceManager, SourceBuffer source);

    CompilationUnitSyntax* rootNode;
    SourceManager& sourceManager;
    BumpAllocator alloc;
    Diagnostics diagnosticsBuffer;
};

}