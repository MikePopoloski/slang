#pragma once

#include "BumpAllocator.h"
#include "Diagnostics.h"
#include "StringRef.h"

namespace slang {

class SourceManager;
struct CompilationUnitSyntax;
struct SourceBuffer;

class SyntaxTree {
public:
    SyntaxTree(SyntaxTree&& other);
    SyntaxTree& operator=(SyntaxTree&& other);

    // not copyable
    SyntaxTree(const SyntaxTree&) = delete;
    SyntaxTree& operator=(const SyntaxTree&) = delete;

    // create from file on disk or text in memory
    static SyntaxTree fromFile(SourceManager& sourceManager, StringRef path);
    static SyntaxTree fromText(SourceManager& sourceManager, StringRef text);

    const CompilationUnitSyntax* root() const { return rootNode; }
    Diagnostics& diagnostics() { return diagnosticsBuffer; }

private:
    SyntaxTree(SourceManager& sourceManager, SourceBuffer source);

    CompilationUnitSyntax* rootNode;
    SourceManager& sourceManager;
    BumpAllocator alloc;
    Diagnostics diagnosticsBuffer;
};

}