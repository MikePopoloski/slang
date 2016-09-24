//------------------------------------------------------------------------------
// SyntaxTree.cpp
// Top-level parser interface.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "SyntaxTree.h"

#include "Parser.h"
#include "Preprocessor.h"
#include "SourceManager.h"

namespace slang {

SyntaxTree::SyntaxTree(SourceManager& sourceManager, SourceBuffer source) :
    sourceManager(sourceManager)
{
    Preprocessor preprocessor(sourceManager, alloc, diagnosticsBuffer);
    preprocessor.pushSource(source);

    Parser parser(preprocessor);
    rootNode = parser.parseCompilationUnit();
}

SyntaxTree SyntaxTree::fromFile(SourceManager& sourceManager, StringRef path) {
    return SyntaxTree(sourceManager, sourceManager.readSource(path));
}

SyntaxTree SyntaxTree::fromText(SourceManager& sourceManager, StringRef text) {
    return SyntaxTree(sourceManager, sourceManager.assignText(text));
}

}