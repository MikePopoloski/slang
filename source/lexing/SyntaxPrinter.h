//------------------------------------------------------------------------------
// SyntaxPrinter.h
// Support for printing syntax nodes and tokens.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <string>

#include "parsing/SyntaxNode.h"

namespace slang {

class SyntaxTree;

/// Provides support for printing tokens, trivia, or whole syntax trees
/// back to source code.
class SyntaxPrinter {
public:
    SyntaxPrinter& print(Trivia trivia);
    SyntaxPrinter& print(Token token);
    SyntaxPrinter& print(const SyntaxNode& node);
    SyntaxPrinter& print(const SyntaxTree& tree);

    SyntaxPrinter& setIncludeTrivia(bool include) { includeTrivia = include; return *this; }
    SyntaxPrinter& setIncludeMissing(bool include) { includeMissing = include; return *this; }
    SyntaxPrinter& setIncludeSkipped(bool include) { includeSkipped = include; return *this; }
    SyntaxPrinter& setIncludeDirectives(bool include) { includeDirectives = include; return *this; }

    SyntaxPrinter& excludePreprocessed(const SourceManager& sm) { sourceManager = &sm; return *this; }

    std::string str() const { return buffer; }

private:
    std::string buffer;
    const SourceManager* sourceManager = nullptr;
    bool includeTrivia = true;
    bool includeMissing = false;
    bool includeSkipped = false;
    bool includeDirectives = false;
};

}