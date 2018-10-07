//------------------------------------------------------------------------------
// SyntaxPrinter.h
// Support for printing syntax nodes and tokens.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <string>

#include "slang/syntax/SyntaxNode.h"

namespace slang {

class SyntaxTree;

/// Provides support for printing tokens, trivia, or whole syntax trees
/// back to source code.
class SyntaxPrinter {
public:
    SyntaxPrinter() = default;
    explicit SyntaxPrinter(const SourceManager& sourceManager);

    SyntaxPrinter& print(Trivia trivia);
    SyntaxPrinter& print(Token token);
    SyntaxPrinter& print(const SyntaxNode& node);
    SyntaxPrinter& print(const SyntaxTree& tree);

    SyntaxPrinter& setIncludeTrivia(bool include) {
        includeTrivia = include;
        return *this;
    }
    SyntaxPrinter& setIncludeMissing(bool include) {
        includeMissing = include;
        return *this;
    }
    SyntaxPrinter& setIncludeSkipped(bool include) {
        includeSkipped = include;
        return *this;
    }
    SyntaxPrinter& setIncludeDirectives(bool include) {
        includeDirectives = include;
        return *this;
    }
    SyntaxPrinter& setIncludePreprocessed(bool include) {
        includePreprocessed = include;
        return *this;
    }
    SyntaxPrinter& setIncludeComments(bool include) {
        includeComments = include;
        return *this;
    }
    SyntaxPrinter& setSquashNewlines(bool include) {
        squashNewlines = include;
        return *this;
    }

    std::string str() const { return buffer; }

    static std::string printFile(const SyntaxTree& tree);

private:
    void append(string_view text);

    std::string buffer;
    const SourceManager* sourceManager = nullptr;
    bool includeTrivia = true;
    bool includeMissing = false;
    bool includeSkipped = false;
    bool includeDirectives = false;
    bool includePreprocessed = true;
    bool includeComments = true;
    bool squashNewlines = true;
};

} // namespace slang
