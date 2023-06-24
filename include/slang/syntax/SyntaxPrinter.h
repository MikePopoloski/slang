//------------------------------------------------------------------------------
//! @file SyntaxPrinter.h
//! @brief Support for printing syntax nodes and tokens
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <string>

#include "slang/parsing/Token.h"

namespace slang {
class SourceManager;
}

namespace slang::syntax {

class SyntaxNode;
class SyntaxTree;

/// Provides support for printing tokens, trivia, or whole syntax trees
/// back to source code.
class SLANG_EXPORT SyntaxPrinter {
public:
    SyntaxPrinter() = default;
    explicit SyntaxPrinter(const SourceManager& sourceManager);

    /// Append raw text to the buffer.
    /// @return a reference to this object, to allow chaining additional method calls.
    SyntaxPrinter& append(std::string_view text);

    /// Print the provided @a trivia to the internal buffer.
    /// @return a reference to this object, to allow chaining additional method calls.
    SyntaxPrinter& print(parsing::Trivia trivia);

    /// Print the provided @a token to the internal buffer.
    /// @return a reference to this object, to allow chaining additional method calls.
    SyntaxPrinter& print(parsing::Token token);

    /// Print the provided @a node to the internal buffer.
    /// @return a reference to this object, to allow chaining additional method calls.
    SyntaxPrinter& print(const SyntaxNode& node);

    /// Print the provided @a tree to the internal buffer.
    /// @return a reference to this object, to allow chaining additional method calls.
    SyntaxPrinter& print(const SyntaxTree& tree);

    /// Sets whether to include trivia when printing syntax.
    /// @return a reference to this object, to allow chaining additional method calls.
    SyntaxPrinter& setIncludeTrivia(bool include) {
        includeTrivia = include;
        return *this;
    }

    /// Sets whether to include missing (automatically inserted) nodes when printing syntax.
    /// @return a reference to this object, to allow chaining additional method calls.
    SyntaxPrinter& setIncludeMissing(bool include) {
        includeMissing = include;
        return *this;
    }

    /// Sets whether to include skipped (due to some sort of error) nodes when printing syntax.
    /// @return a reference to this object, to allow chaining additional method calls.
    SyntaxPrinter& setIncludeSkipped(bool include) {
        includeSkipped = include;
        return *this;
    }

    /// Sets whether to include preprocessor directives when printing syntax.
    /// @return a reference to this object, to allow chaining additional method calls.
    SyntaxPrinter& setIncludeDirectives(bool include) {
        includeDirectives = include;
        return *this;
    }

    /// Sets whether to include preprocessor-expanded tokens when printing syntax.
    /// @return a reference to this object, to allow chaining additional method calls.
    SyntaxPrinter& setIncludePreprocessed(bool include) {
        includePreprocessed = include;
        return *this;
    }

    /// Sets whether to include comments when printing syntax.
    /// @return a reference to this object, to allow chaining additional method calls.
    SyntaxPrinter& setIncludeComments(bool include) {
        includeComments = include;
        return *this;
    }

    /// Sets whether to squash adjacent newlines down into one when printing syntax.
    /// @return a reference to this object, to allow chaining additional method calls.
    SyntaxPrinter& setSquashNewlines(bool include) {
        squashNewlines = include;
        return *this;
    }

    /// @return a copy of the internal text buffer.
    std::string str() const { return buffer; }

    /// A helper method that assists in printing an entire syntax tree back to source
    /// text. A SyntaxPrinter with useful defaults is constructed, the tree is printed,
    /// and the resulting text is returned.
    static std::string printFile(const SyntaxTree& tree);

private:
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

} // namespace slang::syntax
