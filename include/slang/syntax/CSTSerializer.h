
//------------------------------------------------------------------------------
//! @file CSTSerializer.h
//! @brief Concrete Syntax Tree JSON serialization
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/syntax/SyntaxNode.h"
#include "slang/text/Json.h"

namespace slang::syntax {

class SyntaxTree;

/// CST JSON output formatting modes
enum class SLANG_EXPORT CSTJsonMode {
    Full,         ///< Full token objects with trivia kind and array
    SimpleTrivia, ///< Full token objects with trivia as a concatenated string
    NoTrivia,     ///< Full token objects with no trivia
    SimpleTokens  ///< Tokens as strings, no trivia
};

SLANG_EXPORT std::ostream& operator<<(std::ostream& os, CSTJsonMode mode);
SLANG_EXPORT std::string_view toString(CSTJsonMode mode);

class SLANG_EXPORT CSTJsonMode_traits {
public:
    static const std::array<CSTJsonMode, 4> values;
};

/// Converts concrete syntax trees to JSON format for debugging and analysis
class SLANG_EXPORT CSTSerializer {
public:
    explicit CSTSerializer(JsonWriter& writer, CSTJsonMode mode = CSTJsonMode::Full);

    /// Serialize a syntax tree to JSON
    void serialize(const SyntaxTree& tree);

    /// Serialize a syntax node to JSON
    void serialize(const SyntaxNode& node);

private:
    void visitToken(parsing::Token token);
    void writeTokenTrivia(parsing::Token token);

    JsonWriter& writer;
    CSTJsonMode mode;
};
} // namespace slang::syntax
