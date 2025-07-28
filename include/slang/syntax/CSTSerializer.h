
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

/// Converts concrete syntax trees to JSON format for debugging and analysis
class SLANG_EXPORT CSTSerializer {
public:
    explicit CSTSerializer(JsonWriter& writer);

    /// Serialize a syntax tree to JSON
    void serialize(const SyntaxTree& tree);

    /// Serialize a syntax node to JSON
    void serialize(const SyntaxNode& node);

private:
    void visitToken(parsing::Token token);
    void writeTokenTrivia(parsing::Token token);

    JsonWriter& writer;
};
} // namespace slang::syntax
