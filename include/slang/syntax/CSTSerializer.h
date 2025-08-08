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

#define MODE(x) x(Full) x(SimpleTrivia) x(NoTrivia) x(SimpleTokens)
SLANG_ENUM(CSTJsonMode, MODE)
#undef MODE

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
