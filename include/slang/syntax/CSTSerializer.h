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

namespace slang {
class SourceManager;
}

namespace slang::syntax {

class SyntaxTree;

#define MODE(x) x(Full) x(NoWhitespace) x(SimpleTrivia) x(NoTrivia) x(SimpleTokens)
SLANG_ENUM(CSTJsonMode, MODE)
#undef MODE

/// Converts concrete syntax trees to JSON format for debugging and analysis
class SLANG_EXPORT CSTSerializer {
public:
    explicit CSTSerializer(JsonWriter& writer, CSTJsonMode mode = CSTJsonMode::Full);

    /// Serialize a syntax tree to JSON
    void serialize(const SyntaxTree& tree);

    /// Serialize a syntax node to JSON. If provided, the source manager is used to annotate
    /// tokens that originate from macro expansions or included files with a
    /// `"fromExpansion": true` property. Such tokens are serialized in addition to the
    /// directive that produced them, so the annotation lets consumers avoid double-counting
    /// the text.
    void serialize(const SyntaxNode& node, const SourceManager* sourceManager = nullptr);

private:
    JsonWriter& writer;
    CSTJsonMode mode;
};

} // namespace slang::syntax
