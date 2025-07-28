//------------------------------------------------------------------------------
// CSTSerializer.cpp
// Concrete Syntax Tree JSON serialization
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/CSTSerializer.h"

#include "slang/parsing/Token.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"

// This file contains CST JSON conversion functionality.

namespace slang::syntax {

// Define traits and utility functions for CSTJsonMode
const std::array<CSTJsonMode, 4> CSTJsonMode_traits::values = {
    CSTJsonMode::Full, CSTJsonMode::SimpleTrivia, CSTJsonMode::NoTrivia, CSTJsonMode::SimpleTokens};

std::ostream& operator<<(std::ostream& os, CSTJsonMode mode) {
    return os << toString(mode);
}

std::string_view toString(CSTJsonMode mode) {
    switch (mode) {
        case CSTJsonMode::Full:
            return "Full";
        case CSTJsonMode::SimpleTrivia:
            return "SimpleTrivia";
        case CSTJsonMode::NoTrivia:
            return "NoTrivia";
        case CSTJsonMode::SimpleTokens:
            return "SimpleTokens";
        default:
            return "Unknown";
    }
}

CSTSerializer::CSTSerializer(JsonWriter& writer, CSTJsonMode mode) : writer(writer), mode(mode) {
}

void CSTSerializer::serialize(const SyntaxTree& tree) {
    writer.startObject();
    writer.writeProperty("kind");
    writer.writeValue(std::string_view("SyntaxTree"));
    writer.writeProperty("root");
    serialize(tree.root());
    writer.endObject();
}

struct CSTJsonVisitor : public SyntaxVisitor<CSTJsonVisitor> {
    JsonWriter& writer;
    CSTJsonMode mode;

    CSTJsonVisitor(JsonWriter& w, CSTJsonMode m) : writer(w), mode(m) {}

    // Helper methods for common patterns
    void startSyntaxObject(const SyntaxNode& node) {
        writer.startObject();
        writer.writeProperty("kind");
        writer.writeValue(std::string_view(toString(node.kind)));
    }

    void writePropertyAndToken(std::string_view name, parsing::Token token) {
        writer.writeProperty(name);
        visitToken(token);
    }

    void writePropertyAndNode(std::string_view name, const SyntaxNode* node) {
        writer.writeProperty(name);
        node->visit(*this);
    }

    void writeOptionalNode(std::string_view name, const SyntaxNode* node) {
        if (node) {
            writer.writeProperty(name);
            node->visit(*this);
        }
    }

    void writeOptionalToken(std::string_view name, parsing::Token token) {
        if (token) {
            writer.writeProperty(name);
            visitToken(token);
        }
    }

    void writeTokenList(std::string_view name, const TokenList& tokenList) {
        writer.writeProperty(name);
        if (tokenList.empty()) {
            writer.writeEmptyArray();
        }
        else {
            writer.startArray();
            for (auto token : tokenList) {
                visitToken(token);
            }
            writer.endArray();
        }
    }

    template<typename T>
    void writeSyntaxList(std::string_view name, const SyntaxList<T>& syntaxList) {
        writer.writeProperty(name);
        if (syntaxList.empty()) {
            writer.writeEmptyArray();
        }
        else {
            writer.startArray();
            for (auto item : syntaxList) {
                item->visit(*this);
            }
            writer.endArray();
        }
    }

    template<typename T>
    void writeSeparatedSyntaxList(std::string_view name,
                                  const SeparatedSyntaxList<T>& separatedList) {
        writer.writeProperty(name);
        if (separatedList.empty()) {
            writer.writeEmptyArray();
        }
        else {
            writer.startArray();
            // SeparatedSyntaxList stores elements and separators alternately
            for (size_t i = 0; i < separatedList.getChildCount(); i++) {
                auto child = separatedList.childNode(i);
                if (child) {
                    child->visit(*this);
                }
                else {
                    auto token = separatedList.childToken(i);
                    if (token) {
                        visitToken(token);
                    }
                }
            }
            writer.endArray();
        }
    }

    void visitToken(parsing::Token token) {
        // If token text is empty, write null instead of an object
        if (token.rawText().empty()) {
            writer.writeNull();
            return;
        }

        // If simple-tokens mode, just write the text value
        if (mode == CSTJsonMode::SimpleTokens) {
            writer.writeValue(std::string_view(token.rawText()));
            return;
        }

        writer.startObject();
        writer.writeProperty("kind");
        writer.writeValue(std::string_view(toString(token.kind)));
        writer.writeProperty("text");
        writer.writeValue(std::string_view(token.rawText()));

        // Handle trivia based on mode
        if (mode != CSTJsonMode::NoTrivia && !token.trivia().empty()) {
            writer.writeProperty("trivia");
            if (mode == CSTJsonMode::SimpleTrivia) {
                // Just write the concatenated trivia text
                std::string triviaText;
                for (auto trivia : token.trivia()) {
                    triviaText += trivia.getRawText();
                }
                writer.writeValue(std::string_view(triviaText));
            }
            else {
                // Write trivia kind and value
                writer.startArray();
                for (auto trivia : token.trivia()) {
                    writer.startObject();
                    writer.writeProperty("kind");
                    writer.writeValue(std::string_view(toString(trivia.kind)));
                    writer.writeProperty("text");
                    writer.writeValue(std::string_view(trivia.getRawText()));
                    writer.endObject();
                }
                writer.endArray();
            }
        }

        writer.endObject();
    }

// Generated handle() methods for each syntax type
#include "slang/syntax/CSTJsonVisitorGen.h"
};

void CSTSerializer::serialize(const SyntaxNode& node) {
    CSTJsonVisitor visitor(writer, mode);
    node.visit(visitor);
}

} // namespace slang::syntax
