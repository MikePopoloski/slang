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

CSTSerializer::CSTSerializer(JsonWriter& writer) : writer(writer) {
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

    CSTJsonVisitor(JsonWriter& w) : writer(w) {}

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

        writer.startObject();
        writer.writeProperty("kind");
        writer.writeValue(std::string_view(toString(token.kind)));
        writer.writeProperty("text");
        writer.writeValue(std::string_view(token.rawText()));

        // Only include trivia if there are any
        if (!token.trivia().empty()) {
            writer.writeProperty("trivia");
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

        writer.endObject();
    }

// Generated handle() methods for each syntax type
#include "slang/syntax/CSTJsonVisitorGen.h"
};

void CSTSerializer::serialize(const SyntaxNode& node) {
    CSTJsonVisitor visitor(writer);
    node.visit(visitor);
}

} // namespace slang::syntax
