//------------------------------------------------------------------------------
// CSTSerializer.cpp
// Concrete Syntax Tree JSON serialization
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/CSTSerializer.h"

#include <string_view>
#include <type_traits>

#include "slang/parsing/Token.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/util/Util.h"

namespace slang::syntax {

CSTSerializer::CSTSerializer(JsonWriter& writer, CSTJsonMode mode) : writer(writer), mode(mode) {
}

void CSTSerializer::serialize(const SyntaxTree& tree) {
    writer.startObject();
    writer.writeProperty("kind");
    writer.writeValue("SyntaxTree"sv);
    writer.writeProperty("root");
    serialize(tree.root());
    writer.endObject();
}

template<typename T>
struct always_false : std::false_type {};

struct CSTJsonVisitor {
    JsonWriter& writer;
    CSTJsonMode mode;

    CSTJsonVisitor(JsonWriter& w, CSTJsonMode m) : writer(w), mode(m) {}

    template<std::derived_from<SyntaxNode> T>
    void visit(const T& node) {
        if constexpr (requires { handle(node); }) {
            writer.startObject();
            writer.writeProperty("kind");
            writer.writeValue(toString(node.kind));

            handle(node);

            writer.endObject();
        }
        else if constexpr (std::is_same_v<T, SyntaxListBase>) {
            // The child class's handlers should be called
            SLANG_UNREACHABLE;
        }
        else {
            static_assert(always_false<T>::value, "Unhandled syntax node type in CSTJsonVisitor");
        }
    }

    void handle(const detail::InvalidSyntaxNode& node) {
        writer.writeProperty("children");
        writeChildren(node);
    }

    void writeToken(std::string_view name, parsing::Token token) {
        if (token.valueText().empty())
            return;

        writer.writeProperty(name);
        writeTokenValue(token);
    }

    void writeNode(std::string_view name, not_null<const SyntaxNode*> node) {
        writer.writeProperty(name);
        node->visit(*this);
    }

    void writeOptionalNode(std::string_view name, const SyntaxNode* node) {
        if (node) {
            writer.writeProperty(name);
            node->visit(*this);
        }
    }

    void writeTokenList(std::string_view name, const TokenList& tokenList) {
        if (tokenList.empty())
            return;

        writer.writeProperty(name);
        writer.startArray();
        for (auto token : tokenList)
            writeTokenValue(token);
        writer.endArray();
    }

    template<typename T>
    void writeSyntaxList(std::string_view name, const SyntaxList<T>& syntaxList) {
        if (syntaxList.empty())
            return;

        writer.writeProperty(name);
        writer.startArray();
        for (auto item : syntaxList)
            item->visit(*this);
        writer.endArray();
    }

    void writeChildren(const SyntaxNode& node) {
        writer.startArray();
        for (size_t i = 0; i < node.getChildCount(); i++) {
            auto child = node.childNode(i);
            if (child) {
                child->visit(*this);
            }
            else {
                auto token = node.childToken(i);
                if (token)
                    writeTokenValue(token);
            }
        }
        writer.endArray();
    }

    template<typename T>
    void writeSeparatedSyntaxList(std::string_view name,
                                  const SeparatedSyntaxList<T>& separatedList) {
        if (separatedList.empty())
            return;

        writer.writeProperty(name);
        writeChildren(separatedList);
    }

    void writeTrivia(parsing::Trivia trivia) {
        writer.startObject();
        writer.writeProperty("kind");
        writer.writeValue(toString(trivia.kind));
        switch (trivia.kind) {
            case parsing::TriviaKind::Directive:
            case parsing::TriviaKind::SkippedSyntax: {
                writer.writeProperty("syntax");
                trivia.syntax()->visit(*this);
            } break;
            case parsing::TriviaKind::SkippedTokens: {
                writer.writeProperty("tokens");
                writer.startArray();
                for (auto token : trivia.getSkippedTokens())
                    writeTokenValue(token);
                writer.endArray();
            } break;
            default: {
                writer.writeProperty("text");
                writer.writeValue(trivia.getRawText());
            } break;
        }
        writer.endObject();
    }

    void writeTokenValue(parsing::Token token) {
        // If simple-tokens mode, just write the text value
        if (mode == CSTJsonMode::SimpleTokens) {
            writer.writeValue(token.rawText());
            return;
        }

        writer.startObject();
        writer.writeProperty("kind");
        writer.writeValue(toString(token.kind));
        writer.writeProperty("text");
        writer.writeValue(token.rawText());

        // Handle trivia based on mode
        if (mode != CSTJsonMode::NoTrivia && !token.trivia().empty()) {
            writer.writeProperty("trivia");
            if (mode == CSTJsonMode::SimpleTrivia) {
                // Just write the concatenated trivia text
                std::string triviaText;
                for (auto trivia : token.trivia())
                    triviaText += trivia.getRawText();

                writer.writeValue(triviaText);
            }
            else {
                // Write trivia kind and value
                writer.startArray();
                for (auto trivia : token.trivia()) {
                    writeTrivia(trivia);
                }
                writer.endArray();
            }
        }

        writer.endObject();
    }

// Generated handle() methods for each syntax kind
#include "slang/syntax/CSTJsonVisitorGen.h"
};

void CSTSerializer::serialize(const SyntaxNode& node) {
    CSTJsonVisitor visitor(writer, mode);
    node.visit(visitor);
}

} // namespace slang::syntax
