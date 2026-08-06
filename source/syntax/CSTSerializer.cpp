//------------------------------------------------------------------------------
// CSTSerializer.cpp
// Concrete Syntax Tree JSON serialization
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/CSTSerializer.h"

#include <algorithm>
#include <ranges>
#include <string_view>
#include <type_traits>

#include "slang/parsing/Token.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/text/SourceManager.h"
#include "slang/util/Util.h"

namespace slang::syntax {

CSTSerializer::CSTSerializer(JsonWriter& writer, CSTJsonMode mode) : writer(writer), mode(mode) {
}

void CSTSerializer::serialize(const SyntaxTree& tree) {
    writer.startObject();
    writer.writeProperty("kind");
    writer.writeValue("SyntaxTree"sv);
    writer.writeProperty("root");
    serialize(tree.root(), &tree.sourceManager());
    writer.endObject();
}

template<typename T>
struct always_false : std::false_type {};

struct CSTJsonVisitor {
    JsonWriter& writer;
    CSTJsonMode mode;
    const SourceManager* sourceManager;

    CSTJsonVisitor(JsonWriter& w, CSTJsonMode m, const SourceManager* sm) :
        writer(w), mode(m), sourceManager(sm) {}

    template<std::derived_from<SyntaxNode> T>
    void visit(const T& node) {
        if constexpr (requires { handle(node); }) {
            writer.startObject();
            writer.writeProperty("kind");
            writer.writeValue(toString(node.kind));

            handle(node);

            writer.endObject();
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
        if (token.rawText().empty()) {
            if (mode == CSTJsonMode::SimpleTokens || mode == CSTJsonMode::NoTrivia)
                return;
            // The EOF token may have no text, but trivia we want to capture.
            if (token.trivia().empty())
                return;
        }

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
        writer.startArray();
        for (size_t i = 0, count = separatedList.getChildCount(); i < count; i++) {
            auto ele = separatedList.getChild(i);
            if (ele.isToken())
                writeTokenValue(ele.token());
            else if (ele.node())
                ele.node()->visit(*this);
        }
        writer.endArray();
    }

    // Returns true if the given source location comes from a macro expansion or an
    // included file, i.e. text that is serialized in addition to the directive that
    // produced it and so should not be double-counted when reconstructing source.
    bool isExpandedLoc(SourceLocation loc) const {
        return sourceManager && sourceManager->isPreprocessedLoc(loc);
    }

    void writeTrivia(parsing::Trivia trivia, bool expanded) {
        writer.startObject();
        writer.writeProperty("kind");
        writer.writeValue(toString(trivia.kind));

        if (expanded) {
            writer.writeProperty("fromExpansion");
            writer.writeValue(true);
        }

        switch (trivia.kind) {
            case parsing::TriviaKind::Directive:
            case parsing::TriviaKind::SkippedSyntax:
                writer.writeProperty("syntax");
                trivia.syntax()->visit(*this);
                break;
            case parsing::TriviaKind::SkippedTokens:
                writer.writeProperty("tokens");
                writer.startArray();
                for (auto token : trivia.getSkippedTokens())
                    writeTokenValue(token);
                writer.endArray();
                break;
            default:
                writer.writeProperty("text");
                writer.writeValue(trivia.getRawText());
                break;
        }
        writer.endObject();
    }

    bool shouldWriteTrivia(parsing::Trivia trivia) const {
        if (mode != CSTJsonMode::NoWhitespace)
            return true;

        if (trivia.kind == parsing::TriviaKind::Whitespace ||
            trivia.kind == parsing::TriviaKind::EndOfLine) {
            return false;
        }

        return true;
    }

    // Locationless trivia is relative to either the next explicitly located trivia or,
    // if there is no such trivia, the parent token. Resolve those groups before filtering
    // anything so that NoWhitespace mode cannot discard a group's location anchor.
    void writeTriviaList(parsing::TriviaView trivia, bool parentExpanded) {
        size_t groupStart = 0;
        auto writeGroup = [&](size_t groupEnd, bool expanded) {
            for (; groupStart < groupEnd; groupStart++) {
                if (shouldWriteTrivia(trivia[groupStart]))
                    writeTrivia(trivia[groupStart], expanded);
            }
        };

        for (size_t i = 0; i < trivia.size(); i++) {
            if (auto loc = trivia[i].getExplicitLocation())
                writeGroup(i + 1, isExpandedLoc(*loc));
        }
        writeGroup(trivia.size(), parentExpanded);
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

        // Flag tokens that come from a macro expansion or an included file. Such tokens
        // are serialized in addition to the directive that produced them -- the macro
        // usage, or the `include -- which occupies the same textual position, so consumers
        // reconstructing the original source can skip them to avoid double-counting. The
        // trailing trivia without an explicit source anchor inherits the token's state.
        bool expanded = isExpandedLoc(token.location());
        if (expanded) {
            writer.writeProperty("fromExpansion");
            writer.writeValue(true);
        }

        // Handle trivia based on mode
        if (!token.trivia().empty()) {
            switch (mode) {
                case CSTJsonMode::Full:
                    writer.writeProperty("trivia");
                    writer.startArray();
                    writeTriviaList(token.trivia(), expanded);
                    writer.endArray();
                    break;
                case CSTJsonMode::NoWhitespace: {
                    auto trivia = token.trivia();
                    if (std::ranges::any_of(trivia,
                                            [this](auto t) { return shouldWriteTrivia(t); })) {
                        writer.writeProperty("trivia");
                        writer.startArray();
                        writeTriviaList(trivia, expanded);
                        writer.endArray();
                    }
                    break;
                }
                case CSTJsonMode::SimpleTrivia: {
                    writer.writeProperty("trivia");
                    std::string triviaText;
                    for (auto trivia : token.trivia())
                        triviaText += trivia.getRawText();
                    writer.writeValue(triviaText);
                    break;
                }
                case CSTJsonMode::NoTrivia:
                case CSTJsonMode::SimpleTokens:
                    break;
            }
        }

        writer.endObject();
    }

// Generated handle() methods for each syntax kind
#include "slang/syntax/CSTJsonVisitorGen.h"
};

void CSTSerializer::serialize(const SyntaxNode& node, const SourceManager* sourceManager) {
    CSTJsonVisitor visitor(writer, mode, sourceManager);
    node.visit(visitor);
}

} // namespace slang::syntax
