//------------------------------------------------------------------------------
// SyntaxPrinter.cpp
// Support for printing syntax nodes and tokens
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/SyntaxPrinter.h"

#include "slang/parsing/ParserMetadata.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"

namespace slang::syntax {

using namespace parsing;

SyntaxPrinter::SyntaxPrinter(const SourceManager& sourceManager) : sourceManager(&sourceManager) {
}

SyntaxPrinter& SyntaxPrinter::print(Trivia trivia) {
    switch (trivia.kind) {
        case TriviaKind::Directive:
            if (includeDirectives)
                print(*trivia.syntax());
            else if (includePreprocessed) {
                auto nestedTrivia = trivia.syntax()->getFirstToken().trivia();
                for (const auto& t : nestedTrivia)
                    print(t);
            }
            break;
        case TriviaKind::SkippedSyntax:
            if (includeSkipped)
                print(*trivia.syntax());
            break;
        case TriviaKind::SkippedTokens:
            if (includeSkipped) {
                for (Token t : trivia.getSkippedTokens())
                    print(t);
            }
            break;
        case TriviaKind::DisabledText:
            if (includeSkipped)
                append(trivia.getRawText());
            break;
        case TriviaKind::LineComment:
        case TriviaKind::BlockComment:
            if (!includeComments)
                break;
            [[fallthrough]];
        default:
            append(trivia.getRawText());
            break;
    }
    return *this;
}

SyntaxPrinter& SyntaxPrinter::print(Token token) {
    bool excluded = false;
    if (!includePreprocessed && sourceManager)
        excluded = sourceManager->isPreprocessedLoc(token.location());

    if (includeTrivia) {
        if (includePreprocessed || !sourceManager) {
            for (const auto& t : token.trivia())
                print(t);
        }
        else {
            // Exclude any trivia that is from a preprocessed location as well. In order
            // to know that we need to skip over any trivia that is implicitly located
            // relative to something ahead of it (a directive or the token itself).
            SmallVector<const Trivia*> pending;
            for (const auto& trivia : token.trivia()) {
                pending.push_back(&trivia);
                auto loc = trivia.getExplicitLocation();
                if (loc) {
                    if (!sourceManager->isPreprocessedLoc(*loc)) {
                        for (auto t : pending)
                            print(*t);
                    }
                    else {
                        // If this is a directive or skipped trivia we may still
                        // need to print part of it even if the leading trivia
                        // is from a preprocessed location that we're skipping.
                        if (trivia.kind == TriviaKind::Directive ||
                            trivia.kind == TriviaKind::SkippedSyntax ||
                            trivia.kind == TriviaKind::SkippedTokens) {
                            print(trivia);
                        }
                    }
                    pending.clear();
                }
            }

            if (!excluded) {
                for (auto t : pending)
                    print(*t);
            }
        }
    }

    if (!excluded && (includeMissing || !token.isMissing()))
        append(token.rawText());

    return *this;
}

SyntaxPrinter& SyntaxPrinter::print(const SyntaxNode& node) {
    size_t childCount = node.getChildCount();
    for (size_t i = 0; i < childCount; i++) {
        if (auto childNode = node.childNode(i); childNode)
            print(*childNode);
        else if (auto token = node.childToken(i); token)
            print(token);
    }
    return *this;
}

SyntaxPrinter& SyntaxPrinter::print(const SyntaxTree& tree) {
    print(tree.root());
    if (tree.root().kind != SyntaxKind::CompilationUnit && tree.getMetadata().eofToken)
        print(tree.getMetadata().eofToken);
    return *this;
}

std::string SyntaxPrinter::printFile(const SyntaxTree& tree) {
    return SyntaxPrinter(tree.sourceManager())
        .setIncludeDirectives(true)
        .setIncludeSkipped(true)
        .setIncludeTrivia(true)
        .setIncludePreprocessed(false)
        .setSquashNewlines(false)
        .print(tree)
        .str();
}

SyntaxPrinter& SyntaxPrinter::append(std::string_view text) {
    if (!squashNewlines) {
        buffer.append(text);
        return *this;
    }

    bool carriage = false;
    bool newline = false;

    if (!text.empty() && (text[0] == '\r' || text[0] == '\n')) {
        size_t i = 0;
        if (text[i] == '\r') {
            carriage = true;
            i++;
        }

        if (i < text.length() && text[i] == '\n') {
            newline = true;
            i++;
        }

        for (; i < text.length(); i++) {
            if (text[i] == '\r' || text[i] == '\n')
                i++;
        }

        text = text.substr(i);
    }

    if (buffer.empty() || buffer.back() != '\n') {
        if (carriage)
            buffer.push_back('\r');
        if (newline)
            buffer.push_back('\n');
    }

    buffer.append(text);
    return *this;
}

} // namespace slang::syntax
