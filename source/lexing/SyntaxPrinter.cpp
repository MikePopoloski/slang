//------------------------------------------------------------------------------
// SyntaxPrinter.cpp
// Support for printing syntax nodes and tokens.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "SyntaxPrinter.h"

#include "parsing/SyntaxTree.h"
#include "text/SourceManager.h"

namespace slang {

SyntaxPrinter& SyntaxPrinter::print(Trivia trivia) {
    switch (trivia.kind) {
        case TriviaKind::Directive:
            if (includeDirectives)
                print(*trivia.syntax());
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
        default:
            buffer.append(trivia.getRawText());
            break;
    }
    return *this;
}

SyntaxPrinter& SyntaxPrinter::print(Token token) {
    bool excluded = false;
    if (sourceManager) {
        // If we have a source manager set it means we want to exclude any tokens that
        // came from the preprocessor (macro expansion, include files).
        excluded = sourceManager->isPreprocessedLoc(token.location());
    }

    if (includeTrivia) {
        if (!sourceManager) {
            for (const auto& t : token.trivia())
                print(t);
        }
        else {
            // Exclude any trivia that is from a preprocessed location as well. In order
            // to know that we need to skip over any trivia that is implicitly located
            // relative to something ahead of it (a directive or the token itself).
            SmallVectorSized<const Trivia*, 8> pending;
            for (const auto& trivia : token.trivia()) {
                pending.append(&trivia);
                auto loc = trivia.getExplicitLocation();
                if (loc) {
                    if (!sourceManager->isPreprocessedLoc(*loc)) {
                        for (auto t : pending)
                            print(*t);
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
        buffer.append(token.rawText());

    return *this;
}

SyntaxPrinter& SyntaxPrinter::print(const SyntaxNode& node) {
    uint32_t childCount = node.getChildCount();
    for (uint32_t i = 0; i < childCount; i++) {
        if (auto childNode = node.childNode(i); childNode)
            print(*childNode);
        else if (auto token = node.childToken(i); token)
            print(token);
    }
    return *this;
}

SyntaxPrinter& SyntaxPrinter::print(const SyntaxTree& tree) {
    print(tree.root());
    if (tree.root().kind != SyntaxKind::CompilationUnit && tree.getEOFToken())
        print(tree.getEOFToken());
    return *this;
}

std::string SyntaxPrinter::printFile(const SyntaxTree& tree) {
    return SyntaxPrinter()
        .setIncludeDirectives(true)
        .setIncludeSkipped(true)
        .setIncludeTrivia(true)
        .excludePreprocessed(tree.sourceManager())
        .print(tree)
        .str();
}

}