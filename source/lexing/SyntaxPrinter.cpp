//------------------------------------------------------------------------------
// SyntaxPrinter.cpp
// Support for printing syntax nodes and tokens.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "SyntaxPrinter.h"

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
    if (includeTrivia) {
        for (const auto& t : token.trivia())
            print(t);
    }

    if (includeMissing || !token.isMissing())
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

}