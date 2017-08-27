//------------------------------------------------------------------------------
// Trivia.cpp
// Support for tracking trivia like whitespace and comments.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "Trivia.h"

#include "parsing/SyntaxNode.h"
#include "Token.h"

namespace slang {

SyntaxNode* Trivia::syntax() const {
    ASSERT(kind == TriviaKind::Directive || kind == TriviaKind::SkippedSyntax);
    return syntaxNode;
}

void Trivia::writeTo(SmallVector<char>& buffer, uint8_t flags) const {
    switch (kind) {
        case TriviaKind::Directive:
            if (flags & SyntaxToStringFlags::IncludeDirectives)
                syntaxNode->writeTo(buffer, flags);
            break;
        case TriviaKind::SkippedSyntax:
            if (flags & SyntaxToStringFlags::IncludeSkipped)
                syntaxNode->writeTo(buffer, flags);
            break;
        case TriviaKind::SkippedTokens:
            if (flags & SyntaxToStringFlags::IncludeSkipped) {
                for (Token t : tokens)
                    t.writeTo(buffer, flags);
            }
            break;
        default:
            buffer.appendRange(rawText);
            break;
    }
}

}