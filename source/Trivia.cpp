#include <cstdint>
#include <string>
#include <algorithm>

#include "Debug.h"
#include "BumpAllocator.h"
#include "StringRef.h"
#include "Token.h"
#include "Trivia.h"

namespace slang {

SyntaxNode* Trivia::syntax() const {
    ASSERT(kind == TriviaKind::Directive || kind == TriviaKind::SkippedSyntax);
    return syntaxNode;
}

void Trivia::writeTo(Buffer<char>& buffer, uint8_t flags) const {
    switch (kind) {
        case TriviaKind::Directive:
        case TriviaKind::SkippedSyntax:
            syntaxNode->writeTo(buffer, flags);
            break;

        case TriviaKind::SkippedTokens:
            for (auto& t : tokens)
                t->writeTo(buffer, flags);
            break;

        default:
            buffer.appendRange(rawText);
            break;
    }
}

}