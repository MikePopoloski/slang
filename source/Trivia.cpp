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
    ASSERT(kind == TriviaKind::Directive);
    return syntaxNode;
}

void Trivia::writeTo(Buffer<char>& buffer) const {
    switch (kind) {
        case TriviaKind::Directive:
            syntaxNode->writeTo(buffer, true);
            break;

        case TriviaKind::SkippedTokens:
            for (auto& t : tokens)
                t->writeTo(buffer, true);
            break;

        default:
            buffer.appendRange(rawText);
            break;
    }
}

}