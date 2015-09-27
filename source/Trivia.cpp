#include <cstdint>
#include <string>
#include <algorithm>

#include "Debug.h"
#include "BumpAllocator.h"
#include "StringRef.h"
#include "Trivia.h"

namespace slang {

SyntaxNode* Trivia::syntax() const {
    ASSERT(kind == TriviaKind::Directive);
    return syntaxNode;
}

void Trivia::writeTo(Buffer<char>& buffer) const {
    switch (kind) {
        case TriviaKind::Directive:
        case TriviaKind::SkippedTokens:
            return;

        default:
            buffer.appendRange(rawText);
    }
}

}