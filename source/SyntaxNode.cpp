#include <cstdint>
#include <memory>
#include <string>
#include <algorithm>

#include "Buffer.h"
#include "StringRef.h"
#include "Token.h"
#include "SyntaxNode.h"

namespace slang {

void SyntaxNode::writeTo(Buffer<char>& buffer, bool includeTrivia, bool includeMissing) {
    for (uint32_t i = 0; i < childCount; i++) {
        auto child = getChild(i);
        if (child.isToken && child.token)
            child.token->writeTo(buffer, includeTrivia, includeMissing);
        else if (child.node)
            child.node->writeTo(buffer, includeTrivia);
    }
}

TokenOrSyntax SyntaxNode::getChild(uint32_t) {
    // if you hit this assert, you forgot to override getChild in your syntax node
    ASSERT(false);
    return nullptr;
}

std::string SyntaxNode::toString() {
    Buffer<char> buffer;
    writeTo(buffer, false);
    return std::string(buffer.begin(), buffer.end());
}

std::string SyntaxNode::toFullString() {
    Buffer<char> buffer;
    writeTo(buffer, true);
    return std::string(buffer.begin(), buffer.end());
}

Token* SyntaxNode::getFirstToken() {
    for (uint32_t i = 0; i < childCount; i++) {
        auto child = getChild(i);
        if (child.isToken && child.token)
            return child.token;
        else if (child.node) {
            auto result = child.node->getFirstToken();
            if (result)
                return result;
        }
    }
    return nullptr;
}

}