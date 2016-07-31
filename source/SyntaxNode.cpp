#include "SyntaxNode.h"

namespace slang {

void SyntaxNode::writeTo(Buffer<char>& buffer, uint8_t flags) {
    for (uint32_t i = 0; i < childCount; i++) {
        auto child = getChild(i);
        if (child.isToken) {
            if (child.token)
                child.token.writeTo(buffer, flags);
        }
        else if (child.node) {
            child.node->writeTo(buffer, flags);
        }
    }
}

std::string SyntaxNode::toString(uint8_t flags) {
    Buffer<char> buffer;
    writeTo(buffer, flags);
    return std::string(buffer.begin(), buffer.end());
}

Token SyntaxNode::getFirstToken() {
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
    return Token();
}

bool SyntaxNode::replaceFirstToken(Token token) {
    for (uint32_t i = 0; i < childCount; i++) {
        auto child = getChild(i);
        if (child.isToken) {
            replaceChild(i, token);
            return true;
        }
        else if (child.node) {
            if (child.node->replaceFirstToken(token))
                return true;
        }
    }
    return false;
}

}