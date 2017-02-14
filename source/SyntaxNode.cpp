//------------------------------------------------------------------------------
// SyntaxNode.cpp
// Base class and utilities for syntax nodes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "SyntaxNode.h"

namespace slang {

void SyntaxNode::writeTo(SmallVector<char>& buffer, uint8_t flags) {
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
    SmallVectorSized<char, 256> buffer;
    writeTo(buffer, flags);
    return std::string(buffer.begin(), buffer.end());
}

std::string SyntaxNode::toString(uint8_t flags) const {
    // TODO: the const cast is ugly
    return const_cast<SyntaxNode*>(this)->toString(flags);
}

Token SyntaxNode::getFirstToken() {
    for (uint32_t i = 0; i < childCount; i++) {
        auto child = getChild(i);
        if (child.isToken) {
            if (child.token)
                return child.token;
        }
        else if (child.node) {
            auto result = child.node->getFirstToken();
            if (result)
                return result;
        }
    }
    return Token();
}

Token SyntaxNode::getFirstToken() const {
    // TODO: the const cast is ugly
    return const_cast<SyntaxNode*>(this)->getFirstToken();
}

Token SyntaxNode::getLastToken() {
    for (int i = childCount - 1; i >= 0; i--) {
        auto child = getChild(i);
        if (child.isToken) {
            if (child.token)
                return child.token;
        }
        else if (child.node) {
            auto result = child.node->getLastToken();
            if (result)
                return result;
        }
    }
    return Token();
}

Token SyntaxNode::getLastToken() const {
    // TODO: the const cast is ugly
    return const_cast<SyntaxNode*>(this)->getLastToken();
}

SourceRange SyntaxNode::sourceRange() const {
    Token firstToken = getFirstToken();
    Token lastToken = getLastToken();
    return SourceRange(firstToken.location(), lastToken.location() + lastToken.rawText().length());
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
