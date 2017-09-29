//------------------------------------------------------------------------------
// SyntaxNode.cpp
// Base class and utilities for syntax nodes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "SyntaxNode.h"

namespace slang {

void SyntaxNode::writeTo(SmallVector<char>& buffer, uint8_t flags) const {
    uint32_t childCount = getChildCount();
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

std::string SyntaxNode::toString(uint8_t flags) const {
    SmallVectorSized<char, 256> buffer;
    writeTo(buffer, flags);
    return std::string(buffer.begin(), buffer.end());
}

Token SyntaxNode::getFirstToken() const {
    uint32_t childCount = getChildCount();
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

Token SyntaxNode::getLastToken() const {
    uint32_t childCount = getChildCount();
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

SourceRange SyntaxNode::sourceRange() const {
    Token firstToken = getFirstToken();
    Token lastToken = getLastToken();
    return SourceRange(firstToken.location(), lastToken.location() + lastToken.rawText().length());
}

const SyntaxNode* SyntaxNode::childNode(uint32_t index) const {
    auto child = const_cast<SyntaxNode*>(this)->getChild(index);
    if (child.isToken)
        return nullptr;
    return child.node;
}

Token SyntaxNode::childToken(uint32_t index) const {
    auto child = const_cast<SyntaxNode*>(this)->getChild(index);
    if (!child.isToken)
        return Token();
    return child.token;
}

}
