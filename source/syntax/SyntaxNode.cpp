//------------------------------------------------------------------------------
// SyntaxNode.cpp
// Base class and utilities for syntax nodes
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/syntax/SyntaxNode.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxPrinter.h"

namespace {

using namespace slang;

struct GetChildVisitor {
    template<typename T>
    ConstTokenOrSyntax visit(const T& node, size_t index) {
        return node.getChild(index);
    }

    ConstTokenOrSyntax visitInvalid(const SyntaxNode&, size_t) { return nullptr; }
};

} // namespace

namespace slang {

ConstTokenOrSyntax::ConstTokenOrSyntax(TokenOrSyntax tos) {
    if (tos.isNode())
        *this = tos.node();
    else
        *this = tos.token();
}

std::string SyntaxNode::toString() const {
    return SyntaxPrinter().print(*this).str();
}

Token SyntaxNode::getFirstToken() const {
    size_t childCount = getChildCount();
    for (size_t i = 0; i < childCount; i++) {
        auto child = getChild(i);
        if (child.isToken()) {
            if (child.token())
                return child.token();
        }
        else if (child.node()) {
            auto result = child.node()->getFirstToken();
            if (result)
                return result;
        }
    }
    return Token();
}

Token SyntaxNode::getLastToken() const {
    size_t childCount = getChildCount();
    for (ptrdiff_t i = ptrdiff_t(childCount) - 1; i >= 0; i--) {
        auto child = getChild(size_t(i));
        if (child.isToken()) {
            if (child.token())
                return child.token();
        }
        else if (child.node()) {
            auto result = child.node()->getLastToken();
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

ConstTokenOrSyntax SyntaxNode::getChild(size_t index) const {
    GetChildVisitor visitor;
    return visit(visitor, index);
}

const SyntaxNode* SyntaxNode::childNode(size_t index) const {
    auto child = getChild(index);
    if (child.isToken())
        return nullptr;
    return child.node();
}

Token SyntaxNode::childToken(size_t index) const {
    auto child = getChild(index);
    if (!child.isToken())
        return Token();
    return child.token();
}

bool SyntaxListBase::isKind(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::SyntaxList:
        case SyntaxKind::TokenList:
        case SyntaxKind::SeparatedList:
            return true;
        default:
            return false;
    }
}

} // namespace slang
