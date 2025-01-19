//------------------------------------------------------------------------------
// SyntaxNode.cpp
// Base class and utilities for syntax nodes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/SyntaxNode.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxPrinter.h"

namespace {

using namespace slang;
using namespace slang::syntax;

struct PtrGetChildVisitor {
    template<typename T>
    PtrTokenOrSyntax visit(T& node, size_t index) {
        return node.getChildPtr(index);
    }
};

struct ConstGetChildVisitor {
    template<typename T>
    ConstTokenOrSyntax visit(const T& node, size_t index) {
        return node.getChild(index);
    }
};

struct GetChildVisitor {
    template<typename T>
    TokenOrSyntax visit(T& node, size_t index) {
        return node.getChild(index);
    }
};

} // namespace

namespace slang::syntax {

SourceRange PtrTokenOrSyntax::range() const {
    if (isNode())
        return node()->sourceRange();
    else {
        if (token() == nullptr)
            return SourceRange::NoLocation;
        else
            return token()->range();
    }
}

SourceRange ConstTokenOrSyntax::range() const {
    return isNode() ? node()->sourceRange() : token().range();
}

std::string SyntaxNode::toString() const {
    return SyntaxPrinter().print(*this).str();
}

parsing::Token SyntaxNode::getFirstToken() const {
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

parsing::Token SyntaxNode::getLastToken() const {
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

parsing::Token* SyntaxNode::getFirstTokenPtr() {
    size_t childCount = getChildCount();
    for (size_t i = 0; i < childCount; i++) {
        auto child = getChildPtr(i);
        if (child.isToken()) {
            if (child.token())
                return child.token();
        }
        else if (child.node()) {
            auto result = child.node()->getFirstTokenPtr();
            if (result)
                return result;
        }
    }
    return nullptr;
}

parsing::Token* SyntaxNode::getLastTokenPtr() {
    size_t childCount = getChildCount();
    for (ptrdiff_t i = ptrdiff_t(childCount) - 1; i >= 0; i--) {
        auto child = getChildPtr(size_t(i));
        if (child.isToken()) {
            if (child.token())
                return child.token();
        }
        else if (child.node()) {
            auto result = child.node()->getLastTokenPtr();
            if (result)
                return result;
        }
    }
    return nullptr;
}

SourceRange SyntaxNode::sourceRange() const {
    Token firstToken = getFirstToken();
    Token lastToken = getLastToken();
    return SourceRange(firstToken.location(), lastToken.location() + lastToken.rawText().length());
}

ConstTokenOrSyntax SyntaxNode::getChild(size_t index) const {
    ConstGetChildVisitor visitor;
    return visit(visitor, index);
}

PtrTokenOrSyntax SyntaxNode::getChildPtr(size_t index) {
    PtrGetChildVisitor visitor;
    return visit(visitor, index);
}

TokenOrSyntax SyntaxNode::getChild(size_t index) {
    GetChildVisitor visitor;
    return visit(visitor, index);
}

const SyntaxNode* SyntaxNode::childNode(size_t index) const {
    auto child = getChild(index);
    if (child.isToken())
        return nullptr;
    return child.node();
}

SyntaxNode* SyntaxNode::childNode(size_t index) {
    auto child = getChild(index);
    if (child.isToken())
        return nullptr;
    return child.node();
}

parsing::Token SyntaxNode::childToken(size_t index) const {
    auto child = getChild(index);
    if (!child.isToken())
        return Token();
    return child.token();
}

parsing::Token* SyntaxNode::childTokenPtr(size_t index) {
    auto child = getChildPtr(index);
    if (!child.isToken())
        return nullptr;
    return child.token();
}

bool SyntaxNode::isEquivalentTo(const SyntaxNode& other) const {
    size_t childCount = getChildCount();
    if (kind != other.kind || childCount != other.getChildCount())
        return false;

    for (size_t i = 0; i < childCount; i++) {
        auto ln = childNode(i);
        auto rn = other.childNode(i);
        if (bool(ln) != bool(rn))
            return false;

        if (ln) {
            if (!ln->isEquivalentTo(*rn))
                return false;
        }
        else {
            Token lt = childToken(i);
            Token rt = other.childToken(i);
            if (bool(lt) != bool(rt))
                return false;

            if (lt) {
                if (lt.kind != rt.kind || lt.valueText() != rt.valueText())
                    return false;
            }
        }
    }
    return true;
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

bool SyntaxListBase::isChildOptional(size_t index) {
    (void)index;
    return true;
}

} // namespace slang::syntax
