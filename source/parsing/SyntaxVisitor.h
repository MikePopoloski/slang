//------------------------------------------------------------------------------
// SyntaxVisitor.h
// Syntax tree visitor support.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "AllSyntax.h"

namespace slang {

/// Use this type as a base class for syntax tree visitors. It will default to
/// traversing all children of each node. Add implementations for any specific
/// node types you want to handle.
template<typename TDerived>
class SyntaxVisitor {
public:
    void visitNode(const SyntaxNode* node) {
        dispatchVisitor(*static_cast<TDerived*>(this), node);
    }

    void visitDefault(const SyntaxNode& node) {
        for (uint32_t i = 0; i < node.getChildCount(); i++) {
            auto child = node.childNode(i);
            if (child)
                visitNode(node.childNode(i));
            else {
                auto token = node.childToken(i);
                if (token)
                    static_cast<TDerived*>(this)->visitToken(token);
            }
        }
    }

private:
    // This is to make things compile if the derived class doesn't provide an implementation.
    void visitToken(Token) {}
};

}
