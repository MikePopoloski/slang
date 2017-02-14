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
        for (uint32_t i = 0; i < node.getChildCount(); i++)
            visitNode(node.childNode(i));
    }
};

}
