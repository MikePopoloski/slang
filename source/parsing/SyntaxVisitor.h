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
    HAS_METHOD_TRAIT(handle);

public:
    template<typename T>
    void visit(const T& t) {
        if constexpr (has_handle_v<TDerived, void, T>)
            static_cast<TDerived*>(this)->handle(t);
        else
            visitDefault(t);
    }

    void visitDefault(const SyntaxNode& node) {
        for (uint32_t i = 0; i < node.getChildCount(); i++) {
            auto child = node.childNode(i);
            if (child)
                child->visit(*static_cast<TDerived*>(this));
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
