//------------------------------------------------------------------------------
// SyntaxVisitor.h
// Syntax tree visitor support.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "AllSyntax.h"

namespace slang {

#define DERIVED static_cast<TDerived*>(this)

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
            DERIVED->handle(t);
        else
            DERIVED->visitDefault(t);
    }

    void visitDefault(const SyntaxNode& node) {
        for (uint32_t i = 0; i < node.getChildCount(); i++) {
            auto child = node.childNode(i);
            if (child)
                child->visit(*DERIVED);
            else {
                auto token = node.childToken(i);
                if (token)
                    DERIVED->visitToken(token);
            }
        }
    }

private:
    // This is to make things compile if the derived class doesn't provide an implementation.
    void visitToken(Token) {}
};

template<typename TDerived>
class SyntaxRewriter {
    HAS_METHOD_TRAIT(handle);

public:
    explicit SyntaxRewriter(BumpAllocator& alloc) : factory(alloc) {}

    template<typename T>
    void visit(T& t) {
        if constexpr (has_handle_v<TDerived, T*, T>) {
            T* result = DERIVED->handle(t);
            if (result != &t) {

            }
        }
        else {
            DERIVED->visitDefault(t);
        }
    }

    void visitDefault(SyntaxNode& node) {
        for (uint32_t i = 0; i < node.getChildCount(); i++) {
            auto child = node.childNode(i);
            if (child)
                child->visit(*DERIVED);
        }
    }

protected:
    void insertBefore(SyntaxNode& newNode, Token separator = Token());
    void insertAfter(SyntaxNode& newNode, Token separator = Token());

    SyntaxFactory factory;
};

#undef DERIVED

}
