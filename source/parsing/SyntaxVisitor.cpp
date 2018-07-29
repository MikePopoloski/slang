//------------------------------------------------------------------------------
// SyntaxVisitor.cpp
// Syntax tree visitor support.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "SyntaxVisitor.h"

namespace {

using namespace slang;

struct CloneVisitor {
    BumpAllocator& alloc;

    CloneVisitor(BumpAllocator& alloc) : alloc(alloc) {}

    template<typename T>
    SyntaxNode* visit(const T& node) {
        T* cloned = node.clone(alloc);
        for (uint32_t i = 0; i < node.getChildCount(); i++) {
            auto child = node.childNode(i);
            if (child)
                cloned->setChild(i, child->visit(*this));
        }

        return cloned;
    }

    SyntaxNode* visitInvalid(const SyntaxNode&) { THROW_UNREACHABLE; }
};

}

namespace slang {

namespace detail {

std::shared_ptr<SyntaxTree> transformTree(const std::shared_ptr<SyntaxTree>& tree,
                                          span<const SyntaxChange>) {
    BumpAllocator alloc;
    CloneVisitor visitor(alloc);

    SyntaxNode* root = tree->root().visit(visitor);
    return std::make_shared<SyntaxTree>(root, tree->sourceManager(), std::move(alloc), tree);
}

}

}
