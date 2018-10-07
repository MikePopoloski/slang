//------------------------------------------------------------------------------
// SyntaxVisitor.h
// Syntax tree visitor support.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>
#include <vector>

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"

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
        if constexpr (has_handle_v<TDerived, void, T&>)
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

    void visitInvalid(const SyntaxNode&) {}

private:
    // This is to make things compile if the derived class doesn't provide an implementation.
    void visitToken(Token) {}
};

namespace detail {

struct SyntaxChange {
    const SyntaxNode* first = nullptr;
    SyntaxNode* second = nullptr;

    enum Kind { Remove, Replace, InsertBefore, InsertAfter } kind;

    SyntaxChange(Kind kind, const SyntaxNode* first, SyntaxNode* second) :
        first(first), second(second), kind(kind) {}
};

using ChangeMap = flat_hash_map<const SyntaxNode*, detail::SyntaxChange>;
std::shared_ptr<SyntaxTree> transformTree(
    const std::shared_ptr<SyntaxTree>& tree, const ChangeMap& changes,
    const std::vector<std::shared_ptr<SyntaxTree>>& tempTrees);

} // namespace detail

template<typename TDerived>
class SyntaxRewriter : public SyntaxVisitor<TDerived> {
public:
    std::shared_ptr<SyntaxTree> transform(const std::shared_ptr<SyntaxTree>& tree) {
        sourceManager = &tree->sourceManager();
        changes.clear();
        tempTrees.clear();

        tree->root().visit(*this);

        if (changes.empty())
            return tree;

        return transformTree(tree, changes, tempTrees);
    }

protected:
    SyntaxNode& parse(string_view text) {
        tempTrees.emplace_back(SyntaxTree::fromText(text, *sourceManager));
        return tempTrees.back()->root();
    }

    void remove(const SyntaxNode& oldNode) {
        changes.emplace(&oldNode,
                        detail::SyntaxChange{ detail::SyntaxChange::Remove, &oldNode, nullptr });
    }

    void replace(const SyntaxNode& oldNode, SyntaxNode& newNode) {
        changes.emplace(&oldNode,
                        detail::SyntaxChange{ detail::SyntaxChange::Replace, &oldNode, &newNode });
    }

    void insertBefore(const SyntaxNode& oldNode, SyntaxNode& newNode) {
        changes.emplace(&oldNode, detail::SyntaxChange{ detail::SyntaxChange::InsertBefore,
                                                        &oldNode, &newNode });
    }

    void insertAfter(const SyntaxNode& oldNode, SyntaxNode& newNode) {
        changes.emplace(&oldNode, detail::SyntaxChange{ detail::SyntaxChange::InsertAfter, &oldNode,
                                                        &newNode });
    }

private:
    SourceManager* sourceManager = nullptr;
    detail::ChangeMap changes;
    std::vector<std::shared_ptr<SyntaxTree>> tempTrees;
};

#undef DERIVED

} // namespace slang
