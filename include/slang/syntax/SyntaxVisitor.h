//------------------------------------------------------------------------------
//! @file SyntaxVisitor.h
//! @brief Syntax tree visitor support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <vector>

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/util/Hash.h"
#include "slang/util/TypeTraits.h"

namespace slang {

#define DERIVED static_cast<TDerived*>(this)

/// Use this type as a base class for syntax tree visitors. It will default to
/// traversing all children of each node. Add implementations for any specific
/// node types you want to handle.
template<typename TDerived>
class SyntaxVisitor {
    template<typename T, typename Arg>
    using handle_t = decltype(std::declval<T>().handle(std::declval<Arg>()));

public:
    /// Visit the provided node, of static type T.
    template<typename T>
    void visit(const T& t) {
        if constexpr (is_detected_v<handle_t, TDerived, T>)
            DERIVED->handle(t);
        else
            DERIVED->visitDefault(t);
    }

    /// The default handler invoked when no visit() method is overridden for a particular type.
    /// Will visit all child nodes by default.
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

    /// The default handler invoked when visiting an invalid node.
    void visitInvalid(const SyntaxNode&) {}

private:
    // This is to make things compile if the derived class doesn't provide an implementation.
    void visitToken(Token) {}
};

namespace detail {

struct SyntaxChange {
    const SyntaxNode* first = nullptr;
    SyntaxNode* second = nullptr;
    Token separator = {};
};

struct RemoveChange : SyntaxChange {};
struct ReplaceChange : SyntaxChange {};

using InsertChangeMap = flat_hash_map<const SyntaxNode*, std::vector<SyntaxChange>>;
using ModifyChangeMap = flat_hash_map<const SyntaxNode*, std::variant<RemoveChange, ReplaceChange>>;
using ListChangeMap = flat_hash_map<const SyntaxNode*, std::vector<SyntaxChange>>;

struct ChangeCollection {
    InsertChangeMap insertBefore;
    InsertChangeMap insertAfter;
    ModifyChangeMap removeOrReplace;
    ListChangeMap listInsertAtFront;
    ListChangeMap listInsertAtBack;

    void clear() {
        insertBefore.clear();
        insertAfter.clear();
        removeOrReplace.clear();
        listInsertAtFront.clear();
        listInsertAtBack.clear();
    }

    bool empty() const {
        return insertBefore.empty() && insertAfter.empty() && removeOrReplace.empty() &&
               listInsertAtFront.empty() && listInsertAtBack.empty();
    }
};

std::shared_ptr<SyntaxTree> transformTree(
    BumpAllocator&& alloc, const std::shared_ptr<SyntaxTree>& tree, const ChangeCollection& commits,
    const std::vector<std::shared_ptr<SyntaxTree>>& tempTrees);

} // namespace detail

/// A helper class that assists in rewriting syntax trees
/// -- useful for automated refactoring tools.
template<typename TDerived>
class SyntaxRewriter : public SyntaxVisitor<TDerived> {
public:
    SyntaxRewriter() : factory(alloc) {}

    /// Transforms the given syntax tree using the rewriter.
    /// The tree will be visited in order and each node will be given a chance to be
    /// rewritten (by providing visit() implementations in the derived class).
    ///
    /// @return if no changes are requested, returns the original syntax tree.
    /// Otherwise, the changes are applied and the newly rewritten syntax tree is returned.
    std::shared_ptr<SyntaxTree> transform(const std::shared_ptr<SyntaxTree>& tree) {
        sourceManager = &tree->sourceManager();
        commits.clear();
        tempTrees.clear();

        tree->root().visit(*this);

        if (commits.empty())
            return tree;

        return transformTree(std::move(alloc), tree, commits, tempTrees);
    }

protected:
    /// A helper for derived classes that parses some text into syntax nodes.
    SyntaxNode& parse(string_view text) {
        tempTrees.emplace_back(SyntaxTree::fromText(text, *sourceManager));
        return tempTrees.back()->root();
    }

    /// Register a removal for the given syntax node from the tree.
    void remove(const SyntaxNode& oldNode) {
        if (auto [_, ok] = commits.removeOrReplace.emplace(&oldNode,
                                                           detail::RemoveChange{&oldNode, nullptr});
            !ok) {
            throw std::logic_error("Node only permit one remove/replace operation");
        }
    }

    /// Replace the given @a oldNode with @a newNode in the rewritten tree.
    void replace(const SyntaxNode& oldNode, SyntaxNode& newNode) {
        if (auto [_, ok] = commits.removeOrReplace.emplace(
                &oldNode, detail::ReplaceChange{&oldNode, &newNode});
            !ok) {
            throw std::logic_error("Node only permit one remove/replace operation");
        }
    }

    /// Insert @a newNode before @a oldNode in the rewritten tree.
    void insertBefore(const SyntaxNode& oldNode, SyntaxNode& newNode) {
        commits.insertBefore[&oldNode].push_back({&oldNode, &newNode});
    }

    /// Insert @a newNode after @a oldNode in the rewritten tree.
    void insertAfter(const SyntaxNode& oldNode, SyntaxNode& newNode) {
        commits.insertAfter[&oldNode].push_back({&oldNode, &newNode});
    }

    /// Insert @a newNode at the front of @a list in the rewritten tree.
    void insertAtFront(const SyntaxListBase& list, SyntaxNode& newNode, Token separator = {}) {
        commits.listInsertAtFront[&list].push_back({&list, &newNode, separator});
    }

    /// Insert @a newNode at the back of @a list in the rewritten tree.
    void insertAtBack(const SyntaxListBase& list, SyntaxNode& newNode, Token separator = {}) {
        commits.listInsertAtBack[&list].push_back({&list, &newNode, separator});
    }

    Token makeToken(TokenKind kind, string_view text) {
        return Token(alloc, kind, {}, text, SourceLocation::NoLocation);
    }

    Token makeId(string_view text) { return makeToken(TokenKind::Identifier, text); }
    Token makeComma() { return makeToken(TokenKind::Comma, ","sv); }

    BumpAllocator alloc;
    SyntaxFactory factory;

private:
    SourceManager* sourceManager = nullptr;
    detail::ChangeCollection commits;
    std::vector<std::shared_ptr<SyntaxTree>> tempTrees;
};

#undef DERIVED

} // namespace slang
