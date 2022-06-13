//------------------------------------------------------------------------------
//! @file SyntaxVisitor.h
//! @brief Syntax tree visitor support
//
// File is under the MIT license; see LICENSE for details
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
    Token separator;

    enum Kind { Remove, Replace, InsertBefore, InsertAfter, InsertAtFront, InsertAtBack } kind;

    SyntaxChange(Kind kind, const SyntaxNode* first, SyntaxNode* second, Token separator = {}) :
        first(first), second(second), separator(separator), kind(kind) {}
};

using ChangeMap = flat_hash_map<const SyntaxNode*, detail::SyntaxChange>;
using ListChangeMap = flat_hash_map<const SyntaxNode*, std::vector<detail::SyntaxChange>>;
std::shared_ptr<SyntaxTree> transformTree(
    BumpAllocator&& alloc, const std::shared_ptr<SyntaxTree>& tree, const ChangeMap& changes,
    const ListChangeMap& listAdditions, const std::vector<std::shared_ptr<SyntaxTree>>& tempTrees);

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
        changes.clear();
        tempTrees.clear();

        tree->root().visit(*this);

        if (changes.empty())
            return tree;

        return transformTree(std::move(alloc), tree, changes, listAdditions, tempTrees);
    }

protected:
    /// A helper for derived classes that parses some text into syntax nodes.
    SyntaxNode& parse(string_view text) {
        tempTrees.emplace_back(SyntaxTree::fromText(text, *sourceManager));
        return tempTrees.back()->root();
    }

    /// Register a removal for the given syntax node from the tree.
    void remove(const SyntaxNode& oldNode) {
        changes.emplace(&oldNode,
                        detail::SyntaxChange{ detail::SyntaxChange::Remove, &oldNode, nullptr });
    }

    /// Replace the given @a oldNode with @a newNode in the rewritten tree.
    void replace(const SyntaxNode& oldNode, SyntaxNode& newNode) {
        changes.emplace(&oldNode,
                        detail::SyntaxChange{ detail::SyntaxChange::Replace, &oldNode, &newNode });
    }

    /// Insert @a newNode before @a oldNode in the rewritten tree.
    void insertBefore(const SyntaxNode& oldNode, SyntaxNode& newNode) {
        changes.emplace(&oldNode, detail::SyntaxChange{ detail::SyntaxChange::InsertBefore,
                                                        &oldNode, &newNode });
    }

    /// Insert @a newNode after @a oldNode in the rewritten tree.
    void insertAfter(const SyntaxNode& oldNode, SyntaxNode& newNode) {
        changes.emplace(&oldNode, detail::SyntaxChange{ detail::SyntaxChange::InsertAfter, &oldNode,
                                                        &newNode });
    }

    /// Insert @a newNode at the front of @a list in the rewritten tree.
    void insertAtFront(const SyntaxListBase& list, SyntaxNode& newNode, Token separator = {}) {
        listAdditions[&list].push_back(
            { detail::SyntaxChange::InsertAtFront, &list, &newNode, separator });
    }

    /// Insert @a newNode at the back of @a list in the rewritten tree.
    void insertAtBack(const SyntaxListBase& list, SyntaxNode& newNode, Token separator = {}) {
        listAdditions[&list].push_back(
            { detail::SyntaxChange::InsertAtBack, &list, &newNode, separator });
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
    detail::ChangeMap changes;
    detail::ListChangeMap listAdditions;
    std::vector<std::shared_ptr<SyntaxTree>> tempTrees;
};

#undef DERIVED

} // namespace slang
