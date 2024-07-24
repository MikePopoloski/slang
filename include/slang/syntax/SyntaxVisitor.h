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

namespace slang::syntax {

#define DERIVED static_cast<TDerived*>(this)

/// Use this type as a base class for syntax tree visitors. It will default to
/// traversing all children of each node. Add implementations for any specific
/// node types you want to handle.
template<typename TDerived>
class SyntaxVisitor {
public:
    /// Visit the provided node, of static type T.
    template<typename T>
    void visit(T&& t) {
        if constexpr (requires { DERIVED->handle(t); })
            DERIVED->handle(t);
        else
            DERIVED->visitDefault(t);
    }

    /// The default handler invoked when no visit() method is overridden for a particular type.
    /// Will visit all child nodes by default.
    template<typename T>
    void visitDefault(T&& node) {
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
    void visitToken(parsing::Token) {}
};

namespace detail {

struct SLANG_EXPORT SyntaxChange {
    const SyntaxNode* first = nullptr;
    SyntaxNode* second = nullptr;
    parsing::Token separator = {};
};

struct SLANG_EXPORT RemoveChange : SyntaxChange {};
struct SLANG_EXPORT ReplaceChange : SyntaxChange {};

using InsertChangeMap = flat_hash_map<const SyntaxNode*, std::vector<SyntaxChange>>;
using ModifyChangeMap = flat_hash_map<const SyntaxNode*, std::variant<RemoveChange, ReplaceChange>>;
using ListChangeMap = flat_hash_map<const SyntaxNode*, std::vector<SyntaxChange>>;

struct SLANG_EXPORT ChangeCollection {
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

SLANG_EXPORT std::shared_ptr<SyntaxTree> transformTree(
    BumpAllocator&& alloc, const std::shared_ptr<SyntaxTree>& tree, const ChangeCollection& commits,
    const std::vector<std::shared_ptr<SyntaxTree>>& tempTrees, const SourceLibrary* library);

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
    ///
    /// @note lifetimes of new and old trees are independent from each other. If you
    /// shallow clone something from old tree into new one, you have to make sure that
    /// shared_ptr to original doesn't go out of scope too early.
    std::shared_ptr<SyntaxTree> transform(const std::shared_ptr<SyntaxTree>& tree,
                                          const SourceLibrary* library = nullptr) {
        sourceManager = &tree->sourceManager();
        commits.clear();
        tempTrees.clear();

        tree->root().visit(*DERIVED);

        if (commits.empty())
            return tree;

        return transformTree(std::move(alloc), tree, commits, tempTrees, library);
    }

protected:
    using Token = parsing::Token;

    /// A helper for derived classes that parses some text into syntax nodes.
    SyntaxNode& parse(std::string_view text) {
        tempTrees.emplace_back(SyntaxTree::fromText(text, *sourceManager));
        return tempTrees.back()->root();
    }

    /// Register a removal for the given syntax node from the tree.
    void remove(const SyntaxNode& oldNode) {
        if (auto [_, ok] = commits.removeOrReplace.emplace(&oldNode,
                                                           detail::RemoveChange{&oldNode, nullptr});
            !ok) {
            SLANG_THROW(std::logic_error("Node only permit one remove/replace operation"));
        }
    }

    /// Replace the given @a oldNode with @a newNode in the rewritten tree.
    void replace(const SyntaxNode& oldNode, SyntaxNode& newNode) {
        if (auto [_, ok] = commits.removeOrReplace.emplace(
                &oldNode, detail::ReplaceChange{&oldNode, &newNode});
            !ok) {
            SLANG_THROW(std::logic_error("Node only permit one remove/replace operation"));
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

    Token makeToken(parsing::TokenKind kind, std::string_view text,
                    std::span<const parsing::Trivia> trivia = {}) {
        return Token(alloc, kind, trivia, text, SourceLocation::NoLocation);
    }

    Token makeId(std::string_view text, std::span<const parsing::Trivia> trivia = {}) {
        return makeToken(parsing::TokenKind::Identifier, text, trivia);
    }

    Token makeId(std::string_view text, parsing::Trivia trivia) {
        auto triviaPtr = alloc.emplace<parsing::Trivia>(trivia);
        return makeId(text, {triviaPtr, 1});
    }

    Token makeComma() { return makeToken(parsing::TokenKind::Comma, ","sv); }

    BumpAllocator alloc;
    SyntaxFactory factory;

    static const parsing::Trivia SingleSpace;

private:
    SourceManager* sourceManager = nullptr;
    detail::ChangeCollection commits;
    std::vector<std::shared_ptr<SyntaxTree>> tempTrees;
};

template<typename TDerived>
const parsing::Trivia SyntaxRewriter<TDerived>::SingleSpace{parsing::TriviaKind::Whitespace, " "sv};

#undef DERIVED

} // namespace slang::syntax
