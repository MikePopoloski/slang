//------------------------------------------------------------------------------
//! @file SyntaxRewriter.h
//! @brief Syntax tree rewriter support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <utility>
#include <variant>
#include <vector>

#include "slang/parsing/Token.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/util/FlatMap.h"
#include "slang/util/TypeTraits.h"

namespace slang::syntax {

namespace detail {

struct SLANG_EXPORT SyntaxChange {
    const SyntaxNode* first = nullptr;
    SyntaxNode* second = nullptr;
    parsing::Token separator = {};
};

struct SLANG_EXPORT RemoveChange : SyntaxChange {};
struct SLANG_EXPORT ReplaceChange : SyntaxChange {};

struct SLANG_EXPORT TokenRemoveChange {
    bool preserveTrivia = false;
};

struct SLANG_EXPORT TokenReplaceChange {
    parsing::Token newToken = {};
};

using InsertChangeMap = flat_hash_map<const SyntaxNode*, std::vector<SyntaxChange>>;
using ModifyChangeMap = flat_hash_map<const SyntaxNode*, std::variant<RemoveChange, ReplaceChange>>;
using ListChangeMap = flat_hash_map<const void*, std::vector<SyntaxChange>>;
using TokenModifyChangeMap = flat_hash_map<std::pair<const void*, size_t>,
                                           std::variant<TokenRemoveChange, TokenReplaceChange>>;

struct SLANG_EXPORT ChangeCollection {
    InsertChangeMap insertBefore;
    InsertChangeMap insertAfter;
    ModifyChangeMap removeOrReplace;
    ListChangeMap listInsertAtFront;
    ListChangeMap listInsertAtBack;
    TokenModifyChangeMap tokenRemoveOrReplace;

    void clear() {
        insertBefore.clear();
        insertAfter.clear();
        removeOrReplace.clear();
        listInsertAtFront.clear();
        listInsertAtBack.clear();
        tokenRemoveOrReplace.clear();
    }

    bool empty() const {
        return insertBefore.empty() && insertAfter.empty() && removeOrReplace.empty() &&
               listInsertAtFront.empty() && listInsertAtBack.empty() &&
               tokenRemoveOrReplace.empty();
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

        tree->root().visit(*static_cast<TDerived*>(this));

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
            SLANG_THROW(std::logic_error("Nodes only permit one remove/replace operation"));
        }
    }

    /// Remove a token at the given index within the specified node.
    void removeToken(const SyntaxNode& node, size_t index, bool preserveTrivia = false) {
        if (auto [_, ok] = commits.tokenRemoveOrReplace.emplace(
                std::make_pair(static_cast<const void*>(&node), index),
                detail::TokenRemoveChange{preserveTrivia});
            !ok) {
            SLANG_THROW(std::logic_error("Tokens only permit one remove/replace operation"));
        }
    }

    /// Remove a token at the given index within the specified list.
    template<typename TList>
        requires is_syntax_list_v<TList>
    void removeToken(const TList& list, size_t index, bool preserveTrivia = false) {
        if (auto [_, ok] = commits.tokenRemoveOrReplace.emplace(
                std::make_pair(static_cast<const void*>(&list), index),
                detail::TokenRemoveChange{preserveTrivia});
            !ok) {
            SLANG_THROW(std::logic_error("Tokens only permit one remove/replace operation"));
        }
    }

    /// Replace the given @a oldNode with @a newNode in the rewritten tree.
    void replace(const SyntaxNode& oldNode, SyntaxNode& newNode, bool preserveTrivia = false) {
        if (preserveTrivia) {
            if (auto oldTok = oldNode.getFirstToken()) {
                if (auto newTok = newNode.getFirstTokenPtr())
                    *newTok = newTok->withTrivia(alloc, oldTok.trivia());
            }
        }

        if (auto [_, ok] = commits.removeOrReplace.emplace(
                &oldNode, detail::ReplaceChange{&oldNode, &newNode});
            !ok) {
            SLANG_THROW(std::logic_error("Nodes only permit one remove/replace operation"));
        }
    }

    /// Replace a token at the given index within the specified node with @a newToken.
    void replaceToken(const SyntaxNode& node, size_t index, Token newToken,
                      bool preserveTrivia = false) {
        if (preserveTrivia) {
            if (auto oldTok = node.childToken(index)) {
                if (!oldTok.trivia().empty()) {
                    SmallVector<parsing::Trivia, 8> triviaBuffer(oldTok.trivia().size(),
                                                                 UninitializedTag());
                    for (const auto& t : oldTok.trivia())
                        triviaBuffer.push_back(t.clone(alloc, true));
                    newToken = newToken.withTrivia(alloc, triviaBuffer);
                }
            }
        }

        if (auto [_, ok] = commits.tokenRemoveOrReplace.emplace(
                std::make_pair(static_cast<const void*>(&node), index),
                detail::TokenReplaceChange{newToken});
            !ok) {
            SLANG_THROW(std::logic_error("Tokens only permit one remove/replace operation"));
        }
    }

    /// Replace a token at the given index within the specified list.
    template<typename TList>
        requires is_syntax_list_v<TList>
    void replaceToken(const TList& list, size_t index, Token newToken,
                      bool preserveTrivia = false) {
        if (preserveTrivia) {
            if (index < list.getChildCount()) {
                auto child = list.getChild(index);
                if (child.isToken()) {
                    auto oldTok = child.token();
                    if (!oldTok.trivia().empty()) {
                        SmallVector<parsing::Trivia, 8> triviaBuffer(oldTok.trivia().size(),
                                                                     UninitializedTag());
                        for (const auto& t : oldTok.trivia())
                            triviaBuffer.push_back(t.clone(alloc, true));
                        newToken = newToken.withTrivia(alloc, triviaBuffer);
                    }
                }
            }
        }

        if (auto [_, ok] = commits.tokenRemoveOrReplace.emplace(
                std::make_pair(static_cast<const void*>(&list), index),
                detail::TokenReplaceChange{newToken});
            !ok) {
            SLANG_THROW(std::logic_error("Tokens only permit one remove/replace operation"));
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
    template<typename TList>
        requires is_syntax_list_v<TList>
    void insertAtFront(const TList& list, SyntaxNode& newNode, Token separator = {}) {
        commits.listInsertAtFront[static_cast<const void*>(&list)].push_back(
            {nullptr, &newNode, separator});
    }

    /// Insert @a newNode at the back of @a list in the rewritten tree.
    template<typename TList>
        requires is_syntax_list_v<TList>
    void insertAtBack(const TList& list, SyntaxNode& newNode, Token separator = {}) {
        commits.listInsertAtBack[static_cast<const void*>(&list)].push_back(
            {nullptr, &newNode, separator});
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

} // namespace slang::syntax
