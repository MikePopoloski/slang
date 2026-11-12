//------------------------------------------------------------------------------
// SyntaxRewriter.cpp
// Syntax tree rewriter support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/SyntaxRewriter.h"

#include <variant>

#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxListInfo.h"

namespace slang::syntax::detail {

struct CloneVisitor {
    BumpAllocator& alloc;
    const ChangeCollection& commits;
    std::span<const parsing::Trivia> previousTrivia;

    CloneVisitor(BumpAllocator& alloc, const ChangeCollection& commits) :
        alloc(alloc), commits(commits) {}

    std::span<const parsing::Trivia> copyTrivia(std::span<const parsing::Trivia> trivia) {
        if (trivia.empty())
            return {};

        SmallVector<parsing::Trivia, 8> triviaBuffer(trivia.size(), UninitializedTag());
        for (const auto& t : trivia)
            triviaBuffer.push_back(t.clone(alloc, true));
        return triviaBuffer.copy(alloc);
    }

    // Clone the contents of one list-typed child slot, applying any pending
    // edits (insertBefore/insertAfter on elements, replace/remove on elements,
    // listInsertAtFront/listInsertAtBack on the list, and removeToken/
    // replaceToken on separators). Writes the result into the destination
    // list via the type-erased `resetAll` thunk in @a dstList. Returns the
    // number of children written so the caller can advance its destination
    // flat index.
    size_t cloneList(const SyntaxNode& srcNode, const ListChildInfo& srcList,
                     const ListChildInfo& dstList) {
        SmallVector<TokenOrSyntax, 8> listBuffer;
        bool skipSeparator = false;
        const void* listKey = srcList.listPtr;

        if (auto it = commits.listInsertAtFront.find(listKey);
            it != commits.listInsertAtFront.end()) {

            const SyntaxChange* lastChange = nullptr;
            for (const auto& change : it->second) {
                if (!listBuffer.empty() && change.separator)
                    listBuffer.push_back(change.separator);
                listBuffer.push_back(change.second);
                lastChange = &change;
            }

            if (lastChange && srcList.size && lastChange->separator)
                listBuffer.push_back(lastChange->separator);
        }

        for (size_t i = 0; i < srcList.size; i++) {
            ConstTokenOrSyntax origChild = srcNode.getChild(srcList.flatStart + i);
            const SyntaxNode* child = origChild.isNode() ? origChild.node() : nullptr;
            if (!child) {
                if (auto it = commits.tokenRemoveOrReplace.find(std::make_pair(listKey, i));
                    it != commits.tokenRemoveOrReplace.end()) {
                    if (auto replaceChange = std::get_if<TokenReplaceChange>(&it->second))
                        listBuffer.push_back(replaceChange->newToken);
                    else {
                        auto removeChange = std::get_if<TokenRemoveChange>(&it->second);
                        if (removeChange && removeChange->preserveTrivia) {
                            this->previousTrivia = copyTrivia(origChild.token().trivia());
                        }
                    }
                }
                else if (!skipSeparator) {
                    if (this->previousTrivia.empty()) {
                        listBuffer.push_back(origChild.token().deepClone(alloc));
                    }
                    else {
                        listBuffer.push_back(origChild.token().deepClone(alloc).withTrivia(
                            alloc, this->previousTrivia));
                        this->previousTrivia = {};
                    }
                }
                skipSeparator = false;
                continue;
            }

            if (auto it = commits.insertBefore.find(child); it != commits.insertBefore.end()) {
                for (const auto& change : it->second)
                    listBuffer.push_back(change.second);
            }

            if (auto it = commits.removeOrReplace.find(child);
                it != commits.removeOrReplace.end()) {
                if (auto replaceChange = std::get_if<ReplaceChange>(&it->second)) {
                    listBuffer.push_back(replaceChange->second);
                }
                else {
                    skipSeparator = true; // remove separator related to removed node
                }
            }
            else {
                listBuffer.push_back(cloneNode(*child));
            }

            if (auto it = commits.insertAfter.find(child); it != commits.insertAfter.end()) {
                for (const auto& change : it->second)
                    listBuffer.push_back(change.second);
            }
        }

        if (skipSeparator) {
            // remove trailing sep if it wasn't there before transform
            bool isClonedTrailing = !listBuffer.empty() && listBuffer.back().isToken();
            bool isOriginalTrailing =
                srcList.size && srcNode.getChild(srcList.flatStart + srcList.size - 1).isToken();
            if (isClonedTrailing && !isOriginalTrailing)
                listBuffer.pop_back();
        }

        if (auto it = commits.listInsertAtBack.find(listKey);
            it != commits.listInsertAtBack.end()) {

            for (const auto& change : it->second) {
                if (!listBuffer.empty() && change.separator)
                    listBuffer.push_back(change.separator);
                listBuffer.push_back(change.second);
            }
        }

        dstList.resetAll(dstList.listPtr, alloc, listBuffer);
        return listBuffer.size();
    }

    // Apply pending changes to a single non-list child slot of the given node / index,
    // writing the result into `cloned` at flat index `dstIndex`. The two indices may differ
    // when the parent has list members whose sizes change between source and destination.
    void cloneChild(const SyntaxNode& node, size_t srcIndex, SyntaxNode& cloned, size_t dstIndex) {
        auto origChild = node.getChild(srcIndex);
        if (origChild.isToken()) {
            auto token = origChild.token();
            if (auto it = commits.tokenRemoveOrReplace.find(
                    std::make_pair(static_cast<const void*>(&node), srcIndex));
                it != commits.tokenRemoveOrReplace.end()) {
                if (auto replaceChange = std::get_if<TokenReplaceChange>(&it->second)) {
                    cloned.setChild(dstIndex, replaceChange->newToken);
                }
                else {
                    auto removeChange = std::get_if<TokenRemoveChange>(&it->second);
                    if (removeChange && removeChange->preserveTrivia) {
                        this->previousTrivia = copyTrivia(token.trivia());
                    }
                    cloned.setChild(dstIndex, parsing::Token());
                }
            }
            else {
                if (this->previousTrivia.empty()) {
                    cloned.setChild(dstIndex, token.deepClone(alloc));
                }
                else {
                    cloned.setChild(dstIndex,
                                    token.deepClone(alloc).withTrivia(alloc, this->previousTrivia));
                    this->previousTrivia = {};
                }
            }
            return;
        }

        auto child = origChild.node();
        if (!child)
            return;

        if (auto it = commits.removeOrReplace.find(child); it != commits.removeOrReplace.end()) {
            if (auto replaceChange = std::get_if<ReplaceChange>(&it->second)) {
                cloned.setChild(dstIndex, replaceChange->second);
            }
            else {
                static SyntaxNode* emptyNode = nullptr;
                cloned.setChild(dstIndex, emptyNode);
            }
        }
        else {
            cloned.setChild(dstIndex, cloneNode(*child));
        }
    }

    SyntaxNode* cloneNode(const SyntaxNode& node) {
        SyntaxNode* cloned = clone(node, alloc);
        cloneChildren(node, *cloned);

        // The shallow clone still points at the original node's parent, and the
        // children we kept or inserted still point at their old parents, so wire
        // everything up to the new tree. The cloned node's own parent gets set when
        // its parent finishes, and the root's stays null.
        //
        // Also propagate the contains-enum mark up from children. Inserted nodes
        // that came from another parsed tree are already marked, which would stop
        // the new tree from marking their new ancestors.
        cloned->parent = nullptr;
        for (size_t i = 0; i < cloned->getChildCount(); i++) {
            if (auto child = cloned->childNode(i)) {
                child->parent = cloned;
                if (child->containsEnum())
                    cloned->markContainsEnum();
            }
        }
        return cloned;
    }

    void cloneChildren(const SyntaxNode& node, SyntaxNode& cloned) {
        // Discover any list-typed child slots so we can dispatch list-level
        // edits via the rewriter machinery. Most node types have no lists,
        // in which case we fall back to a simple flat-index walk.
        SmallVector<ListChildInfo, 2> srcLists, dstLists;
        getChildListInfo(const_cast<SyntaxNode&>(node), srcLists);
        getChildListInfo(cloned, dstLists);

        if (srcLists.empty()) {
            const size_t count = node.getChildCount();
            for (size_t i = 0; i < count; i++)
                cloneChild(node, i, cloned, i);
            return;
        }

        // Walk children in source order so that pending trivia (e.g. from a
        // token removal) can flow forward to the next token across list
        // boundaries. The destination index can diverge from the source
        // index when list sizes change due to inserts/removes.
        const size_t srcCount = node.getChildCount();
        size_t srcIdx = 0;
        size_t dstIdx = 0;
        size_t listIdx = 0;
        while (srcIdx < srcCount) {
            if (listIdx < srcLists.size() && srcLists[listIdx].flatStart == srcIdx) {
                const size_t newDstSize = cloneList(node, srcLists[listIdx], dstLists[listIdx]);
                srcIdx += srcLists[listIdx].size;
                dstIdx += newDstSize;
                ++listIdx;
            }
            else {
                cloneChild(node, srcIdx, cloned, dstIdx);
                ++srcIdx;
                ++dstIdx;
            }
        }
    }
};

std::shared_ptr<SyntaxTree> transformTree(BumpAllocator&& alloc,
                                          const std::shared_ptr<SyntaxTree>& tree,
                                          const ChangeCollection& commits,
                                          const std::vector<std::shared_ptr<SyntaxTree>>& tempTrees,
                                          const SourceLibrary* library) {
    CloneVisitor visitor(alloc, commits);
    SyntaxNode* root = visitor.cloneNode(tree->root());

    // Steal ownership of any temporary syntax trees that the user created; once we return the
    // user expects that the newly transformed tree fully owns all of its memory.
    for (auto& t : tempTrees)
        alloc.steal(std::move(t->allocator()));

    auto newTree = std::make_shared<SyntaxTree>(root, tree->sourceManager(), std::move(alloc),
                                                library, tree);
    alloc = BumpAllocator(); // creation of newTree invalidated our old alloc
    return newTree;
}

} // namespace slang::syntax::detail
