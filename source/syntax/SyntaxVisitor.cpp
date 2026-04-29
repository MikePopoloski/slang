//------------------------------------------------------------------------------
// SyntaxVisitor.cpp
// Syntax tree visitor support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/SyntaxVisitor.h"

#include <variant>

#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxListInfo.h"

namespace {

using namespace slang;
using namespace slang::syntax;
using namespace slang::syntax::detail;

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

#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4127) // conditional expression is constant
#endif
    // Clone the contents of one list-typed child slot, applying any pending
    // edits (insertBefore/insertAfter on elements, replace/remove on elements,
    // listInsertAtFront/listInsertAtBack on the list, and removeToken/
    // replaceToken on separators). Writes the result into the destination
    // list via the type-erased `resetAll` thunk in @a dstList. Returns the
    // number of children written so the caller can advance its destination
    // flat index.
    template<typename T>
    size_t cloneList(const T& srcNode, const ListChildInfo& srcList, const ListChildInfo& dstList) {
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
                listBuffer.push_back(child->visit(*this));
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
    template<typename T>
    void cloneChild(const T& node, size_t srcIndex, T& cloned, size_t dstIndex) {
        auto child = node.childNode(srcIndex);
        if (!child) {
            if (node.getChild(srcIndex).isToken()) {
                if (auto it = commits.tokenRemoveOrReplace.find(
                        std::make_pair(static_cast<const void*>(&node), srcIndex));
                    it != commits.tokenRemoveOrReplace.end()) {
                    if (auto replaceChange = std::get_if<TokenReplaceChange>(&it->second)) {
                        cloned.setChild(dstIndex, replaceChange->newToken);
                    }
                    else {
                        auto removeChange = std::get_if<TokenRemoveChange>(&it->second);
                        if (removeChange && removeChange->preserveTrivia) {
                            this->previousTrivia = copyTrivia(node.childToken(srcIndex).trivia());
                        }
                        cloned.setChild(dstIndex, parsing::Token());
                    }
                }
                else {
                    if (this->previousTrivia.empty()) {
                        cloned.setChild(dstIndex, node.childToken(srcIndex).deepClone(alloc));
                    }
                    else {
                        cloned.setChild(dstIndex,
                                        node.childToken(srcIndex).deepClone(alloc).withTrivia(
                                            alloc, this->previousTrivia));
                        this->previousTrivia = {};
                    }
                }
            }
            return;
        }

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
            cloned.setChild(dstIndex, child->visit(*this));
        }
    }

    // Convenience overload used by the simple flat-index path for parents
    // without list members; here srcIndex == dstIndex.
    template<typename T>
    void cloneChild(const T& node, size_t i, T& cloned) {
        cloneChild(node, i, cloned, i);
    }

    template<typename T>
    SyntaxNode* visit(const T& node) {
        T* cloned = clone(node, alloc);

        // Discover any list-typed child slots so we can dispatch list-level
        // edits via the rewriter machinery. Most node types have no lists,
        // in which case we fall back to a simple flat-index walk.
        SmallVector<ListChildInfo, 2> srcLists, dstLists;
        getChildListInfo(const_cast<T&>(node), srcLists);
        getChildListInfo(*cloned, dstLists);

        if (srcLists.empty()) {
            const size_t count = node.getChildCount();
            for (size_t i = 0; i < count; i++)
                cloneChild(node, i, *cloned);
            return cloned;
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
                cloneChild(node, srcIdx, *cloned, dstIdx);
                ++srcIdx;
                ++dstIdx;
            }
        }

        return cloned;
    }
#ifdef _MSC_VER
#    pragma warning(pop)
#endif
};

} // namespace

namespace slang::syntax::detail {

std::shared_ptr<SyntaxTree> transformTree(BumpAllocator&& alloc,
                                          const std::shared_ptr<SyntaxTree>& tree,
                                          const ChangeCollection& commits,
                                          const std::vector<std::shared_ptr<SyntaxTree>>& tempTrees,
                                          const SourceLibrary* library) {
    CloneVisitor visitor(alloc, commits);
    SyntaxNode* root = tree->root().visit(visitor);

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
