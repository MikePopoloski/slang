//------------------------------------------------------------------------------
// SyntaxVisitor.cpp
// Syntax tree visitor support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/syntax/SyntaxVisitor.h"

namespace {

using namespace slang;
using namespace slang::syntax;
using namespace slang::syntax::detail;

struct CloneVisitor {
    BumpAllocator& alloc;
    const ChangeCollection& commits;

    CloneVisitor(BumpAllocator& alloc, const ChangeCollection& commits) :
        alloc(alloc), commits(commits) {}

#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4127) // conditional expression is constant
#endif
    template<typename T>
    SyntaxNode* visit(const T& node) {
        T* cloned = clone(node, alloc);

        constexpr bool IsList = std::is_same_v<T, SyntaxListBase>;
        SmallVector<TokenOrSyntax, 8> listBuffer;

        if constexpr (IsList) {
            if (auto it = commits.listInsertAtFront.find(&node);
                it != commits.listInsertAtFront.end()) {

                const SyntaxChange* lastChange = nullptr;
                for (const auto& change : it->second) {
                    if (!listBuffer.empty() && change.separator)
                        listBuffer.push_back(change.separator);
                    listBuffer.push_back(change.second);
                    lastChange = &change;
                }

                if (lastChange && node.getChildCount() && lastChange->separator)
                    listBuffer.push_back(lastChange->separator);
            }
        }

        for (size_t i = 0; i < node.getChildCount(); i++) {
            auto child = node.childNode(i);
            if (!child) {
                if constexpr (IsList)
                    listBuffer.push_back(node.childToken(i));
                continue;
            }

            if (auto it = commits.insertBefore.find(child); it != commits.insertBefore.end()) {
                if (!IsList) {
                    throw std::logic_error(
                        "Can't use insertBefore or insertAfter on a non-list node");
                }

                for (const auto& change : it->second)
                    listBuffer.push_back(change.second);
            }

            if (auto it = commits.removeOrReplace.find(child);
                it != commits.removeOrReplace.end()) {
                if (auto replaceChange = std::get_if<ReplaceChange>(&it->second)) {
                    if constexpr (IsList)
                        listBuffer.push_back(replaceChange->second);
                    else
                        cloned->setChild(i, replaceChange->second);
                }
                else {
                    if constexpr (!IsList) {
                        static SyntaxNode* emptyNode = nullptr;
                        cloned->setChild(i, emptyNode);
                    }
                }
            }
            else {
                if constexpr (IsList) {
                    listBuffer.push_back(child->visit(*this));
                }
                else {
                    cloned->setChild(i, child->visit(*this));
                }
            }

            if (auto it = commits.insertAfter.find(child); it != commits.insertAfter.end()) {
                if (!IsList) {
                    throw std::logic_error(
                        "Can't use insertBefore or insertAfter on a non-list node");
                }

                for (const auto& change : it->second)
                    listBuffer.push_back(change.second);
            }
        }

        if constexpr (IsList) {
            if (auto it = commits.listInsertAtBack.find(&node);
                it != commits.listInsertAtBack.end()) {

                for (const auto& change : it->second) {
                    if (!listBuffer.empty() && change.separator)
                        listBuffer.push_back(change.separator);
                    listBuffer.push_back(change.second);
                }
            }

            cloned->resetAll(alloc, listBuffer);
        }

        return cloned;
    }
#ifdef _MSC_VER
#    pragma warning(pop)
#endif

    SyntaxNode* visitInvalid(const SyntaxNode&) {
        ASSUME_UNREACHABLE;
    }
};

} // namespace

namespace slang::syntax::detail {

std::shared_ptr<SyntaxTree> transformTree(
    BumpAllocator&& alloc, const std::shared_ptr<SyntaxTree>& tree, const ChangeCollection& commits,
    const std::vector<std::shared_ptr<SyntaxTree>>& tempTrees) {

    CloneVisitor visitor(alloc, commits);
    SyntaxNode* root = tree->root().visit(visitor);

    // Steal ownership of any temporary syntax trees that the user created; once we return the
    // user expects that the newly transformed tree fully owns all of its memory.
    for (auto& t : tempTrees)
        alloc.steal(std::move(t->allocator()));

    return std::make_shared<SyntaxTree>(root, tree->sourceManager(), std::move(alloc), tree);
}

} // namespace slang::syntax::detail
