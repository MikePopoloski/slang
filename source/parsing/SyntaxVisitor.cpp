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
    const slang::detail::ChangeMap& changes;

    CloneVisitor(BumpAllocator& alloc, const slang::detail::ChangeMap& changes) :
        alloc(alloc), changes(changes) {}

#ifdef _MSC_VER
#pragma warning(push)
#pragma warning(disable: 4127)  // conditional expression is constant
#endif
    template<typename T>
    SyntaxNode* visit(const T& node) {
        T* cloned = node.clone(alloc);

        constexpr bool IsList = std::is_same_v<T, SyntaxListBase>;
        optional<SmallVectorSized<TokenOrSyntax, 8>> listBuffer;

        auto backfillList = [&](uint32_t index) {
            if (cloned->kind != SyntaxKind::SyntaxList && cloned->kind != SyntaxKind::SeparatedList)
                throw std::logic_error("Can't use insertBefore or insertAfter on a non-list node");

            listBuffer.emplace();
            for (uint32_t i = 0; i < index; i++)
                listBuffer->append(cloned->getChild(i));
        };

        for (uint32_t i = 0; i < node.getChildCount(); i++) {
            auto child = node.childNode(i);
            if (!child) {
                if (IsList && listBuffer)
                    listBuffer->append(node.childToken(i));
                continue;
            }

            // We might not know until we're part way through a list that we
            // want to insert or remove elements from it. Once we see the first
            // modification we start building the buffer instead, and then replace
            // the whole list in one go at the end.
            auto it = changes.find(child);
            if (it == changes.end()) {
                if (IsList && listBuffer)
                    listBuffer->append(child->visit(*this));
                else
                    cloned->setChild(i, child->visit(*this));
            }
            else {
                switch (it->second.kind) {
                    case slang::detail::SyntaxChange::Remove:
                        THROW_UNREACHABLE; // TODO: implement this

                    case slang::detail::SyntaxChange::Replace:
                        if (IsList && listBuffer)
                            listBuffer->append(it->second.second);
                        else
                            cloned->setChild(i, it->second.second);
                        break;
                    case slang::detail::SyntaxChange::InsertBefore:
                        if (!listBuffer)
                            backfillList(i);
                        listBuffer->append(it->second.second);
                        listBuffer->append(child->visit(*this));
                        break;
                    case slang::detail::SyntaxChange::InsertAfter:
                        if (!listBuffer)
                            backfillList(i);
                        listBuffer->append(child->visit(*this));
                        listBuffer->append(it->second.second);
                        break;
                    default:
                        THROW_UNREACHABLE;
                }
            }
        }

        if constexpr (IsList) {
            if (listBuffer) {
                cloned->resetAll(alloc, *listBuffer);
                listBuffer.reset();
            }
        }

        return cloned;
    }
#ifdef _MSC_VER
#pragma warning(pop)
#endif

    SyntaxNode* visitInvalid(const SyntaxNode&) { THROW_UNREACHABLE; }
};

}

namespace slang {

namespace detail {

std::shared_ptr<SyntaxTree> transformTree(const std::shared_ptr<SyntaxTree>& tree, const ChangeMap& changes,
                                          const std::vector<std::shared_ptr<SyntaxTree>>& tempTrees) {
    BumpAllocator alloc;
    CloneVisitor visitor(alloc, changes);

    SyntaxNode* root = tree->root().visit(visitor);

    // Steal ownership of any temporary syntax trees that the user created; once we return the
    // user expects that the newly transformed tree fully owns all of its memory.
    for (auto& t : tempTrees)
        alloc.steal(std::move(t->allocator()));

    return std::make_shared<SyntaxTree>(root, tree->sourceManager(), std::move(alloc), tree);
}

}

}
