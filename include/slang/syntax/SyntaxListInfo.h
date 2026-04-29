//------------------------------------------------------------------------------
//! @file SyntaxListInfo.h
//! @brief Reflection helpers for list-typed children of syntax nodes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <span>

#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang {
class BumpAllocator;
}

namespace slang::syntax {

class SyntaxNode;
struct TokenOrSyntax;

/// @brief Reflection metadata for a single list-typed child slot of a SyntaxNode.
///
/// Used by SyntaxRewriter to identify list members during cloning so that
/// list-level edits (insertAtFront/insertAtBack, separator token edits) can
/// be applied generically without per-type helper methods.
struct SLANG_EXPORT ListChildInfo {
    /// Address of the list member; used as a stable identity key for
    /// list-level edits in the rewriter.
    void* listPtr = nullptr;

    /// Flat child index at which this list begins.
    size_t flatStart = 0;

    /// Number of flat child slots this list currently contributes.
    size_t size = 0;

    /// Type-erased thunk that replaces the list's contents with the
    /// provided children, allocating in @a alloc. Only meaningful when
    /// applied to a mutable destination node.
    void (*resetAll)(void* listPtr, BumpAllocator& alloc,
                     std::span<const TokenOrSyntax> children) = nullptr;

    template<typename TList>
    ListChildInfo(TList& list, size_t start) :
        listPtr(&list), flatStart(start), size(list.getChildCount()),
        resetAll([](void* listPtr, BumpAllocator& alloc, std::span<const TokenOrSyntax> children) {
            static_cast<TList*>(listPtr)->resetAll(alloc, children);
        }) {}
};

/// @brief Fills @a out with reflection descriptors for any list-typed
/// child slots of @a node, in flat-index order.
///
/// Used by SyntaxRewriter to apply list-level edits during cloning.
SLANG_EXPORT void getChildListInfo(SyntaxNode& node, SmallVector<ListChildInfo, 2>& out);

} // namespace slang::syntax
