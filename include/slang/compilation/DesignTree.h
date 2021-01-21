//------------------------------------------------------------------------------
//! @file DesignTree.h
//! @brief Post-AST elaborated design tree
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang {

class Compilation;
class Scope;
class Symbol;

/// A storage element is representative of a single net or variable in the
/// post-elaboration design tree.
class StorageElement {
public:
    const Symbol& symbol;
};

/// The design tree is the post-elaboration hierarchy of de-duplicated instances,
/// containing storage elements (nets and variables). This simplified view can be
/// used for final upward-name resolution and multi-driver checks.
class DesignTreeNode {
public:
    const Scope& astScope;
    span<const DesignTreeNode* const> childNodes;
    span<const StorageElement* const> storageElements;

    DesignTreeNode(const Scope& astScope, span<const DesignTreeNode* const> childNodes,
                   span<const StorageElement* const> storageElements) :
        astScope(astScope),
        childNodes(childNodes), storageElements(storageElements) {}

    static DesignTreeNode& build(Compilation& compilation);
};

} // namespace slang
