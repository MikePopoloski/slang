//------------------------------------------------------------------------------
// IntervalMap.cpp
// Specialized map data structure with interval keys
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/util/IntervalMap.h"

namespace slang::IntervalMapDetails {

void Path::replaceRoot(void* node, uint32_t size, IndexPair offset) {
    SLANG_ASSERT(!path.empty());
    path.front() = Entry(node, size, offset.first);
    path.insert(path.begin() + 1, Entry(childAt(0), offset.second));
}

void Path::moveLeft(uint32_t level) {
    SLANG_ASSERT(level);

    // Go up the tree until we find a node where we can go left.
    uint32_t l = 0;
    if (valid()) {
        l = level - 1;
        while (path[l].offset == 0) {
            SLANG_ASSERT(l);
            --l;
        }
    }
    else if (height() < level) {
        path.resize(level + 1, Entry(nullptr, 0, 0));
    }

    --path[l].offset;

    // Get the rightmost node of the new subtree.
    NodeRef nodeRef = childAt(l);
    for (++l; l != level; ++l) {
        path[l] = Entry(nodeRef, nodeRef.size() - 1);
        nodeRef = nodeRef.childAt(nodeRef.size() - 1);
    }
    path[l] = Entry(nodeRef, nodeRef.size() - 1);
}

void Path::moveRight(uint32_t level) {
    SLANG_ASSERT(level);

    // Go up the tree until we find a node where we can go right.
    uint32_t l = level - 1;
    while (l && path[l].offset == path[l].size - 1)
        --l;

    // If we hit the end we've gone as far as we can.
    if (++path[l].offset == path[l].size)
        return;

    NodeRef nodeRef = childAt(l);
    for (++l; l != level; ++l) {
        path[l] = Entry(nodeRef, 0);
        nodeRef = nodeRef.childAt(0);
    }
    path[l] = Entry(nodeRef, 0);
}

NodeRef Path::getLeftSibling(uint32_t level) const {
    SLANG_ASSERT(level > 0);

    // Go up until we can go left.
    uint32_t l = level - 1;
    while (l && path[l].offset == 0)
        --l;

    // If we hit the root there is no left sibling.
    if (path[l].offset == 0)
        return NodeRef();

    // Start with left subtree and go down to the right
    // until we reach the original level.
    NodeRef node = path[l].childAt(path[l].offset - 1);
    for (++l; l != level; ++l)
        node = node.childAt(node.size() - 1);
    return node;
}

NodeRef Path::getRightSibling(uint32_t level) const {
    SLANG_ASSERT(level > 0);

    // Go up until we can go right.
    uint32_t l = level - 1;
    while (l && path[l].offset == path[l].size - 1)
        --l;

    // If we hit the root there is no right sibling.
    if (path[l].offset == path[l].size - 1)
        return NodeRef();

    // Start with right subtree and go down to the left
    // until we reach the original level.
    NodeRef node = path[l].childAt(path[l].offset + 1);
    for (++l; l != level; ++l)
        node = node.childAt(0);
    return node;
}

IndexPair distribute(uint32_t numNodes, uint32_t numElements, uint32_t capacity, uint32_t* newSizes,
                     uint32_t position) {
    SLANG_ASSERT(numElements + 1 <= numNodes * capacity);
    SLANG_ASSERT(position <= numElements);
    SLANG_ASSERT(numNodes > 0);

    // left-leaning even distribution
    const uint32_t perNode = (numElements + 1) / numNodes;
    const uint32_t extra = (numElements + 1) % numNodes;
    IndexPair posPair(numNodes, 0);
    uint32_t sum = 0;
    for (uint32_t n = 0; n != numNodes; ++n) {
        sum += newSizes[n] = perNode + (n < extra);
        if (posPair.first == numNodes && sum > position)
            posPair = {n, position - (sum - newSizes[n])};
    }

    // Subtract the new element that was added.
    SLANG_ASSERT(sum == numElements + 1);
    SLANG_ASSERT(posPair.first < numNodes);
    SLANG_ASSERT(newSizes[posPair.first]);
    --newSizes[posPair.first];

    return posPair;
}

} // namespace slang::IntervalMapDetails
