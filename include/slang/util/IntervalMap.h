//------------------------------------------------------------------------------
//! @file IntervalMap.h
//! @brief Specialized map data structure with interval keys
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/PointerIntPair.h"
#include "slang/util/PoolAllocator.h"
#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang {

namespace IntervalMapDetails {

// Note: the implementation here is inspired by the corresponding type from LLVM:
// https://llvm.org/doxygen/IntervalMap_8h_source.html
//
// The data structure here though has several important modifications, e.g.
// intervals are allowed to overlap here but not in LLVM's version.

template<typename T>
struct interval {
    T left;
    T right;

    void unionWith(const interval<T>& rhs) {
        left = std::min(left, rhs.left);
        right = std::max(right, rhs.right);
    }
};

template<typename T>
bool operator<(const interval<T>& a, const interval<T>& b) {
    return a.left < b.left || (a.left == b.left && a.right < b.right);
}

using IndexPair = std::pair<uint32_t, uint32_t>;

// Base class for nodes in the interval tree. Nodes are either leaf nodes,
// which store the intervals and mapped values, or branch nodes, which store
// references to child nodes and intervals that encapsulate the entire range
// of each child.
//
// Nodes don't know how many elements they contain -- that information is stored
// in their parent.
template<typename TKey, typename TValue, uint32_t N>
struct NodeBase {
    enum { Capacity = N };

    // Keys and values are stored in separate arrays to avoid padding
    // caused by differing alignments of TKey and TValue.
    TKey first[Capacity];
    TValue second[Capacity];

    // Copies child elements from @a other, from the range [src, src+count) to [dst, dst+count)
    template<uint32_t M>
    void copy(const NodeBase<TKey, TValue, M>& other, uint32_t src, uint32_t dst, uint32_t count) {
        ASSERT(src + count <= M && dst + count <= N);
        for (uint32_t end = src + count; src != end; src++, dst++) {
            first[dst] = other.first[src];
            second[dst] = other.second[src];
        }
    }

    // Moves child nodes to the right, from [src, src+count) to [dst, dst+count)
    void moveRight(uint32_t src, uint32_t dst, uint32_t count) {
        ASSERT(src <= dst && dst + count <= Capacity);
        while (count--) {
            first[dst + count] = first[src + count];
            second[dst + count] = second[src + count];
        }
    }
};

enum {
    // Size our nodes based on a multiple of cache line size.
    // This assumes 64 bytes, which is a pretty reasonable default
    // for most modern systems.
    Log2CacheLine = 6,
    CacheLineBytes = 1 << Log2CacheLine
};

// A pointer to a leaf or branch node, along with the number of elements
// in the pointed-to child. All nodes are cache line aligned so we can
// use the lower 6 bits of the pointer to store the count.
//
// A NodeRef doesn't know if it points to a leaf or a branch, the parent
// that owns the NodeRef needs to keep track.
//
// Nodes are never empty, so size of 0 is invalid (so the stored range is
// able to express 1-64 children).
struct NodeRef {
    NodeRef() = default;

    template<typename T>
    NodeRef(T* node, uint32_t s) : pip(node, s) {
        ASSERT(s);
    }

    uint32_t size() const { return pip.getInt() + 1; }

    void setSize(uint32_t s) {
        ASSERT(s);
        pip.setInt(s - 1);
    }

    template<typename T>
    T& get() const {
        return *reinterpret_cast<T*>(pip.getPointer());
    }

    // Accesses the i'th subtree reference in a branch node.
    // This depends on branch nodes storing the NodeRef array as their first
    // member.
    NodeRef& childAt(uint32_t i) const { return reinterpret_cast<NodeRef*>(pip.getPointer())[i]; }

    explicit operator bool() const { return pip.getOpaqueValue(); }

    bool operator==(const NodeRef& rhs) const {
        if (pip == rhs.pip)
            return true;

        ASSERT(pip.getPointer() != rhs.pip.getPointer());
        return false;
    }

    bool operator!=(const NodeRef& rhs) const { return !(*this == rhs); }

private:
    PointerIntPair<void*, Log2CacheLine, Log2CacheLine> pip;
};

// Leaf nodes store the actual elements. The keys array contains the
// actual inserted intervals, sorted in order by their start values
// (and then their end values if equal start values). The values array is
// whatever value those entries map to, as given by the insert() call.
template<typename TKey, typename TValue, uint32_t Capacity>
struct LeafNode : public NodeBase<interval<TKey>, TValue, Capacity> {
    const interval<TKey>& keyAt(uint32_t i) const { return this->first[i]; }
    const TValue& valueAt(uint32_t i) const { return this->second[i]; }
    TValue& valueAt(uint32_t i) { return this->second[i]; }

    uint32_t findFrom(uint32_t i, uint32_t size, const interval<TKey>& key) const {
        ASSERT(i <= size && size <= Capacity);
        ASSERT(i == 0 || keyAt(i - 1) < key);
        while (i != size && keyAt(i) < key)
            i++;
        return i;
    }

    // Same as findFrom except that we don't need the size because we know it's
    // safe to call this on this particular branch and we'll always find a slot
    // before hitting the end of the child array.
    uint32_t safeFind(uint32_t i, const interval<TKey>& key) const {
        ASSERT(i < Capacity);
        ASSERT(i == 0 || keyAt(i - 1) < key);
        while (keyAt(i) < key)
            i++;

        ASSERT(i < Capacity);
        return i;
    }

    uint32_t insertFrom(uint32_t i, uint32_t size, const interval<TKey>& key, const TValue& value);
};

// Branch nodes store references to subtree nodes, all of the same height.
template<typename TKey, uint32_t Capacity>
struct BranchNode : public NodeBase<NodeRef, interval<TKey>, Capacity> {
    const interval<TKey>& keyAt(uint32_t i) const { return this->second[i]; }
    interval<TKey>& keyAt(uint32_t i) { return this->second[i]; }

    const NodeRef& childAt(uint32_t i) const { return this->first[i]; }
    NodeRef& childAt(uint32_t i) { return this->first[i]; }

    uint32_t findFrom(uint32_t i, uint32_t size, const interval<TKey>& key) const {
        ASSERT(i <= size && size <= Capacity);
        ASSERT(i == 0 || keyAt(i - 1) < key);
        while (i != size && keyAt(i) < key)
            i++;
        return i;
    }

    // Same as findFrom except that we don't need the size because we know it's
    // safe to call this on this particular branch and we'll always find a slot
    // before hitting the end of the child array.
    uint32_t safeFind(uint32_t i, const interval<TKey>& key) const {
        ASSERT(i < Capacity);
        ASSERT(i == 0 || keyAt(i - 1) < key);
        while (keyAt(i) < key)
            i++;

        ASSERT(i < Capacity);
        return i;
    }
};

// Represents a position in the b+ tree and a path to get there from the root.
struct Path {
    Path() = default;

    bool valid() const { return !path.empty() && path.front().offset < path.front().size; }

    template<typename T>
    T& node(uint32_t level) const {
        return *reinterpret_cast<T*>(path[level].node);
    }

    template<typename T>
    T& leaf() const {
        return *reinterpret_cast<T*>(path.back().node);
    }

    uint32_t leafSize() const { return path.back().size; }
    uint32_t leafOffset() const { return path.back().offset; }
    uint32_t& leafOffset() { return path.back().offset; }

    uint32_t size(uint32_t level) const { return path[level].size; }
    uint32_t offset(uint32_t level) const { return path[level].offset; }
    uint32_t& offset(uint32_t level) { return path[level].offset; }

    uint32_t height() const {
        ASSERT(valid());
        return uint32_t(path.size() - 1);
    }

    // Gets the subtree referenced at the given level.
    NodeRef& childAt(uint32_t level) const { return path[level].childAt(path[level].offset); }

    // Clear the path and set a new root node.
    void setRoot(void* node, uint32_t size, uint32_t offset) {
        path.clear();
        path.emplace_back(node, size, offset);
    }

    // Update the size of the node at the given level.
    void setSize(uint32_t level, uint32_t size) {
        path[level].size = size;
        if (level)
            childAt(level - 1).setSize(size);
    }

    // Grow path to target height by taking leftmost branches.
    void fillLeft(uint32_t targetHeight) {
        while (height() < targetHeight)
            push(childAt(height()), 0);
    }

    // Replace the current root of the path without changing the rest of it.
    void replaceRoot(void* node, uint32_t size, IndexPair offset);

    void moveLeft(uint32_t level);
    void moveRight(uint32_t level);

    void push(NodeRef node, uint32_t offset) { path.emplace_back(node, offset); }

    // Makes sure the current path is prepared for insertion at the given level.
    // This is always true except when path is at the end (i.e. not valid()) and
    // we fix that by moving back to the last node in the level.
    void legalizeForInsert(uint32_t level) {
        if (valid())
            return;

        moveLeft(level);
        ++path[level].offset;
    }

private:
    struct Entry {
        void* node;
        uint32_t size;
        uint32_t offset;

        Entry(void* node, uint32_t size, uint32_t offset) :
            node(node), size(size), offset(offset) {}

        Entry(NodeRef node, uint32_t offset) :
            node(&node.childAt(0)), size(node.size()), offset(offset) {}

        NodeRef& childAt(uint32_t i) const { return reinterpret_cast<NodeRef*>(node)[i]; }
    };
    SmallVector<Entry> path;
};

// Computes a new distribution of node elements after an overflow or underflow.
// Reserves space for a new element at @a position, and computes the node that
// will hold that same position after redistributing elements.
//
// newSizes[] will be filled in such that:
//   sum(newSizes) == numElements
//   newSizes[i] <= capacity
//
// The returned index is the node where position will go, so:
//   sum(newSizes[0..idx-1]) <= Position
//   sum(newSizes[0..idx])   >= Position
//
// The last equality, sum(newSizes[0..idx]) == position, can only happen when
// grow is set and newSizes[idx] == capacity-1. The index points to the node
// before the one holding the position element where there is room for an insertion.
IndexPair distribute(uint32_t numNodes, uint32_t numElements, uint32_t capacity, uint32_t* newSizes,
                     uint32_t position, bool grow);

} // namespace IntervalMapDetails

template<typename TKey, typename TValue>
class IntervalMap {
    enum {
        // Aim for 3 cache lines of bytes for each node.
        CacheLineBytes = IntervalMapDetails::CacheLineBytes,
        DesiredNodeBytes = 3 * CacheLineBytes,

        // Compute number of elements from the desired size,
        // but we need at least three elements in each leaf
        // for B+ balancing algorithms to work.
        DesiredLeafSize = DesiredNodeBytes / (2 * sizeof(TKey) + sizeof(TValue)),
        MinLeafSize = 3,

        // Typical size for 4-byte key types and 8-byte value types:
        // 64*3/(8+8) = 12 entries per leaf node
        LeafSize = DesiredLeafSize > MinLeafSize ? DesiredLeafSize : MinLeafSize
    };
    using Leaf = IntervalMapDetails::LeafNode<TKey, TValue, LeafSize>;

    enum {
        // Round up allocation size to a full cache line.
        AllocBytes = (sizeof(Leaf) + CacheLineBytes - 1) & ~(CacheLineBytes - 1),

        // For typical size (4-byte key) this will be the same as the number of
        // leaf entries, i.e. 12 children per branch node.
        BranchSize = AllocBytes / (2 * sizeof(TKey) + sizeof(void*))
    };
    using Branch = IntervalMapDetails::BranchNode<TKey, BranchSize>;

public:
    using Allocator = PoolAllocator<char, AllocBytes, CacheLineBytes>;
    class iterator;
    class const_iterator;
    class overlap_iterator;

    /// Default constructor.
    IntervalMap() {}

    /// Destructor.
    ~IntervalMap() = default;

    /// Not copyable.
    IntervalMap(const IntervalMap&) = delete;
    /// Not movable.
    IntervalMap(IntervalMap&&) = delete;

    /// Not copyable.
    IntervalMap& operator=(const IntervalMap&) = delete;
    /// Not movable.
    IntervalMap& operator=(IntervalMap&&) = delete;

    bool empty() const { return rootSize == 0; }

    void insert(TKey left, TKey right, const TValue& value, Allocator& alloc) {
        if (!isFlat() || rootSize == Leaf::Capacity) {
            iterator it(*this);
            it.setToFind(left, right);
            return it.insert(left, right, value, alloc);
        }

        uint32_t i = rootLeaf.findFrom(0, rootSize, {left, right});
        rootSize = rootLeaf.insertFrom(i, rootSize, {left, right}, value);
    }

    iterator begin() {
        iterator i(*this);
        i.setToBegin();
        return i;
    }

    const_iterator begin() const {
        const_iterator i(*this);
        i.setToBegin();
        return i;
    }

    iterator end() {
        iterator i(*this);
        i.setToEnd();
        return i;
    }

    const_iterator end() const {
        const_iterator i(*this);
        i.setToEnd();
        return i;
    }

    overlap_iterator find(TKey left, TKey right) const;

private:
    friend class iterator;
    friend class const_iterator;

    bool isFlat() const { return height == 0; }

    IntervalMapDetails::IndexPair switchToBranch(uint32_t position, Allocator& alloc);

    union {
        Leaf rootLeaf;
        Branch rootBranch;
    };

    uint32_t height = 0;
    uint32_t rootSize = 0;
};

template<typename TKey, typename TValue>
class IntervalMap<TKey, TValue>::const_iterator {
public:
    using iterator_category = std::bidirectional_iterator_tag;
    using difference_type = std::ptrdiff_t;
    using value_type = const TValue;
    using pointer = value_type*;
    using reference = value_type&;

    const_iterator() = default;

    TKey left() const {
        ASSERT(valid());
        return path.leaf<Leaf>().keyAt(path.leafOffset()).left;
    }

    TKey right() const {
        ASSERT(valid());
        return path.leaf<Leaf>().keyAt(path.leafOffset()).right;
    }

    bool valid() const { return path.valid(); }

    const TValue& operator*() const {
        ASSERT(valid());
        return path.leaf<Leaf>().valueAt(path.leafOffset());
    }

    bool operator==(const const_iterator& rhs) const {
        ASSERT(map == rhs.map);
        if (!valid())
            return !rhs.valid();

        if (path.leafOffset() != rhs.path.leafOffset())
            return false;

        return &path.template leaf<Leaf>() == &rhs.path.template leaf<Leaf>();
    }

    bool operator!=(const const_iterator& rhs) const { return !(*this == rhs); }

    const_iterator& operator++() {
        ASSERT(valid());
        if (++path.leafOffset() == path.leafSize() && !isFlat())
            path.moveRight(map->height);
        return *this;
    }

    const_iterator operator++(int) {
        const_iterator tmp(*this);
        ++(*this);
        return tmp;
    }

    const_iterator& operator--() {
        ASSERT(valid());
        if (path.leafOffset())
            --path.leafOffset();
        else
            path.moveLeft(map->height);
        return *this;
    }

    const_iterator operator--(int) {
        const_iterator tmp(*this);
        --(*this);
        return tmp;
    }

protected:
    friend class IntervalMap;

    explicit const_iterator(const IntervalMap& map) : map(const_cast<IntervalMap*>(&map)) {}

    bool isFlat() const {
        ASSERT(map);
        return map->isFlat();
    }

    void setRoot(uint32_t offset) {
        if (isFlat())
            path.setRoot(&map->rootLeaf, map->rootSize, offset);
        else
            path.setRoot(&map->rootBranch, map->rootSize, offset);
    }

    void setToBegin() {
        setRoot(0);
        if (!isFlat())
            path.fillLeft(map->height);
    }

    void setToEnd() { setRoot(map->rootSize); }

    void setToFind(TKey left, TKey right) {
        if (!isFlat())
            treeFind(left, right);
        else
            setRoot(map->rootLeaf.findFrom(0, map->rootSize, {left, right}));
    }

    void treeFind(TKey left, TKey right);

    IntervalMap* map = nullptr;
    IntervalMapDetails::Path path;
};

template<typename TKey, typename TValue>
class IntervalMap<TKey, TValue>::iterator : public const_iterator {
public:
    using value_type = TValue;
    using pointer = value_type*;
    using reference = value_type&;

    iterator() = default;

    TValue& operator*() {
        ASSERT(this->valid());
        return this->path.template leaf<Leaf>().valueAt(this->path.leafOffset());
    }

    iterator& operator++() {
        const_iterator::operator++();
        return *this;
    }

    iterator operator++(int) {
        iterator tmp(*this);
        ++(*this);
        return tmp;
    }

    iterator& operator--() {
        const_iterator::operator--();
        return *this;
    }

    iterator operator--(int) {
        iterator tmp(*this);
        --(*this);
        return tmp;
    }

private:
    friend class IntervalMap;

    iterator(IntervalMap& map) : const_iterator(map) {}

    void insert(TKey left, TKey right, const TValue& value, Allocator& alloc) {
        auto& map = *this->map;
        auto& path = this->path;

        if (this->isFlat()) {
            ASSERT(map.rootSize == Leaf::Capacity);

            auto offset = map.switchToBranch(path.leafOffset(), alloc);
            path.replaceRoot(&map.rootBranch, map.rootSize, offset);
        }

        treeInsert(left, right, value, alloc);
    }

    void treeInsert(TKey left, TKey right, const TValue& value, Allocator& alloc);
    void updateParentBounds(uint32_t level, const IntervalMapDetails::interval<TKey>& key);
};

namespace IntervalMapDetails {

template<typename TKey, typename TValue, uint32_t Capacity>
uint32_t LeafNode<TKey, TValue, Capacity>::insertFrom(uint32_t i, uint32_t size,
                                                      const interval<TKey>& key,
                                                      const TValue& value) {
    ASSERT(i <= size && size <= Capacity);
    ASSERT(key.left <= key.right);
    ASSERT(i == 0 || keyAt(i - 1) < key);
    ASSERT(i == size || !(keyAt(i) < key));

    // If we're at capacity we can't insert another element.
    if (i == Capacity)
        return Capacity + 1;

    if (i != size) {
        // We're inserting in the middle -- make sure we have room.
        if (size == Capacity)
            return Capacity + 1;

        this->moveRight(i, i + 1, size);
    }

    this->first[i] = key;
    this->second[i] = value;
    return size + 1;
}

} // namespace IntervalMapDetails

template<typename TKey, typename TValue>
IntervalMapDetails::IndexPair IntervalMap<TKey, TValue>::switchToBranch(uint32_t position,
                                                                        Allocator& alloc) {
    using namespace IntervalMapDetails;

    // Split the root leaf node into two new leaf nodes.
    constexpr uint32_t NumNodes = 2;
    uint32_t sizes[NumNodes];
    IndexPair newOffset = distribute(NumNodes, rootSize, Leaf::Capacity, sizes, position,
                                     /* grow */ true);

    // Construct new nodes.
    uint32_t pos = 0;
    NodeRef nodes[NumNodes];
    for (uint32_t i = 0; i < NumNodes; i++) {
        auto leaf = alloc.emplace<Leaf>();
        uint32_t size = sizes[i];

        leaf->copy(rootLeaf, pos, 0, size);
        nodes[i] = NodeRef(leaf, size);
        pos += size;
    }

    // Destroy the old root leaf and switch it to a branch node.
    rootLeaf.~Leaf();
    height = 1;
    new (&rootBranch) Branch();

    for (uint32_t i = 0; i < NumNodes; i++) {
        // The interval of this new child node is the start of the
        // first child's interval and the end of the last child's interval.
        auto& leaf = nodes[i].template get<Leaf>();
        rootBranch.keyAt(i) = {leaf.keyAt(0).left, leaf.keyAt(sizes[i] - 1).right};
        rootBranch.childAt(i) = nodes[i];
    }

    rootSize = NumNodes;
    return newOffset;
}

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::const_iterator::treeFind(TKey left, TKey right) {
    using namespace IntervalMapDetails;

    interval<TKey> ival{left, right};
    setRoot(map->rootBranch.findFrom(0, map->rootSize, ival));
    if (valid()) {
        auto child = path.childAt(path.height());
        for (uint32_t i = map->height - path.height() - 1; i > 0; i--) {
            uint32_t offset = child.get<Branch>().safeFind(0, ival);
            path.push(child, offset);
            child = child.childAt(offset);
        }

        path.push(child, child.get<Leaf>().safeFind(0, ival));
    }
}

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::iterator::treeInsert(TKey left, TKey right, const TValue& value,
                                                     Allocator& alloc) {
    using namespace IntervalMapDetails;

    interval<TKey> ival{left, right};
    auto& path = this->path;
    if (!path.valid())
        path.legalizeForInsert(this->map->height);

    uint32_t size = path.leafSize();
    size = path.leaf<Leaf>().insertFrom(path.leafOffset(), size, ival, value);

    if (size > Leaf::Capacity) {
        // TODO: Leaf was full, overflow and try again.
    }

    // Update path to match the newly inserted element.
    path.setSize(path.height(), size);
    updateParentBounds(path.height(), ival);
}

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::iterator::updateParentBounds(
    uint32_t level, const IntervalMapDetails::interval<TKey>& key) {
    auto& path = this->path;
    while (--level)
        path.node<Branch>(level).keyAt(path.offset(level)).unionWith(key);
}

} // namespace slang
