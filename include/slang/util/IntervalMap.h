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

    bool overlapsOrAdjacent(const interval<T>& rhs) const {
        return (right + 1 >= rhs.left) && (rhs.right + 1 >= left);
    }

    bool operator==(const interval<T>& rhs) const = default;
};

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
        SLANG_ASSERT(src + count <= M && dst + count <= N);
        for (uint32_t end = src + count; src != end; src++, dst++) {
            first[dst] = other.first[src];
            second[dst] = other.second[src];
        }
    }

    // Moves child nodes to the left, from [src, src+count) to [dst, dst+count)
    void moveLeft(uint32_t src, uint32_t dst, uint32_t count) {
        SLANG_ASSERT(dst <= src);
        copy(*this, src, dst, count);
    }

    // Moves child nodes to the right, from [src, src+count) to [dst, dst+count)
    void moveRight(uint32_t src, uint32_t dst, uint32_t count) {
        SLANG_ASSERT(src <= dst && dst + count <= Capacity);
        while (count--) {
            first[dst + count] = first[src + count];
            second[dst + count] = second[src + count];
        }
    }

    // Erase elements in the given range.
    void erase(uint32_t start, uint32_t end, uint32_t size) { moveLeft(end, start, size - end); }

    // Transfer (move) elements to left sibling node.
    void transferToLeftSib(uint32_t size, NodeBase& sib, uint32_t sibSize, uint32_t count) {
        sib.copy(*this, 0, sibSize, count);
        erase(0, count, size);
    }

    // Transfer (move) elements to right sibling node.
    void transferToRightSib(uint32_t size, NodeBase& sib, uint32_t sibSize, uint32_t count) {
        sib.moveRight(0, count, sibSize);
        sib.copy(*this, size - count, 0, count);
    }

    // Adjust the number of elements in this node by moving elements to or from
    // a left sibling node.
    int adjustFromLeftSib(uint32_t size, NodeBase& sib, uint32_t sibSize, int toAdd) {
        if (toAdd > 0) {
            // Copy from sibling.
            uint32_t count = std::min(std::min(uint32_t(toAdd), sibSize), Capacity - size);
            sib.transferToRightSib(sibSize, *this, size, count);
            return int(count);
        }
        else {
            // Copy to sibling.
            uint32_t count = std::min(std::min(uint32_t(-toAdd), size), Capacity - sibSize);
            transferToLeftSib(size, sib, sibSize, count);
            return -int(count);
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
    NodeRef(T* node, uint32_t s) : pip(node, s - 1) {
        SLANG_ASSERT(s);
    }

    uint32_t size() const { return pip.getInt() + 1; }

    void setSize(uint32_t s) {
        SLANG_ASSERT(s);
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

private:
    PointerIntPair<void*, Log2CacheLine, Log2CacheLine> pip;
};

// A helper base class to provide common implementations for routines templated
// on the derived type of the node itself.
template<typename TKey, typename TDerived>
struct NodeImpl {
    uint32_t find(uint32_t size, const interval<TKey>& key) const {
        SLANG_ASSERT(size <= TDerived::Capacity);
        auto& self = *static_cast<const TDerived*>(this);
        uint32_t i = 0;
        while (i != size && self.keyAt(i).left < key.left)
            i++;
        return i;
    }

    uint32_t findFirstOverlap(uint32_t i, uint32_t size, const interval<TKey>& key) const {
        SLANG_ASSERT(i <= size);
        SLANG_ASSERT(size <= TDerived::Capacity);
        auto& self = *static_cast<const TDerived*>(this);

        for (; i < size; i++) {
            // Our left values are ordered, so if our right is before the
            // current left then there's no way anything here overlaps.
            auto curr = self.keyAt(i);
            if (curr.left > key.right)
                break;

            if (curr.right >= key.left)
                return i;
        }

        return size;
    }

    uint32_t findUnionLeft(uint32_t i, uint32_t size, const interval<TKey>& key) const {
        SLANG_ASSERT(i <= size);
        SLANG_ASSERT(size <= TDerived::Capacity);
        auto& self = *static_cast<const TDerived*>(this);

        for (; i < size; i++) {
            // If we've found where we would insert this key as a new interval
            // based on its left value, stop and return that.
            auto curr = self.keyAt(i);
            if (curr.left >= key.left)
                return i;

            // Otherwise, if we've found an overlap, return it.
            if (curr.right + 1 >= key.left)
                return i;
        }

        return size;
    }

    bool canUnionRight(uint32_t i, uint32_t size, const interval<TKey>& key) const {
        SLANG_ASSERT(i <= size);
        SLANG_ASSERT(size <= TDerived::Capacity);
        auto& self = *static_cast<const TDerived*>(this);

        // This function is called under the assumption that we've already done
        // a findUnionLeft and so all further keys have left values (and therefore
        // also right values) >= our search key left. Therefore we only need to check
        // one thing, which is whether the very next item overlaps or not.
        return i < size && self.keyAt(i).left <= key.right + 1;
    }

    interval<TKey> getBounds(uint32_t size) const {
        SLANG_ASSERT(size);
        auto& self = *static_cast<const TDerived*>(this);
        auto result = self.keyAt(0);
        for (uint32_t i = 1; i < size; i++)
            result.right = std::max(result.right, self.keyAt(i).right);
        return result;
    }
};

// Leaf nodes store the actual elements. The keys array contains the
// actual inserted intervals, sorted in order by their start values
// (and then their end values if equal start values). The values array is
// whatever value those entries map to, as given by the insert() call.
template<typename TKey, typename TValue, uint32_t Capacity>
struct LeafNode : public NodeBase<interval<TKey>, TValue, Capacity>,
                  public NodeImpl<TKey, LeafNode<TKey, TValue, Capacity>> {
    const interval<TKey>& keyAt(uint32_t i) const { return this->first[i]; }
    interval<TKey>& keyAt(uint32_t i) { return this->first[i]; }

    const TValue& valueAt(uint32_t i) const { return this->second[i]; }
    TValue& valueAt(uint32_t i) { return this->second[i]; }

    uint32_t insertFrom(uint32_t i, uint32_t size, const interval<TKey>& key, const TValue& value);
};

// Branch nodes store references to subtree nodes, all of the same height.
template<typename TKey, uint32_t Capacity>
struct BranchNode : public NodeBase<NodeRef, interval<TKey>, Capacity>,
                    public NodeImpl<TKey, BranchNode<TKey, Capacity>> {
    const interval<TKey>& keyAt(uint32_t i) const { return this->second[i]; }
    interval<TKey>& keyAt(uint32_t i) { return this->second[i]; }

    const NodeRef& childAt(uint32_t i) const { return this->first[i]; }
    NodeRef& childAt(uint32_t i) { return this->first[i]; }

    // Inserts a new node into the branch at the given position.
    void insert(uint32_t i, uint32_t size, NodeRef node, const interval<TKey>& key) {
        SLANG_ASSERT(size < Capacity);
        SLANG_ASSERT(i <= size);

        this->moveRight(i, i + 1, size - i);
        childAt(i) = node;
        keyAt(i) = key;
    }
};

// Represents a position in the b+ tree and a path to get there from the root.
struct SLANG_EXPORT Path {
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

    uint32_t height() const { return uint32_t(path.size() - 1); }

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

    NodeRef getLeftSibling(uint32_t level) const;
    NodeRef getRightSibling(uint32_t level) const;

    void push(NodeRef node, uint32_t offset) { path.emplace_back(node, offset); }
    void pop() { path.pop_back(); }

    // Resets the cached information about the node at the given level after it's
    // been modified by some other operation.
    void reset(uint32_t level) { path[level] = Entry(childAt(level - 1), offset(level)); }

    // Makes sure the current path is prepared for insertion at the given level.
    // This is always true except when path is at the end (i.e. not valid()) and
    // we fix that by moving back to the last node in the level.
    void legalizeForInsert(uint32_t level) {
        if (valid())
            return;

        moveLeft(level);
        ++path[level].offset;
    }

    bool operator==(const Path& rhs) const {
        if (!valid())
            return !rhs.valid();

        if (leafOffset() != rhs.leafOffset())
            return false;

        return path.back().node == rhs.path.back().node;
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
//   sum(newSizes[0..idx-1]) <= position
//   sum(newSizes[0..idx])   >= position
//
SLANG_EXPORT IndexPair distribute(uint32_t numNodes, uint32_t numElements, uint32_t capacity,
                                  uint32_t* newSizes, uint32_t position);

} // namespace IntervalMapDetails

/// @brief A data structure that maps from intervals (closed ranges) to values.
///
/// The first N intervals will be stored inline with the object itself,
/// so no allocations will occur until that space is exhausted. Once it is,
/// the map switches to a B+ tree representation with very small overhead for
/// small key and value objects.
///
/// Overlapping and duplicate intervals are allowed.
///
/// New branches of the B+ tree are allocated via a provided PoolAllocator
/// instance. This allocator is not stored in the map itself, but instead
/// provided on each insert call. This trades off convenience to save
/// space in the map object.
///
/// The memory reserved by the map from the PoolAllocator is not returned
/// in its destructor (IntervalMap has a trivial destructor). This is so
/// it can be used in types that themselves require a trivial destructor.
/// The tradeoff is that the reserved memory is not returnable to the pool
/// once the map is destroyed, and you must dispose of the PoolAllocator
/// itself to free up the memory.
///
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
    using key_type = TKey;
    using value_type = TValue;
    using size_type = size_t;
    using difference_type = ptrdiff_t;
    using allocator_type = PoolAllocator<char, AllocBytes, CacheLineBytes>;

    class iterator;
    class const_iterator;
    class overlap_iterator;

    /// Default constructor.
    IntervalMap() {}

    /// Destructor.
    ~IntervalMap() = default;

    /// Not copyable.
    IntervalMap(const IntervalMap&) = delete;

    /// Not copyable.
    IntervalMap& operator=(const IntervalMap&) = delete;

    /// Move constructor.
    IntervalMap(IntervalMap&& other) noexcept { *this = std::move(other); }

    /// Move assignment operator.
    IntervalMap& operator=(IntervalMap&& other) noexcept {
        if (isFlat())
            rootLeaf.~Leaf();
        else
            rootBranch.~Branch();

        height = other.height;
        rootSize = other.rootSize;

        if (other.isFlat()) {
            rootLeaf = std::move(other.rootLeaf);
        }
        else {
            rootBranch = std::move(other.rootBranch);
            other.rootBranch.~Branch();
            other.height = 0;
            new (&other.rootLeaf) Leaf();
        }

        return *this;
    }

    /// Indicates whether the map is empty.
    bool empty() const { return rootSize == 0; }

    /// Clears the map and returns all allocated memory, if any, to the provided allocator.
    void clear(allocator_type& alloc);

    /// @brief Inserts a new interval and value pair into the map.
    ///
    /// Insertion complexity is O(log n)
    void insert(TKey left, TKey right, const TValue& value, allocator_type& alloc) {
        if (isFlat() && rootSize != Leaf::Capacity) {
            uint32_t i = rootLeaf.find(rootSize, {left, right});
            rootSize = rootLeaf.insertFrom(i, rootSize, {left, right}, value);
        }
        else {
            iterator it(*this);
            it.setToFind(left, right);
            it.insert(left, right, value, alloc);
        }
    }

    /// @brief Inserts a new interval and value pair into the map.
    ///
    /// Insertion complexity is O(log n)
    void insert(const std::pair<TKey, TKey>& key, const TValue& value, allocator_type& alloc) {
        insert(key.first, key.second, value, alloc);
    }

    /// @brief Inserts a new interval and value pair into the map, combining it
    /// with any intervals that already exist in the map that are adjacent to or
    /// overlap with the new one.
    ///
    /// Note that it in the case of combining intervals, the old value associated
    /// with the interval will be kept and the new one ignored. It is assumed that
    /// if you are using this method you don't care much about the values.
    ///
    /// Complexity is O(log n + m) where n is the number of intervals
    /// in the map and m is the number of intervals found to union with.
    void unionWith(TKey left, TKey right, const TValue& value, allocator_type& alloc) {
        overlap_iterator it(*this, left, right);
        it.unionWith(value, alloc);
    }

    /// @brief Inserts a new interval and value pair into the map, combining it
    /// with any intervals that already exist in the map that are adjacent to or
    /// overlap with the new one and share the same value.
    ///
    /// Note that it in the case of combining intervals, the old value associated
    /// with the interval will be kept and the new one ignored. It is assumed that
    /// if you are using this method you don't care much about the values.
    ///
    /// Complexity is O(log n + m) where n is the number of intervals
    /// in the map and m is the number of intervals found to union with.
    void unionWith(const std::pair<TKey, TKey>& key, const TValue& value, allocator_type& alloc) {
        unionWith(key.first, key.second, value, alloc);
    }

    /// Returns an iterator at the start of the map.
    iterator begin() {
        iterator it(*this);
        it.setToBegin();
        return it;
    }

    /// Returns an iterator at the start of the map.
    const_iterator begin() const {
        const_iterator it(*this);
        it.setToBegin();
        return it;
    }

    /// Returns an iterator at the end of the map.
    iterator end() {
        iterator it(*this);
        it.setToEnd();
        return it;
    }

    /// Returns an iterator at the end of the map.
    const_iterator end() const {
        const_iterator it(*this);
        it.setToEnd();
        return it;
    }

    /// @brief Finds all intervals that overlap the given interval.
    ///
    /// The returned iterator can be used to traverse all of the
    /// overlapping intervals.
    ///
    /// The complexity is O(log n + m) where n is the number of intervals
    /// in the map and m is the number of overlapping intervals found.
    overlap_iterator find(TKey left, TKey right) const {
        overlap_iterator it(*this, left, right);
        it.setToBegin();
        return it;
    }

    /// @brief Finds all intervals that overlap the given interval.
    ///
    /// The returned iterator can be used to traverse all of the
    /// overlapping intervals.
    ///
    /// The complexity is O(log n + m) where n is the number of intervals
    /// in the map and m is the number of overlapping intervals found.
    overlap_iterator find(const std::pair<TKey, TKey>& key) const {
        return find(key.first, key.second);
    }

    /// Gets an interval encompassing the entire set of items in the map.
    std::pair<TKey, TKey> getBounds() const {
        SLANG_ASSERT(!empty());
        auto ival = isFlat() ? rootLeaf.getBounds(rootSize) : rootBranch.getBounds(rootSize);
        return {ival.left, ival.right};
    }

    /// Verifies the internal state of the map, ASSERTing if it's not valid.
    /// This is only intended for use with unit tests.
    void verify() const {
        if (isFlat())
            return;

        TKey lastKey = std::numeric_limits<TKey>::min();
        verify(rootBranch, rootSize, 0, lastKey);
    }

private:
    friend class iterator;
    friend class const_iterator;
    friend class overlap_iterator;

    bool isFlat() const { return height == 0; }

    void verify(const Branch& branch, uint32_t size, uint32_t depth, TKey& lastKey) const;

    template<typename TNode, bool SwitchToBranch>
    IntervalMapDetails::IndexPair modifyRoot(TNode& rootNode, uint32_t position,
                                             allocator_type& alloc);

    IntervalMapDetails::IndexPair switchToBranch(uint32_t position, allocator_type& alloc) {
        return modifyRoot<Leaf, true>(rootLeaf, position, alloc);
    }

    IntervalMapDetails::IndexPair splitRoot(uint32_t position, allocator_type& alloc) {
        return modifyRoot<Branch, false>(rootBranch, position, alloc);
    }

    void switchToLeaf() {
        rootBranch.~Branch();
        height = 0;
        new (&rootLeaf) Leaf();
    }

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

    std::pair<TKey, TKey> bounds() const {
        SLANG_ASSERT(valid());
        auto ival = path.leaf<Leaf>().keyAt(path.leafOffset());
        return {ival.left, ival.right};
    }

    bool valid() const { return path.valid(); }

    const TValue& operator*() const {
        SLANG_ASSERT(valid());
        return path.leaf<Leaf>().valueAt(path.leafOffset());
    }

    bool operator==(const const_iterator& rhs) const { return path == rhs.path; }
    bool operator==(const overlap_iterator& rhs) const { return path == rhs.path; }

    const_iterator& operator++() {
        SLANG_ASSERT(valid());
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
        if (path.leafOffset() && (valid() || isFlat()))
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
        SLANG_ASSERT(map);
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
        if (isFlat())
            setRoot(map->rootLeaf.find(map->rootSize, {left, right}));
        else
            treeFind(left, right);
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
        SLANG_ASSERT(this->valid());
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

    void insert(TKey left, TKey right, const TValue& value, allocator_type& alloc);
    bool erase(allocator_type& alloc, bool shouldRecomputeBounds);
    void updateParentBounds(uint32_t level, const IntervalMapDetails::interval<TKey>& key);
    void recomputeBounds(uint32_t level);
    bool insertNode(uint32_t level, IntervalMapDetails::NodeRef node,
                    const IntervalMapDetails::interval<TKey>& key, allocator_type& alloc);
    void eraseNode(uint32_t level, allocator_type& alloc);

    template<typename TNode>
    bool overflow(uint32_t level, allocator_type& alloc);
};

template<typename TKey, typename TValue>
class IntervalMap<TKey, TValue>::overlap_iterator : iterator {
public:
    using iterator_category = std::forward_iterator_tag;
    using difference_type = std::ptrdiff_t;
    using value_type = const TValue;
    using pointer = value_type*;
    using reference = value_type&;

    overlap_iterator() = default;

    using iterator::bounds;
    using iterator::valid;

    const TValue& operator*() const {
        SLANG_ASSERT(valid());
        return this->path.template leaf<Leaf>().valueAt(this->path.leafOffset());
    }

    overlap_iterator& operator++() {
        SLANG_ASSERT(valid());

        uint32_t offset = this->path.leafOffset() + 1;
        offset = this->path.template leaf<Leaf>().findFirstOverlap(offset, this->path.leafSize(),
                                                                   searchKey);

        this->path.leafOffset() = offset;
        if (offset == this->path.leafSize() && !this->isFlat())
            nextOverlap();

        return *this;
    }

    overlap_iterator operator++(int) {
        overlap_iterator tmp(*this);
        ++(*this);
        return tmp;
    }

    bool operator==(const overlap_iterator& rhs) const { return this->path == rhs.path; }
    bool operator==(const const_iterator& rhs) const { return this->path == rhs.path; }

protected:
    friend class IntervalMap;

    overlap_iterator(const IntervalMap& map, TKey left, TKey right) :
        iterator(const_cast<IntervalMap&>(map)), searchKey({left, right}) {}

    void setToBegin() {
        if (this->isFlat()) {
            this->setRoot(this->map->rootLeaf.findFirstOverlap(0, this->map->rootSize, searchKey));
        }
        else {
            this->setRoot(
                this->map->rootBranch.findFirstOverlap(0, this->map->rootSize, searchKey));
            treeFind();
        }
    }

    void unionWith(const TValue& value, allocator_type& alloc);

    void treeFind();
    void treeFindUnion();
    void nextOverlap();

    IntervalMapDetails::interval<TKey> searchKey;
};

namespace IntervalMapDetails {

template<typename TKey, typename TValue, uint32_t Capacity>
uint32_t LeafNode<TKey, TValue, Capacity>::insertFrom(uint32_t i, uint32_t size,
                                                      const interval<TKey>& key,
                                                      const TValue& value) {
    SLANG_ASSERT(i <= size && size <= Capacity);
    SLANG_ASSERT(key.left <= key.right);
    SLANG_ASSERT(i == 0 || keyAt(i - 1).left < key.left);
    SLANG_ASSERT(i == size || !(keyAt(i).left < key.left));

    // If we're at capacity we can't insert another element.
    if (i == Capacity)
        return Capacity + 1;

    if (i != size) {
        // We're inserting in the middle -- make sure we have room.
        if (size == Capacity)
            return Capacity + 1;

        this->moveRight(i, i + 1, size - i);
    }

    this->first[i] = key;
    this->second[i] = value;
    return size + 1;
}

} // namespace IntervalMapDetails

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::clear(allocator_type& alloc) {
    using namespace IntervalMapDetails;
    if (!isFlat()) {
        // Collect level 0 nodes from the root.
        SmallVector<NodeRef> refs, nextRefs;
        for (uint32_t i = 0; i < rootSize; i++)
            refs.push_back(rootBranch.childAt(i));

        // Visit all branch nodes.
        for (uint32_t h = height - 1; h > 0; h--) {
            for (size_t i = 0, e = refs.size(); i != e; i++) {
                for (size_t j = 0, s = refs[i].size(); j != s; j++)
                    nextRefs.push_back(refs[i].childAt(uint32_t(j)));

                alloc.destroy(&refs[i].get<Branch>());
            }

            refs.clear();
            refs.swap(nextRefs);
        }

        // Visit all leaf nodes.
        for (size_t i = 0, e = refs.size(); i != e; i++)
            alloc.destroy(&refs[i].get<Leaf>());

        switchToLeaf();
    }
    rootSize = 0;
}

template<typename TKey, typename TValue>
template<typename TNode, bool SwitchToBranch>
IntervalMapDetails::IndexPair IntervalMap<TKey, TValue>::modifyRoot(TNode& rootNode,
                                                                    uint32_t position,
                                                                    allocator_type& alloc) {
    using namespace IntervalMapDetails;

    // Split the root branch node into two new nodes.
    constexpr uint32_t NumNodes = 2;
    uint32_t sizes[NumNodes];
    IndexPair newOffset = distribute(NumNodes, rootSize, Leaf::Capacity, sizes, position);

    // Construct new nodes.
    uint32_t pos = 0;
    NodeRef nodes[NumNodes];
    for (uint32_t i = 0; i < NumNodes; i++) {
        auto newNode = alloc.template emplace<TNode>();
        uint32_t size = sizes[i];

        newNode->copy(rootNode, pos, 0, size);
        nodes[i] = NodeRef(newNode, size);
        pos += size;
    }

    if (SwitchToBranch) {
        // Destroy the old root leaf and switch it to a branch node.
        rootLeaf.~Leaf();
        new (&rootBranch) Branch();
    }

    for (uint32_t i = 0; i < NumNodes; i++) {
        rootBranch.keyAt(i) = nodes[i].template get<TNode>().getBounds(sizes[i]);
        rootBranch.childAt(i) = nodes[i];
    }

    rootSize = NumNodes;
    height++;
    return newOffset;
}

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::verify(const Branch& branch, uint32_t size, uint32_t depth,
                                       TKey& lastKey) const {
    for (uint32_t i = 0; i < size; i++) {
        auto child = branch.childAt(i);
        auto key = branch.keyAt(i);

        SLANG_ASSERT(key.left >= lastKey);
        lastKey = key.left;

        if (depth == height - 1) {
            auto bounds = child.template get<Leaf>().getBounds(child.size());
            SLANG_ASSERT(bounds == key);
        }
        else {
            auto& childBranch = child.template get<Branch>();
            auto bounds = childBranch.getBounds(child.size());
            SLANG_ASSERT(bounds == key);

            verify(childBranch, child.size(), depth + 1, lastKey);
        }
    }
}

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::const_iterator::treeFind(TKey left, TKey right) {
    using namespace IntervalMapDetails;

    interval<TKey> ival{left, right};
    uint32_t offset = map->rootBranch.find(map->rootSize, ival);
    if (offset)
        offset--;
    setRoot(offset);

    if (valid()) {
        auto child = path.childAt(path.height());
        for (uint32_t i = map->height - path.height() - 1; i > 0; i--) {
            offset = child.template get<Branch>().find(child.size(), ival);
            if (offset)
                offset--;
            path.push(child, offset);
            child = child.childAt(offset);
        }

        path.push(child, child.template get<Leaf>().find(child.size(), ival));
    }
}

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::iterator::insert(TKey left, TKey right, const TValue& value,
                                                 allocator_type& alloc) {
    using namespace IntervalMapDetails;

    auto& map = *this->map;
    auto& path = this->path;

    interval<TKey> ival{left, right};
    if (this->isFlat()) {
        // Try simple root leaf insert first.
        uint32_t size = map.rootLeaf.insertFrom(path.leafOffset(), map.rootSize, ival, value);
        if (size <= Leaf::Capacity) {
            map.rootSize = size;
            path.setSize(0, size);
            return;
        }

        // Root is full, we need to branch.
        auto offset = map.switchToBranch(path.leafOffset(), alloc);
        path.replaceRoot(&map.rootBranch, map.rootSize, offset);
    }

    if (!path.valid())
        path.legalizeForInsert(this->map->height);

    uint32_t size = path.leafSize();
    size = path.template leaf<Leaf>().insertFrom(path.leafOffset(), size, ival, value);

    if (size > Leaf::Capacity) {
        // If the new element didn't fit, overflow the node and try again.
        overflow<Leaf>(path.height(), alloc);
        size = path.template leaf<Leaf>().insertFrom(path.leafOffset(), path.leafSize(), ival,
                                                     value);
    }

    // Update path to match the newly inserted element.
    path.setSize(path.height(), size);
    updateParentBounds(path.height(), ival);
}

template<typename TKey, typename TValue>
bool IntervalMap<TKey, TValue>::iterator::erase(allocator_type& alloc, bool shouldRecomputeBounds) {
    auto& map = *this->map;
    auto& path = this->path;
    SLANG_ASSERT(this->valid());

    uint32_t offset = path.leafOffset();
    if (this->isFlat()) {
        map.rootLeaf.erase(offset, offset + 1, map.rootSize);
        path.setSize(0, --map.rootSize);
        return false;
    }

    // Nodes are not allowed to become empty, so erase the node itself
    // if that were to be the case.
    auto& node = path.template leaf<Leaf>();
    if (path.leafSize() == 1) {
        alloc.destroy(&node);
        eraseNode(map.height, alloc);
        return true;
    }

    // Otherwise just erase the current entry.
    node.erase(offset, offset + 1, path.leafSize());
    path.setSize(map.height, path.leafSize() - 1);

    if (shouldRecomputeBounds)
        recomputeBounds(map.height);

    return false;
}

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::iterator::updateParentBounds(
    uint32_t level, const IntervalMapDetails::interval<TKey>& key) {
    auto& path = this->path;
    while (level) {
        --level;
        path.template node<Branch>(level).keyAt(path.offset(level)).unionWith(key);
    }
}

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::iterator::recomputeBounds(uint32_t level) {
    auto& path = this->path;
    while (level) {
        --level;
        auto& branch = path.template node<Branch>(level);
        auto offset = path.offset(level);
        auto child = branch.childAt(offset);
        auto bounds = (level == path.height() - 1)
                          ? child.template get<Leaf>().getBounds(child.size())
                          : child.template get<Branch>().getBounds(child.size());
        branch.keyAt(offset) = bounds;
    }
}

template<typename TKey, typename TValue>
template<typename TNode>
bool IntervalMap<TKey, TValue>::iterator::overflow(uint32_t level, allocator_type& alloc) {
    SLANG_ASSERT(level > 0);
    using namespace IntervalMapDetails;

    auto& path = this->path;
    uint32_t offset = path.offset(level);
    uint32_t numElems = 0;
    uint32_t numNodes = 0;
    TNode* nodes[4];
    uint32_t curSizes[4];

    // Handle left sibling, if it exists.
    NodeRef leftSib = path.getLeftSibling(level);
    if (leftSib) {
        numElems = curSizes[0] = leftSib.size();
        offset += numElems;
        nodes[numNodes++] = &leftSib.get<TNode>();
    }

    // Handle the current node.
    numElems += curSizes[numNodes] = path.size(level);
    nodes[numNodes++] = &path.template node<TNode>(level);

    // Handle right sibling, if it exists.
    NodeRef rightSib = path.getRightSibling(level);
    if (rightSib) {
        numElems += curSizes[numNodes] = rightSib.size();
        nodes[numNodes++] = &rightSib.get<TNode>();
    }

    // Check if we need to allocate a new node.
    uint32_t newNode = 0;
    if (numElems + 1 > numNodes * TNode::Capacity) {
        // Insert new node at the penultimate position, or after a single node if only one.
        newNode = numNodes == 1 ? 1 : numNodes - 1;
        curSizes[numNodes] = curSizes[newNode];
        nodes[numNodes] = nodes[newNode];
        curSizes[newNode] = 0;
        nodes[newNode] = alloc.template emplace<TNode>();
        numNodes++;
    }

    // Redistribute elements among the nodes.
    uint32_t newSizes[4];
    IndexPair newOffset = distribute(numNodes, numElems, TNode::Capacity, newSizes, offset);

    // Move elements right.
    for (uint32_t n = numNodes - 1; n; --n) {
        if (curSizes[n] == newSizes[n])
            continue;

        for (int m = int(n - 1); m != -1; --m) {
            int delta = nodes[n]->adjustFromLeftSib(curSizes[n], *nodes[m], curSizes[m],
                                                    int(newSizes[n]) - int(curSizes[n]));
            curSizes[m] = uint32_t(int(curSizes[m]) - delta);
            curSizes[n] = uint32_t(int(curSizes[n]) + delta);

            // If the current node was exhausted we can bail out.
            if (curSizes[n] >= newSizes[n])
                break;
        }
    }

    // Move elements left.
    for (uint32_t n = 0; n < numNodes - 1; n++) {
        if (curSizes[n] == newSizes[n])
            continue;

        for (uint32_t m = n + 1; m < numNodes; m++) {
            int delta = nodes[m]->adjustFromLeftSib(curSizes[m], *nodes[n], curSizes[n],
                                                    int(curSizes[n]) - int(newSizes[n]));
            curSizes[m] = uint32_t(int(curSizes[m]) + delta);
            curSizes[n] = uint32_t(int(curSizes[n]) - delta);

            // If the current node was exhausted we can bail out.
            if (curSizes[n] >= newSizes[n])
                break;
        }
    }

    // Move the path to the leftmost node.
    if (leftSib)
        path.moveLeft(level);

    // Elements have been moved, update node sizes and interval bounds.
    bool split = false;
    uint32_t pos = 0;
    while (true) {
        if (newNode && pos == newNode) {
            // Actually insert the new node that we created earlier.
            auto ival = nodes[pos]->getBounds(newSizes[pos]);
            split = insertNode(level, NodeRef(nodes[pos], newSizes[pos]), ival, alloc);
            if (split)
                level++;
        }
        else {
            // Otherwise just update the size and bounds.
            path.setSize(level, newSizes[pos]);
            recomputeBounds(level);
        }

        if (pos + 1 == numNodes)
            break;

        path.moveRight(level);
        ++pos;
    }

    // Move our path to the new offset of the element we used to be pointing at.
    while (pos != newOffset.first) {
        path.moveLeft(level);
        --pos;
    }

    path.offset(level) = newOffset.second;
    return split;
}

template<typename TKey, typename TValue>
bool IntervalMap<TKey, TValue>::iterator::insertNode(uint32_t level,
                                                     IntervalMapDetails::NodeRef node,
                                                     const IntervalMapDetails::interval<TKey>& key,
                                                     allocator_type& alloc) {
    SLANG_ASSERT(level > 0);

    bool split = false;
    auto& map = *this->map;
    auto& path = this->path;

    if (level == 1) {
        // Insert into the root branch node.
        if (map.rootSize < Branch::Capacity) {
            map.rootBranch.insert(path.offset(0), map.rootSize, node, key);
            path.setSize(0, ++map.rootSize);
            path.reset(level);
            return false;
        }

        // We need to split the root while keeping our position.
        split = true;
        auto newOffset = map.splitRoot(path.offset(0), alloc);
        path.replaceRoot(&map.rootBranch, map.rootSize, newOffset);

        // Fall through to insert at the new higher level.
        level++;
    }

    // When inserting before end, make sure we have a valid path.
    path.legalizeForInsert(--level);

    if (path.size(level) == Branch::Capacity) {
        // Branch node is full, we need to split it.
        SLANG_ASSERT(!split);
        split = overflow<Branch>(level, alloc);
        if (split)
            level++;
    }

    // Actually insert into the branch node.
    path.template node<Branch>(level).insert(path.offset(level), path.size(level), node, key);
    path.setSize(level, path.size(level) + 1);
    updateParentBounds(level, key);

    path.reset(level + 1);
    return split;
}

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::iterator::eraseNode(uint32_t level, allocator_type& alloc) {
    SLANG_ASSERT(level > 0);
    auto& map = *this->map;
    auto& path = this->path;

    if (--level == 0) {
        uint32_t offset = path.offset(0);
        map.rootBranch.erase(offset, offset + 1, map.rootSize);
        path.setSize(0, --map.rootSize);
        if (map.empty()) {
            map.switchToLeaf();
            this->setRoot(0);
            return;
        }
    }
    else {
        auto& parent = path.template node<Branch>(level);
        if (path.size(level) == 1) {
            // Branch node became empty, remove it recursively.
            alloc.destroy(&parent);
            eraseNode(level, alloc);
        }
        else {
            // N.B. see note about updating parent bounds in erase()
            uint32_t offset = path.offset(level);
            uint32_t size = path.size(level);
            parent.erase(offset, offset + 1, size);
            path.setSize(level, size - 1);
            recomputeBounds(level);
        }
    }

    if (path.valid()) {
        path.reset(level + 1);
        path.offset(level + 1) = 0;
    }
}

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::overlap_iterator::treeFind() {
    if (!valid())
        return;

    auto& path = this->path;
    auto child = path.childAt(path.height());
    for (uint32_t i = this->map->height - path.height() - 1; i > 0; i--) {
        uint32_t size = child.size();
        uint32_t offset = child.template get<Branch>().findFirstOverlap(0, size, searchKey);
        if (offset == size) {
            this->setToEnd();
            return;
        }

        path.push(child, offset);
        child = child.childAt(offset);
    }

    uint32_t size = child.size();
    uint32_t offset = child.template get<Leaf>().findFirstOverlap(0, size, searchKey);
    if (offset == size) {
        this->setToEnd();
        return;
    }

    path.push(child, offset);
}

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::overlap_iterator::treeFindUnion() {
    if (!valid())
        return;

    auto& path = this->path;
    auto child = path.childAt(path.height());
    for (uint32_t i = this->map->height - path.height() - 1; i > 0; i--) {
        uint32_t size = child.size();
        uint32_t offset = child.template get<Branch>().findUnionLeft(0, size, searchKey);
        if (offset == size) {
            this->setToEnd();
            return;
        }

        path.push(child, offset);
        child = child.childAt(offset);
    }

    uint32_t size = child.size();
    uint32_t offset = child.template get<Leaf>().findUnionLeft(0, size, searchKey);
    if (offset == size) {
        this->setToEnd();
        return;
    }

    path.push(child, offset);
}

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::overlap_iterator::nextOverlap() {
    auto& path = this->path;
    SLANG_ASSERT(path.leafOffset() == path.leafSize());
    SLANG_ASSERT(valid());

    // Pop up a level and try to move forward. Keep going until we
    // find a new branch that overlaps our target key.
    uint32_t l = path.height();
    while (path.height()) {
        path.pop();
        --l;

        uint32_t& offset = path.leafOffset();
        uint32_t size = path.leafSize();
        if (offset < size - 1) {
            offset = path.template node<Branch>(l).findFirstOverlap(offset + 1, size, searchKey);
            if (offset != size) {
                // Descend back down to the next overlapping leaf node from our current position.
                treeFind();
                return;
            }
        }
    }

    // If we hit this point we ran out places to look. We should be right
    // before the last node in the root branch so bump our offset by one
    // to make the path point to the end of the tree.
    SLANG_ASSERT(path.height() == 0);
    path.leafOffset()++;
}

template<typename TKey, typename TValue>
void IntervalMap<TKey, TValue>::overlap_iterator::unionWith(const TValue& value,
                                                            allocator_type& alloc) {
    using namespace IntervalMapDetails;

    auto& map = *this->map;
    auto& path = this->path;
    if (this->isFlat()) {
        this->setRoot(map.rootLeaf.findUnionLeft(0, map.rootSize, searchKey));
    }
    else {
        this->setRoot(map.rootBranch.findUnionLeft(0, map.rootSize, searchKey));
        treeFindUnion();
    }

    // The iterator now points to one of the following:
    // - The first existing interval that overlaps (or is adjacent to) the search key
    // - The correct place to insert the search key as a new interval
    // - The end of the map (also the correct place to insert)
    if (!valid()) {
        // We're at the end of the map so just insert and we're done.
        this->insert(searchKey.left, searchKey.right, value, alloc);
        return;
    }

    auto updateCurrKey = [&](interval<TKey> newKey) {
        // Expand the current entry to match our new item.
        interval<TKey>& currKey = path.template leaf<Leaf>().keyAt(path.leafOffset());
        currKey.unionWith(newKey);
        searchKey = currKey;
    };

    if (!path.template leaf<Leaf>().keyAt(path.leafOffset()).overlapsOrAdjacent(searchKey)) {
        this->insert(searchKey.left, searchKey.right, value, alloc);
    }
    else {
        // Otherwise expand the current entry to match our new item.
        updateCurrKey(searchKey);
        this->updateParentBounds(path.height(), searchKey);
    }

    // Our new interval is inserted or updated. Continue forward and
    // merge all later intervals that overlap with this one.
    while (true) {
        auto& leaf = path.template leaf<Leaf>();
        uint32_t offset = path.leafOffset() + 1;
        if (leaf.canUnionRight(offset, path.leafSize(), searchKey)) {
            // This does not change our parent bounds so no need to update.
            updateCurrKey(leaf.keyAt(offset));

            path.leafOffset() = offset;
            bool modifiedPath = this->erase(alloc, false);
            SLANG_ASSERT(!modifiedPath);

            path.leafOffset()--;
        }
        else if (offset == path.leafSize() && !this->isFlat()) {
            // Copy our iterator and advance to the next node to see if we can merge
            // with it. This intentionally slices the object since we don't need the
            // wider overlapped_iterator here.
            iterator nextIt = *this;
            nextIt.path.moveRight(map.height);
            if (!nextIt.valid() || !nextIt.path.template leaf<Leaf>().canUnionRight(
                                       0, nextIt.path.leafSize(), searchKey)) {
                // Nope, we're done.
                return;
            }

            // Merge and erase the next elem.
            updateCurrKey(nextIt.path.template leaf<Leaf>().keyAt(0));
            this->updateParentBounds(path.height(), searchKey);

            if (nextIt.erase(alloc, true)) {
                // The erase operation deleted nodes so our path is invalid.
                // Get back to a good state by copying from the nextIt's path
                // and then moving back left.
                path = nextIt.path;
                path.moveLeft(map.height);
            }
        }
        else {
            return;
        }
    }
}

} // namespace slang
