//------------------------------------------------------------------------------
// HashMap.h
// Fast hash map implementation.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>
#include <functional>
#include <type_traits>

#include "MathUtils.h"

namespace slang {

/// HashMapBase - Base class for hash map implementations
///
/// There are two derivations of this class; one that is a normal heap
/// allocated hash map and another that tries to keep it all on the stack
/// for small numbers of elements before spilling to the heap.
///
/// In both cases we use open addressing with robin hood hashing.
/// As you'll notice this class lacks *many* features since I'm
/// only adding what I need as I need it.
///
template<typename TKey, typename TValue>
class HashMapBase {
public:
    template<typename TElement, bool IsConst>
    class iterator_templ {
    public:
        using difference_type = ptrdiff_t;
        using value_type = typename std::conditional<IsConst, const std::pair<TKey, TValue>, std::pair<TKey, TValue>>::type;
        using pointer = value_type*;
        using reference = value_type&;
        using iterator_category = std::forward_iterator_tag;

        iterator_templ() : ptr(nullptr), end(nullptr) {}
        iterator_templ(TElement* ptr, TElement* end) : ptr(ptr), end(end) { advance(); }

        // Converting ctor from non-const iterator to const iterator. SFINAE'd out
        // for const iterator destinations.
        template<bool IsConstSrc, typename = typename std::enable_if<!IsConstSrc && IsConst>::type>
        iterator_templ(const iterator_templ<TElement, IsConstSrc>& other) : ptr(other.ptr), end(other.end) {}

        iterator_templ& operator++() {
            ++ptr;
            advance();
            return *this;
        }

        iterator_templ operator++(int) {
            iterator_temp result = *this;
            ++(*this);
            return result;
        }

        reference operator*() const { return ptr->pair; }
        pointer operator->() const { return &ptr->pair; }

        bool operator==(const iterator_templ<TElement, true>& other) const { return ptr == other.ptr; }
        bool operator!=(const iterator_templ<TElement, true>& other) const { return ptr != other.ptr; }

    private:
        TElement* ptr;
        TElement* end;

        void advance() {
            while (ptr != end && !ptr->valid)
                ++ptr;
        }
    };

    struct Element;
    using iterator = iterator_templ<Element, false>;
    using const_iterator = iterator_templ<Element, true>;

    iterator begin() { return empty() ? end() : iterator(data, dataEnd()); }
    iterator end() { return iterator(dataEnd(), dataEnd()); }
    const_iterator begin() const { return empty() ? end() : const_iterator(data, dataEnd()); }
    const_iterator end() const { return const_iterator(dataEnd(), dataEnd()); }
    const_iterator cbegin() const { return begin(); }
    const_iterator cend() const { return end(); }
    uint32_t size() const { return len; }
    bool empty() const { return len == 0; }

    void clear() {
        destructElements();
        len = 0;
    }

    template<typename... Args>
    std::pair<iterator, bool> emplace(const TKey& key, Args&&... args) {
        checkResize();
        size_t hash = std::hash<TKey>{}(key);
        auto pair = findOrInsert(hash, key);
        if (!pair.second)
            return std::make_pair(iterator(pair.first, dataEnd()), pair.second);

        new (pair.first) Element(hash, key, std::forward<Args>(args)...);
        return std::make_pair(iterator(pair.first, dataEnd()), pair.second);
    }

    template<typename... Args>
    std::pair<iterator, bool> emplace(TKey&& key, Args&&... args) {
        checkResize();
        size_t hash = std::hash<TKey>{}(key);
        auto pair = findOrInsert(hash, key);
        if (!pair.second)
            return std::make_pair(iterator(pair.first, dataEnd()), pair.second);
        
        new (pair.first) Element(hash, std::move(key), std::forward<Args>(args)...);
        return std::make_pair(iterator(pair.first, dataEnd()), pair.second);
    }

    iterator find(const TKey& key) {
        Element* slot = findSlot(key);
        return slot ? iterator(slot, dataEnd()) : end();
    }

    const_iterator find(const TKey& key) const {
        Element* slot = findSlot(key);
        return slot ? const_iterator(slot, dataEnd()) : end();
    }

    TValue& operator[](const TKey& key) { return emplace(key).first->second; }
    TValue& operator[](TKey&& key) { return emplace(std::move(key)).first->second; }

protected:
    struct Element {
        std::pair<TKey, TValue> pair;
        size_t hash;
        bool valid;

        template<typename... Args>
        Element(size_t hash, const TKey& key, Args&&... args) :
            pair(std::piecewise_construct, std::forward_as_tuple(key), std::forward_as_tuple(std::forward<Args>(args)...)),
            hash(hash),
            valid(true)
        {
        }

        template<typename... Args>
        Element(size_t hash, TKey&& key, Args&&... args) :
            pair(std::piecewise_construct, std::forward_as_tuple(std::move(key)), std::forward_as_tuple(std::forward<Args>(args)...)),
            hash(hash),
            valid(true)
        {
        }
    };

    template<typename TKey, typename TValue, uint32_t N>
    friend class SmallHashMap;

    Element* data;
    uint32_t len = 0;
    uint32_t capacity;
    bool isSmall = false;

    explicit HashMapBase(uint32_t capacity = 0) : capacity(capacity) {}
    ~HashMapBase() { cleanup(); }

    Element* dataEnd() { return data + capacity; }
    const Element* dataEnd() const { return data + capacity; }

    Element* findSlot(const TKey& key) const {
        size_t hash = std::hash<TKey>{}(key);
        uint32_t index = hash & (capacity - 1);
        int dist = 0;

        while (true) {
            size_t elemHash = data[index].hash;
            if (!data[index].valid)
                return nullptr;
            if (dist > probeDistance(elemHash, index))
                return nullptr;
            if (elemHash == hash && data[index].pair.first == key)
                return data + index;

            index = (index + 1) & (capacity - 1);
            dist++;
        }
    }

    std::pair<Element*, bool> findOrInsert(size_t hash, const TKey& key) {
        uint32_t index = hash & (capacity - 1);
        int dist = 0;

        // We'll swap elements as we go along to get better lookup characteristics;
        // this is the "robin hood" aspect of the probing strategy. The very first
        // spot we do this gets returned as the final insert location.
        std::pair<TKey, TValue> swapPair;
        Element* result = nullptr;

        while (true) {
            // If the existing element has probed less than us, steal their spot
            // and keep going with the existing element to find a better spot for it.
            // If elemHash is zero, the slot is empty and we can just take it.
            size_t elemHash = data[index].hash;
            int existingDist = probeDistance(elemHash, index);
            if (!data[index].valid || existingDist < dist) {
                std::swap(hash, data[index].hash);
                std::swap(swapPair, data[index].pair);
                dist = existingDist;
                if (!result)
                    result = data + index;

                if (!data[index].valid) {
                    len++;
                    return std::make_pair(result, true);
                }
            }
            // Check if the element is already in the table (only on the first insertion)
            else if (!result && data[index].valid && elemHash == hash && data[index].pair.first == key)
                return std::make_pair(data + index, false);

            index = (index + 1) & (capacity - 1);
            dist++;
        }
    }

    int probeDistance(size_t hash, uint32_t slotIndex) const {
        return (slotIndex + capacity - (hash & (capacity - 1))) & (capacity - 1);
    }

    void checkResize() {
        // Resize if we get too full; robin hood hashing lets us get pretty
        // high load factors, relative to more traditional methods
        const float loadFactor = 0.9f;
        if (len == (uint32_t)(capacity * loadFactor))
            resize();
    }

    void resize() {
        Element* oldData = data;
        Element* oldEnd = oldData + capacity;

        capacity *= 2;
        data = (Element*)malloc(capacity * sizeof(Element));
        memset(data, 0, capacity * sizeof(Element));

        // Reinsert old elements; we have a different capacity now so they
        // will probably end up in different spots.
        for (Element* ptr = oldData; ptr != oldEnd; ptr++) {
            if (ptr->valid) {
                Element* slot = findOrInsert(ptr->hash, ptr->pair.first).first;
                new (slot) Element(std::move(*ptr));
                ptr->~Element();
            }
        }

        if (!isSmall)
            free(oldData);
        isSmall = false;
    }

    void destructElements() {
        if (!std::is_trivially_destructible<TKey>() || !std::is_trivially_destructible<TValue>()) {
            for (uint32_t i = 0; i < capacity; i++) {
                if (data[i].valid)
                    data[i].~Element();
            }
        }
    }

    void cleanup() {
        destructElements();
        if (!isSmall)
            free(data);
    }
};

template<typename TKey, typename TValue>
class HashMap : public HashMapBase<TKey, TValue> {
public:
    HashMap() : HashMapBase(4) {
        this->data = (Element*)malloc(this->capacity * sizeof(Element));
        memset(this->data, 0, capacity * sizeof(Element));
    }

    HashMap(HashMap&& other) {
        this->data = other.data;
        this->len = other.len;
        this->capacity = other.capacity;

        other.data = nullptr;
        other.len = 0;
        other.capacity = 0;
    }

    // not copyable
    HashMap(const HashMap&) = delete;
    HashMap& operator=(const HashMap&) = delete;

    HashMap& operator=(HashMap&& other) {
        if (this != &other) {
            cleanup();
            new (this) HashMap(other);
        }
        return *this;
    }
};

template<typename TKey, typename TValue, uint32_t N>
class SmallHashMap : public HashMapBase<TKey, TValue> {
    static_assert(N >= 1 && isPowerOfTwo(N), "Size must be greater than zero and a power of two");
    static_assert(sizeof(Element) * N < 1024, "Initial size of SmallHashMap is over 1KB");

public:
    SmallHashMap() : HashMapBase(N) {
        this->isSmall = true;
        this->data = (Element*)stackData;
        memset(this->data, 0, capacity * sizeof(Element));
    }

    template<uint32_t OtherN>
    SmallHashMap(SmallHashMap<TKey, TValue, OtherN>&& other) {
        if (other.isSmall()) {
            this->len = 0;
            this->isSmall = true;
            this->capacity = sizeof(Element) * N;
            this->data = (Element*)stackData;

            // Copy elements over since we can't steal their local stack pointer
            for (auto ptr = other.data; ptr != other.data + other.capacity; ptr++) {
                if (ptr->valid) {
                    Element* slot = findOrInsert(ptr->hash, ptr->pair.first).first;
                    new (slot) Element(std::move(*ptr));
                    ptr->~Element();
                }
            }
        }
        else {
            this->data = (Element*)other.data;
            this->len = other.len;
            this->capacity = other.capacity;
        }

        other.data = nullptr;
        other.len = 0;
        other.capacity = 0;
    }

    // not copyable
    SmallHashMap(const SmallHashMap&) = delete;
    SmallHashMap& operator=(const SmallHashMap&) = delete;

    template<uint32_t OtherN>
    SmallHashMap& operator=(SmallHashMap<TKey, TValue, OtherN>&& other) {
        if (static_cast<HashMapBase*>(this) != static_cast<HashMapBase*>(&other)) {
            cleanup();
            new (this) SmallHashMap(std::move(other));
        }
        return *this;
    }

private:
    char stackData[sizeof(Element) * N];
};

}