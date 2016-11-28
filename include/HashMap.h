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
template<typename TKey, typename TValue, typename TDerived>
class HashMapBase {
public:
    uint32_t count() const { return len; }
    bool empty() const { return len == 0; }

    void clear() {
        destructElements();
        len = 0;
    }

    bool add(const TKey& key, const TValue& value) {
        checkResize();

        size_t hash = std::hash<TKey>{}(key);
        Element* slot = findInsertLocation(hash, key);
        if (!slot)
            return false;

        len++;
        new (slot) Element(hash, key, value);
        return true;
    }

    bool add(TKey&& key, TValue&& value) {
        checkResize();

        size_t hash = std::hash<TKey>{}(key);
        Element* slot = findInsertLocation(hash, key);
        if (!slot)
            return false;
        
        len++;
        new (slot) Element(hash, std::move(key), std::move(value));
        return true;
    }

    template<typename U = TValue>
    typename std::enable_if<std::is_pointer<U>::value, const U>::type operator[](const TKey& key) const {
        Element* slot = findSlot(key);
        return slot ? slot->value : nullptr;
    }

    template<typename U = TValue>
    typename std::enable_if<!std::is_pointer<U>::value, const U*>::type operator[](const TKey& key) const {
        Element* slot = findSlot(key);
        return slot ? &slot->value : nullptr;
    }

    template<typename U = TValue>
    typename std::enable_if<std::is_pointer<U>::value, U>::type operator[](const TKey& key) {
        Element* slot = findSlot(key);
        return slot ? slot->value : nullptr;
    }

    template<typename U = TValue>
    typename std::enable_if<!std::is_pointer<U>::value, U*>::type operator[](const TKey& key) {
        Element* slot = findSlot(key);
        return slot ? &slot->value : nullptr;
    }

protected:
    struct Element {
        size_t hash;
        TKey key;
        TValue value;

        Element(size_t hash, const TKey& key, const TValue& value) :
            hash(hash), key(key), value(value) {}

        Element(size_t hash, TKey&& key, TValue&& value) :
            hash(hash), key(std::move(key)), value(std::move(value)) {}
    };

    template<typename TKey, typename TValue, uint32_t N>
    friend class SmallHashMap;

    Element* data;
    uint32_t len = 0;
    uint32_t capacity;

    explicit HashMapBase(uint32_t capacity = 0) : capacity(capacity) {}
    ~HashMapBase() { cleanup(); }

    Element* findSlot(const TKey& key) const {
        size_t hash = std::hash<TKey>{}(key);
        uint32_t index = hash & (capacity - 1);
        int dist = 0;

        while (true) {
            size_t elemHash = data[index].hash;
            if (elemHash == 0)
                return nullptr;
            if (dist > probeDistance(elemHash, index))
                return nullptr;
            if (elemHash == hash && data[index].key == key)
                return data + index;

            index = (index + 1) & (capacity - 1);
            dist++;
        }
    }

    Element* findInsertLocation(size_t hash, const TKey& key) {
        uint32_t index = hash & (capacity - 1);
        int dist = 0;

        // We'll swap elements as we go along to get better lookup characteristics;
        // this is the "robin hood" aspect of the probing strategy. The very first
        // spot we do this gets returned as the final insert location.
        TKey swapKey;
        TValue swapValue;
        Element* result = nullptr;

        while (true) {
            // If the existing element has probed less than us, steal their spot
            // and keep going with the existing element to find a better spot for it.
            // If elemHash is zero, the slot is empty and we can just take it.
            size_t elemHash = data[index].hash;
            int existingDist = probeDistance(elemHash, index);
            if (elemHash == 0 || existingDist < dist) {
                std::swap(hash, data[index].hash);
                std::swap(swapKey, data[index].key);
                std::swap(swapValue, data[index].value);
                dist = existingDist;
                if (!result)
                    result = data + index;

                if (elemHash == 0)
                    return result;
            }
            // Check if the element is already in the table (only on the first insertion)
            else if (!result && elemHash == hash && data[index].key == key)
                return nullptr;

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
        bool isSmall = static_cast<TDerived*>(this)->isSmall();
        Element* oldData = data;
        Element* oldEnd = oldData + capacity;

        capacity *= 2;
        data = (Element*)malloc(capacity * sizeof(Element));
        memset(data, 0, capacity * sizeof(Element));

        // Reinsert old elements; we have a different capacity now so they
        // will probably end up in different spots.
        for (Element* ptr = oldData; ptr != oldEnd; ptr++) {
            if (ptr->hash != 0) {
                Element* slot = findInsertLocation(ptr->hash, ptr->key);
                ASSERT(slot);
                slot->key = std::move(ptr->key);
                slot->value = std::move(ptr->value);
                ptr->~Element();
            }
        }

        if (!isSmall)
            free(oldData);
    }

    void destructElements() {
        if (!std::is_trivially_destructible<TKey>() || !std::is_trivially_destructible<TValue>()) {
            for (uint32_t i = 0; i < len; i++) {
                if (data[i].hash)
                    data[i].~Element();
            }
        }
    }

    void cleanup() {
        destructElements();
        if (!static_cast<TDerived*>(this)->isSmall())
            free(data);
    }
};

template<typename TKey, typename TValue>
class HashMap : public HashMapBase<TKey, TValue, HashMap<TKey, TValue>> {
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

    bool isSmall() const { return false; }
};

template<typename TKey, typename TValue, uint32_t N>
class SmallHashMap : public HashMapBase<TKey, TValue, SmallHashMap<TKey, TValue, N>> {
    static_assert(N >= 1 && isPowerOfTwo(N), "Size must be greater than zero and a power of two");
    static_assert(sizeof(Element) * N < 1024, "Initial size of SmallHashMap is over 1KB");

public:
    SmallHashMap() : HashMapBase(N) {
        this->data = (Element*)stackData;
        memset(this->data, 0, capacity * sizeof(Element));
    }

    template<uint32_t OtherN>
    SmallHashMap(SmallHashMap<TKey, TValue, OtherN>&& other) {
        if (other.isSmall()) {
            this->len = 0;
            this->capacity = sizeof(Element) * N;
            this->data = (Element*)stackData;

            // Copy elements over since we can't steal their local stack pointer
            for (auto ptr = other.data; ptr != other.data + other.capacity; ptr++) {
                if (ptr->hash != 0) {
                    Element* slot = findInsertLocation(ptr->hash, ptr->key);
                    ASSERT(slot);
                    slot->key = std::move(ptr->key);
                    slot->value = std::move(ptr->value);
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
        if ((void*)this != (void*)&other) {
            cleanup();
            new (this) SmallHashMap(std::move(other));
        }
        return *this;
    }

    bool isSmall() const { return (void*)this->data == (void*)stackData; }

private:
    char stackData[sizeof(Element) * N];
};

}