//------------------------------------------------------------------------------
// SafeIndexedVector.h
// Type-safe indexed container.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <deque>
#include <vector>

namespace slang {

/// SafeIndexedVector - a flat random-access container that uses a strongly
/// typed integer type for indexing, so that clients can store indices
/// without chance of mistaking them for some other value.
///
/// Indices are never invalidated until they are removed from the index, at
/// which point they are placed on a freelist and potentially reused.
///
/// The index uses a vector internally for managing storage and therefore
/// has the same performance characteristics when adding new elements and
/// there are no open slots in the freelist.
///
/// Note that index zero is always reserved as an invalid sentinel value.
/// The Index type must be explicitly convertible to and from size_t.
///
/// T should be default-constructible, and its default constructed state
/// should represent an invalid / empty value.
template<typename T, typename Index>
class SafeIndexedVector {
public:
    SafeIndexedVector() {
        // reserve a slot for the invalid value
        storage.emplace_back();
    }

    Index add(const T& item) {
        if (!freelist.empty()) {
            Index i = freelist.front();
            storage[static_cast<size_t>(i)] = item;
            freelist.pop_front();
            return i;
        }
        storage.push_back(item);
        return static_cast<Index>(storage.size() - 1);
    }

    Index add(T&& item) {
        if (!freelist.empty()) {
            Index i = freelist.front();
            storage[static_cast<size_t>(i)] = std::move(item);
            freelist.pop_front();
            return i;
        }
        storage.push_back(std::move(item));
        return static_cast<Index>(storage.size() - 1);
    }

    template<typename... Args>
    Index emplace(Args&&... args) {
        if (!freelist.empty()) {
            Index i = freelist.front();
            storage[static_cast<size_t>(i)] = T(std::forward<Args>(args)...);
            freelist.pop_front();
            return i;
        }
        storage.emplace_back(std::forward<Args>(args)...);
        return static_cast<Index>(storage.size() - 1);
    }

    void remove(Index index) {
        storage[static_cast<size_t>(index)] = T();
        freelist.push_back(index);
    }

    void clear() {
        storage.clear();
        freelist.clear();
        storage.emplace_back();
    }

    size_t size() const {
        return storage.size() - freelist.size() - 1;
    }

    const T& operator[](Index index) const {
        return storage[static_cast<size_t>(index)];
    }

    T& operator[](Index index) {
        return storage[static_cast<size_t>(index)];
    }

private:
    std::vector<T> storage;
    std::deque<Index> freelist;
};

}