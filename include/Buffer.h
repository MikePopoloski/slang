//------------------------------------------------------------------------------
// Buffer.h
// Implements fast resizable buffer template.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include <cstdlib>
#include <cstring>
#include <iterator>

#include "BumpAllocator.h"
#include "ArrayRef.h"

namespace slang {

/// Buffer<T> - A fast growable array.
///
/// In the name of performance and simplicity, we avoid adding lots of junk
/// that comes with std::vector, such as exception safety, inserting in the
/// middle, copy constructors, etc.
template<typename T>
class Buffer {
public:
    explicit Buffer(uint32_t capacity = 16) :
        len(0), capacity(capacity)
    {
        data = (T*)malloc(capacity * sizeof(T));
    }

    Buffer(Buffer&& other) :
        data(other.data), len(other.len), capacity(other.capacity)
    {
        other.data = nullptr;
        other.len = 0;
        other.capacity = 0;
    }

    ~Buffer() {
        cleanup();
    }

    // not copyable
    Buffer(const Buffer&) = delete;
    Buffer& operator=(const Buffer&) = delete;

    Buffer& operator=(Buffer&& other) {
        if (this != &other) {
            cleanup();

            data = other.data;
            len = other.len;
            capacity = other.capacity;

            other.data = nullptr;
            other.len = 0;
            other.capacity = 0;
        }
        return *this;
    }

    T* begin() { return data; }
    T* end() { return data + len; }
    const T* begin() const { return data; }
    const T* end() const { return data + len; }
    const T* cbegin() const { return data; }
    const T* cend() const { return data + len; }

    const T& front() const {
        ASSERT(len);
        return data[0];
    }

    const T& back() const {
        ASSERT(len);
        return data[len - 1];
    }

    T& front() {
        ASSERT(len);
        return data[0];
    }

    T& back() {
        ASSERT(len);
        return data[len - 1];
    }

    uint32_t count() const { return len; }
    bool empty() const { return len == 0; }

    /// Clear all elements but retain underlying storage.
    void clear() {
        destructElements();
        len = 0;
    }

    /// Remove the last element from the buffer. Asserts if empty.
    void pop() {
        ASSERT(len);
        len--;
        data[len].~T();
    }

    /// Add an element to the end of the buffer.
    void append(const T& item) {
        amortizeCapacity();
        new (&data[len++]) T(item);
    }

    /// Add a range of elements to the end of the buffer.
    template<typename Container>
    void appendRange(const Container& container) {
        appendRange(std::begin(container), std::end(container));
    }

    /// Add a range of elements to the end of the buffer.
    void appendRange(const T* begin, const T* end) {
        uint32_t count = (uint32_t)(end - begin);
        uint32_t newLen = len + count;
        ensureSize(newLen);

        T* ptr = data + len;
        if (std::is_trivially_copyable<T>())
            memcpy(ptr, begin, count * sizeof(T));
        else {
            while (begin != end)
                new (ptr++) T(*begin++);
        }

        len = newLen;
    }

    /// Construct a new element at the end of the buffer.
    template<typename... Args>
    void emplace(Args&&... args) {
        amortizeCapacity();
        new (&data[len++]) T(std::forward<Args>(args)...);
    }

    /// Adds @a size elements to the buffer (default constructed).
    void extend(uint32_t size) {
        ensureSize(len + size);
        len += size;
    }

    /// Creates a copy of the buffer using the given allocator.
    ArrayRef<T> copy(BumpAllocator& alloc) const {
        if (len == 0)
            return nullptr;

        const T* source = data;
        T* dest = reinterpret_cast<T*>(alloc.allocate(len * sizeof(T)));
        for (uint32_t i = 0; i < len; i++)
            new (&dest[i]) T(*source++);
        return ArrayRef<T>(dest, len);
    }

    T& operator[](int index) { return data[index]; }
    const T& operator[](int index) const { return data[index]; }

private:
    T* data;
    uint32_t len;
    uint32_t capacity;

    void resize() {
        T* newData = (T*)malloc(capacity * sizeof(T));
        if (std::is_trivially_copyable<T>())
            memcpy(newData, data, len * sizeof(T));
        else {
            for (uint32_t i = 0; i < len; i++)
                new (&newData[i]) T(std::move(data[i]));
        }

        cleanup();
        data = newData;
    }

    void amortizeCapacity() {
        if (len == capacity) {
            capacity = (uint32_t)(capacity * 1.5);
            if (capacity == 0)
                capacity = 4;
            resize();
        }
    }

    void ensureSize(uint32_t size) {
        if (size > capacity) {
            capacity = size;
            resize();
        }
    }

    void destructElements() {
        if (!std::is_trivially_destructible<T>()) {
            for (uint32_t i = 0; i < len; i++)
                data[i].~T();
        }
    }

    void cleanup() {
        destructElements();
        free(data);
    }
};

}
