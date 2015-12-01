#pragma once

#include "BumpAllocator.h"
#include "ArrayRef.h"

// Simple resizable buffer that can only be appended and cleared.
// It makes no attempt at being exception safe.

namespace slang {

template<typename T>
class Buffer {
public:
    explicit Buffer(uint32_t capacity = 16) :
        len(0), capacity(capacity) {
        
        data = (T*)malloc(capacity * sizeof(T));
    }

    Buffer(Buffer&& other) :
        data(other.data), len(other.len), capacity(other.capacity) {

        other.data = nullptr;
        other.len = 0;
        other.capacity = 0;
    }

    ~Buffer() {
        cleanup();
    }

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
    const T& last() const { return data[len]; } // TODO: assert not empty

    uint32_t count() const { return len; }
    bool empty() const { return len == 0; }

    void clear() {
        destructElements();
        len = 0;
    }

    void pop() {
        ASSERT(len);
        len--;
        data[len].~T();
    }

    void append(const T& item) {
        if (len == capacity) {
            capacity = (uint32_t)(capacity * 1.5);
            resize();
        }

        new (&data[len++]) T(item);
    }

    template<typename Container>
    void appendRange(const Container& container) {
        appendRange(std::begin(container), std::end(container));
    }

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

    template<typename... Args>
    void emplace(Args&&... args) {
        if (len == capacity) {
            capacity = (uint32_t)(capacity * 1.5);
            resize();
        }

        new (&data[len++]) T(std::forward<Args>(args)...);
    }

    void extend(uint32_t size) {
        ensureSize(len + size);
        len += size;
    }

    ArrayRef<T> copy(BumpAllocator& alloc) const {
        if (len == 0)
            return nullptr;

        const T* source = data;
        T* dest = reinterpret_cast<T*>(alloc.allocate(len * sizeof(T)));
        for (uint32_t i = 0; i < len; i++)
            new (&dest[i]) T(*source++);
        return ArrayRef<T>(dest, len);
    }

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