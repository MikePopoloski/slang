#pragma once

// Simple resizable buffer that can only be appended and cleared.
// Some caveats:
// - Explicitly doesn't try to be exception safe.
// - Clearing doesn't destruct the entries. 

namespace slang {

template<typename T>
class Buffer {
public:
    explicit Buffer(uint32_t capacity)
        : len(0), capacity(capacity) {
        
        ASSERT(capacity > 0);
        data = (T*)malloc(capacity * sizeof(T));
    }

    ~Buffer() {
        free(data);
    }

    Buffer(const Buffer&) = delete;
    Buffer& operator=(const Buffer&) = delete;

    T* begin() { return data; }
    T* end() { return data + len; }

    const T* cbegin() const { return data; }
    const T* cend() const { return data + len; }

    uint32_t count() const { return len; }
    bool empty() const { return len == 0; }

    void clear() {
        len = 0;
    }

    void append(const T& item) {
        if (len == capacity)
            grow();

        new (&data[len++]) T(item);
    }

    template<typename... Args>
    void emplace(Args&&... args) {
        if (len == capacity)
            grow();

        new (&data[len++]) T(std::forward<Args>(args)...);
    }

private:
    T* data;
    uint32_t len;
    uint32_t capacity;

    void grow() {
        capacity = (uint32_t)(capacity * 1.5);
        T* newData = (T*)malloc(capacity * sizeof(T));
        for (uint32_t i = 0; i < len; i++)
            new (&newData[i]) T(std::move(data[i]));

        delete[] data;
        data = newData;
    }
};

}