#pragma once

// Wrapper around a {pointer, length} pair to an array on the heap.

namespace slang {

template<typename T>
class ArrayRef {
public:
    ArrayRef(std::nullptr_t) :
        ptr(nullptr), length(0) {
    }

    ArrayRef(const T* ptr, uint32_t length) :
        ptr(ptr), length(length) {
    }

    const T* begin() const { return ptr; }
    const T* end() const { return ptr + length; }

    uint32_t count() const { return length; }
    bool empty() const { return length == 0; }

    const T& operator[](uint32_t index) const {
        ASSERT(index < length);
        return ptr[index];
    }

private:
    const T* ptr;
    uint32_t length;
};

}