#pragma once

namespace slang {

template<typename T>
class ArrayRef {
public:
    ArrayRef(const T* ptr, uint32_t length)
        : ptr(ptr), length(length) {
    }

    uint32_t Count() const { return length; }

    const T& operator[](uint32_t index) const {
        ASSERT(index < length);
        return ptr[index];
    }

private:
    const T* ptr;
    uint32_t length;
};

}