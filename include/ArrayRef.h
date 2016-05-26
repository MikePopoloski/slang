//------------------------------------------------------------------------------
// ArrayRef.h
// Implements array reference utility template.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>
#include <cstddef>

#include "Debug.h"

namespace slang {

/// ArrayRef<T> - Lightweight reference to array
///
/// Contains a simple pointer,length pair that is cheap to copy around.
/// Note that ArrayRef is immutable.
template<typename T>
class ArrayRef {
public:
    ArrayRef() {}
    ArrayRef(std::nullptr_t) {}

    ArrayRef(const T* ptr, uint32_t length) :
        ptr(ptr), len(length)
    {
    }

    ArrayRef(const T* begin, const T* end) :
        ptr(ptr), len(end - begin)
    {
    }

    const T* begin() const { return ptr; }
    const T* end() const { return ptr + len; }
    const T* cbegin() const { return ptr; }
    const T* cend() const { return ptr + len; }

    const T& front() const {
        ASSERT(len);
        return ptr[0];
    }

    const T& back() const {
        ASSERT(len);
        return ptr[len - 1];
    }

    uint32_t count() const { return len; }
    bool empty() const { return len == 0; }

    const T& operator[](uint32_t index) const {
        ASSERT(index < len);
        return ptr[index];
    }

private:
    const T* ptr = nullptr;
    uint32_t len = 0;
};

}
