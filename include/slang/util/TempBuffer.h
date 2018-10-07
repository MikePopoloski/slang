//------------------------------------------------------------------------------
// TempBuffer.h
// Temporary buffer type that tries to use stack memory where possible.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang {

/// Provides a temporary storage region of dynamic size. If that size is less than
/// the specified stack size, the memory will be entirely contained on the stack.
/// Otherwise, a heap allocation will be performed and then cleaned up in the destructor.
template<typename T, size_t StackCount>
class TempBuffer {
public:
    explicit TempBuffer(size_t size) : size(size) {
        if (size > StackCount)
            ptr = new T[size];
        else {
            ptr = reinterpret_cast<T*>(stackBase);
            std::uninitialized_default_construct_n(ptr, size);
        }
    }

    void fill(uint8_t b) { memset(ptr, b, size * sizeof(T)); }

    ~TempBuffer() {
        if (size > StackCount)
            delete[] ptr;
        else
            std::destroy_n(ptr, size);
    }

    T* get() const { return ptr; }

private:
    T* ptr;
    size_t size;
    alignas(T) char stackBase[StackCount * sizeof(T)];
};

} // namespace slang