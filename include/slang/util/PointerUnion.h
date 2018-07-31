//------------------------------------------------------------------------------
// PointerUnion.h
// Lightweight discriminated union.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang {

template<typename T1, typename T2>
class PointerUnion {
    enum : uintptr_t {
        // The number of bits in the pointer that we can steal. Obviously
        // platform dependent, but we'll assert at runtime.
        NumPointerBitsAvailable = 2,

        // The number of bits to reserve for the discriminator.
        IntBits = 1,

        // The mask used to extract the pointer value.
        PointerMask = ~(uintptr_t)(((intptr_t)1 << NumPointerBitsAvailable) - 1),

        // The number of bits to shift to get the discriminator value.
        IntShift = NumPointerBitsAvailable - IntBits,

        // The mask used to extract the discriminator.
        IntMask = (uintptr_t)(((intptr_t)1 << IntBits) - 1)
    };

    uintptr_t value = 0;

    void set(const void* v, uint32_t i) {
        uintptr_t ptr = reinterpret_cast<uintptr_t>(v);
        ASSERT((ptr & ~PointerMask) == 0);
        value = ptr | (i << IntShift);
    }

    uintptr_t getPointer() const { return value & PointerMask; }
    int getDiscrim() const { return (value >> IntShift) & IntMask; }

public:
    PointerUnion() = default;
    PointerUnion(std::nullptr_t) {}
    PointerUnion(T1 v) { set(v, 0); }
    PointerUnion(T2 v) { set(v, 1); }

    template<typename T>
    bool is() const {
        if constexpr (std::is_same_v<T, T1>)
            return getDiscrim() == 0;
        else if constexpr (std::is_same_v<T, T2>)
            return getDiscrim() != 0;
        else
            return false;
    }

    template<typename T>
    T get() const {
        ASSERT(is<T>());
        return reinterpret_cast<T>(getPointer());
    }

    explicit operator bool() const {
        return reinterpret_cast<T1>(getPointer());
    }

    const PointerUnion& operator=(std::nullptr_t) { value = 0; return *this; }
    const PointerUnion& operator=(T1 v) { set(v, 0); return *this; }
    const PointerUnion& operator=(T2 v) { set(v, 1); return *this; }

    bool operator==(const PointerUnion& other) const {
        return value == other.value;
    }

    bool operator!=(const PointerUnion& other) const {
        return value != other.value;
    }

    bool operator<(const PointerUnion& other) const {
        return value < other.value;
    }
};

}