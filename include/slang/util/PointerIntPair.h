//------------------------------------------------------------------------------
//! @file PointerIntPair.h
//! @brief Space optimize pointer + int pair type
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang {

template<typename TPointer, uint32_t IntBits, uint32_t LowBitsAvailable, typename TInt = uint32_t>
class PointerIntPair {
    enum : uintptr_t {
        PointerMask = ~(uintptr_t)(((intptr_t)1 << LowBitsAvailable) - 1),
        IntShift = (uintptr_t)LowBitsAvailable - IntBits,
        IntMask = (uintptr_t)(((intptr_t)1 << IntBits) - 1),
        ShiftedIntMask = (uintptr_t)(IntMask << IntShift)
    };

public:
    PointerIntPair() = default;
    PointerIntPair(TPointer ptr, TInt intVal) { setBoth(ptr, intVal); }

    TPointer getPointer() const {
        return static_cast<TPointer>(reinterpret_cast<void*>(value & PointerMask));
    }

    TInt getInt() const { return TInt((value >> IntShift) & IntMask); }

    void setPointer(TPointer ptr) {
        intptr_t ptrWord = reinterpret_cast<intptr_t>(ptr);
        ASSERT((ptrWord & ~PointerMask) == 0);
        value = ptrWord | (value & ~PointerMask);
    }

    void setInt(TInt intVal) {
        intptr_t intWord = static_cast<intptr_t>(intVal);
        ASSERT((intWord & ~IntMask) == 0);
        value = (value & ~ShiftedIntMask) | (intWord << IntShift);
    }

    void setBoth(TPointer ptr, TInt intVal) {
        value = 0;
        setPointer(ptr);
        setInt(intVal);
    }

    intptr_t getOpaqueValue() const { return value; }

    bool operator==(const PointerIntPair& rhs) const { return value == rhs.value; }
    bool operator!=(const PointerIntPair& rhs) const { return value != rhs.value; }
    bool operator<(const PointerIntPair& rhs) const { return value < rhs.value; }
    bool operator<=(const PointerIntPair& rhs) const { return value <= rhs.value; }
    bool operator>(const PointerIntPair& rhs) const { return value > rhs.value; }
    bool operator>=(const PointerIntPair& rhs) const { return value >= rhs.value; }

private:
    intptr_t value = 0;
};

} // namespace slang
