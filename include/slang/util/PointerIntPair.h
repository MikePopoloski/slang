//------------------------------------------------------------------------------
//! @file PointerIntPair.h
//! @brief Space optimized pointer + int pair type
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang {

/// A data structure that operates as a pair of a pointer and an integer,
/// which fits in the space of one full sized pointer by exploiting unused
/// bits in the pointer representation.
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
        uintptr_t ptrWord = reinterpret_cast<uintptr_t>(ptr);
        SLANG_ASSERT((ptrWord & ~PointerMask) == 0);
        value = ptrWord | (value & ~PointerMask);
    }

    void setInt(TInt intVal) {
        uintptr_t intWord = static_cast<uintptr_t>(intVal);
        SLANG_ASSERT((intWord & ~IntMask) == 0);
        value = (value & ~ShiftedIntMask) | (intWord << IntShift);
    }

    void setBoth(TPointer ptr, TInt intVal) {
        value = 0;
        setPointer(ptr);
        setInt(intVal);
    }

    uintptr_t getOpaqueValue() const { return value; }

    auto operator<=>(const PointerIntPair& rhs) const = default;

private:
    uintptr_t value = 0;
};

} // namespace slang
