//------------------------------------------------------------------------------
//! @file Instr.h
//! @brief MIR instruction definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Enum.h"

namespace slang {

class ConstantValue;
class Type;

namespace mir {

// clang-format off
#define INSTR(x) \
    x(Invalid) \
    x(SysCall)
ENUM(InstrKind, INSTR);
#undef INSTR

#define SYSCALL(x) \
    x(PrintChar) \
    x(PrintInt)
ENUM(SysCallKind, SYSCALL);
#undef SYSCALL
// clang-format on

class MIRValue {
public:
    enum Kind { Empty, Slot, Constant };

    MIRValue() : val(0) {}
    explicit MIRValue(const ConstantValue& cv) : val(reinterpret_cast<uintptr_t>(&cv) | Constant) {}
    explicit MIRValue(size_t instructionIndex) : val(instructionIndex << 3) {}

    Kind getKind() const { return Kind(val & 7); }

    const ConstantValue& asConstant() const {
        ASSERT(getKind() == Constant);
        return *reinterpret_cast<const ConstantValue*>(val & ~7ull);
    }

    size_t asInstrSlot() const {
        ASSERT(getKind() == Slot);
        return val >> 3;
    }

private:
    uintptr_t val;
};
static_assert(sizeof(MIRValue) == 8);

class Instr {
public:
    const Type& type;
    InstrKind kind;

    Instr(SysCallKind sysCall, const Type& returnType, span<const MIRValue> args) noexcept :
        type(returnType), kind(InstrKind::SysCall), sysCallKind(sysCall), varOps(args) {}

    SysCallKind getSysCallKind() const { return sysCallKind; }
    span<const MIRValue> getOperands() const;

private:
    SysCallKind sysCallKind;

    union {
        MIRValue immOps[2];
        span<const MIRValue> varOps;
    };
};
static_assert(sizeof(span<const MIRValue>) == 16);
static_assert(sizeof(Instr) == 32);

class BasicBlock {
public:
};

} // namespace mir

} // namespace slang