//------------------------------------------------------------------------------
//! @file Instr.h
//! @brief MIR instruction definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/numeric/ConstantValue.h"
#include "slang/util/Enum.h"
#include "slang/util/Util.h"

namespace slang {

class Type;

namespace mir {

struct TypedConstantValue {
    const Type& type;
    ConstantValue value;

    TypedConstantValue(const Type& type, const ConstantValue& value) : type(type), value(value) {}
    TypedConstantValue(const Type& type, ConstantValue&& value) :
        type(type), value(std::move(value)) {}
};

// clang-format off
#define INSTR(x) \
    x(invalid) \
    x(syscall) \
    x(store) \
    x(negate) \
    x(bitnot) \
    x(reducand) \
    x(reducor) \
    x(reducxor)
ENUM(InstrKind, INSTR);
#undef INSTR

#define SYSCALL(x) \
    x(flush) \
    x(printStr) \
    x(printInt) \
    x(printFloat)

ENUM(SysCallKind, SYSCALL);
#undef SYSCALL
// clang-format on

class MIRValue {
public:
    enum Kind { Empty, InstrSlot, Constant, Local, Global };

    MIRValue() : val(0) {}
    explicit MIRValue(const TypedConstantValue& cv) :
        val(reinterpret_cast<uintptr_t>(&cv) | Constant) {}
    MIRValue(Kind kind, size_t index) : val((index << 3) | kind) {}

    static MIRValue slot(size_t index) { return MIRValue(InstrSlot, index); }
    static MIRValue local(size_t index) { return MIRValue(Local, index); }
    static MIRValue global(size_t index) { return MIRValue(Global, index); }

    Kind getKind() const { return Kind(val & 7); }

    const TypedConstantValue& asConstant() const {
        ASSERT(getKind() == Constant);
        return *reinterpret_cast<const TypedConstantValue*>(val & ~7ull);
    }

    bool isConstant() const { return getKind() == Constant; }

    size_t asIndex() const {
        ASSERT(!isConstant());
        return val >> 3;
    }

    explicit operator bool() const { return getKind() != Empty; }

private:
    uintptr_t val;
};

class Instr {
public:
    const Type& type;
    InstrKind kind;

    Instr(InstrKind kind, const Type& type, MIRValue op) noexcept :
        type(type), kind(kind), immOps{ op, MIRValue{} } {}
    Instr(InstrKind kind, const Type& type, MIRValue op0, MIRValue op1) noexcept :
        type(type), kind(kind), immOps{ op0, op1 } {}

    Instr(SysCallKind sysCall, const Type& returnType, span<const MIRValue> args) noexcept :
        type(returnType), kind(InstrKind::syscall), sysCallKind(sysCall), varOps(args) {}

    SysCallKind getSysCallKind() const { return sysCallKind; }
    span<const MIRValue> getOperands() const;

private:
    SysCallKind sysCallKind;

    union {
        MIRValue immOps[2];
        span<const MIRValue> varOps;
    };
};

class BasicBlock {
public:
};

} // namespace mir

} // namespace slang
