//------------------------------------------------------------------------------
//! @file Procedure.h
//! @brief MIR procedures (always, initial, etc)
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <vector>

#include "slang/mir/Instr.h"
#include "slang/util/BumpAllocator.h"

namespace slang {

class ConstantValue;
class Expression;
class ProceduralBlockSymbol;
class Type;

namespace mir {

class MIRBuilder;

class Procedure {
public:
    Procedure(MIRBuilder& builder, const ProceduralBlockSymbol& block);

    MIRValue emitExpr(const Expression& expr);
    MIRValue emitConst(const ConstantValue& val);
    MIRValue emitConst(ConstantValue&& val);

    MIRValue emitCall(SysCallKind sysCall, const Type& returnType, span<const MIRValue> args);
    void emitCall(SysCallKind sysCall, span<const MIRValue> args);
    void emitCall(SysCallKind sysCall, MIRValue arg0);

    span<const Instr> getInstructions() const { return instructions; }

    std::string toString() const;

private:
    span<const MIRValue> copyValues(span<const MIRValue> values);

    MIRBuilder& builder;
    std::vector<Instr> instructions;
    std::vector<BasicBlock> blocks;
    BumpAllocator alloc;
    TypedBumpAllocator<ConstantValue> constantAlloc;
};

} // namespace mir

} // namespace slang