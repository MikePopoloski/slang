//------------------------------------------------------------------------------
//! @file Procedure.h
//! @brief MIR procedures (always, initial, etc)
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/mir/MIRBuilder.h"

namespace slang {

class Expression;
class ProceduralBlockSymbol;

namespace mir {

class Procedure {
public:
    Procedure(MIRBuilder& builder, const ProceduralBlockSymbol& block);

    MIRValue emitExpr(const Expression& expr);

    MIRValue emitCall(SysCallKind sysCall, const Type& returnType, span<const MIRValue> args);
    void emitCall(SysCallKind sysCall, span<const MIRValue> args);
    void emitCall(SysCallKind sysCall, MIRValue arg0);

    MIRValue emitConst(const Type& type, const ConstantValue& val) {
        return builder.emitConst(type, val);
    }

    MIRValue emitConst(const Type& type, ConstantValue&& val) {
        return builder.emitConst(type, std::move(val));
    }

    void emitLocal(const VariableSymbol& symbol);
    MIRValue emitGlobal(const VariableSymbol& symbol) { return builder.emitGlobal(symbol); }

    span<const Instr> getInstructions() const { return instructions; }
    span<const VariableSymbol* const> getLocals() const { return locals; }

    Compilation& getCompilation() const;

    std::string toString() const;

private:
    span<const MIRValue> copyValues(span<const MIRValue> values);

    MIRBuilder& builder;
    std::vector<Instr> instructions;
    std::vector<BasicBlock> blocks;
    std::vector<const VariableSymbol*> locals;
    flat_hash_map<const VariableSymbol*, MIRValue> localMap;
};

} // namespace mir

} // namespace slang