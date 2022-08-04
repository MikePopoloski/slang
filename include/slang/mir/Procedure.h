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

    MIRValue emitInstr(InstrKind kind, const Type& type, MIRValue op0);
    MIRValue emitInstr(InstrKind kind, const Type& type, MIRValue op0, MIRValue op1);

    MIRValue emitConst(const Type& type, const ConstantValue& val) {
        return builder.emitConst(type, val);
    }

    MIRValue emitConst(const Type& type, ConstantValue&& val) {
        return builder.emitConst(type, std::move(val));
    }

    MIRValue emitInt(bitwidth_t width, uint64_t value, bool isSigned);

    MIRValue emitBool(bool b) { return emitInt(1, uint64_t(b), /* isSigned */ false); }

    MIRValue emitString(std::string&& str);

    template<int N>
    MIRValue emitString(const char (&str)[N]) {
        return emitString(std::string(str));
    }

    void emitLocal(const VariableSymbol& symbol);
    MIRValue emitGlobal(const VariableSymbol& symbol) { return builder.emitGlobal(symbol); }

    span<const Instr> getInstructions() const { return instructions; }
    span<const VariableSymbol* const> getLocals() const { return locals; }
    const VariableSymbol& getLocalSymbol(MIRValue val) const;
    MIRValue findLocalSlot(const VariableSymbol& symbol) const;

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
