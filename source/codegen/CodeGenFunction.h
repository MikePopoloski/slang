//------------------------------------------------------------------------------
// CodeGenFunction.h
// LLVM code generation for SystemVerilog procedures
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "CGBuilder.h"

#include "slang/mir/Instr.h"

namespace slang {

class CodeGenerator;
class CodeGenTypes;

namespace mir {

class Procedure;

} // namespace mir

class CodeGenFunction {
public:
    CodeGenFunction(CodeGenerator& codegen, const mir::Procedure& proc);

    llvm::Function* finalize();

private:
    const Type& getTypeOf(mir::MIRValue val) const;
    llvm::Function* getSysFunc(mir::SysCallKind kind) const;

    Address createTempAlloca(AlignedType type);
    Address boxInt(llvm::Value* value, const Type& type);

    llvm::Value* emit(const mir::Instr& instr);
    llvm::Value* emit(mir::MIRValue val);
    llvm::Value* emitSysCall(mir::SysCallKind kind, span<const mir::MIRValue> operands);
    llvm::Value* emitLoad(mir::MIRValue val);
    llvm::Value* emitStore(mir::MIRValue dest, mir::MIRValue src);

    llvm::Value* emitNegate(const Type& type, mir::MIRValue op);

    llvm::Value* emitConstant(const Type& type, const ConstantValue& cv);
    llvm::Value* emitConstant(const Type& type, const SVInt& integer);

    Address emitLValue(mir::MIRValue val);

    CodeGenerator& codegen;
    CodeGenTypes& types;
    CGBuilder builder;
    llvm::LLVMContext& ctx;
    llvm::Function* generatedFunc;

    // Stored values per instruction, so that they can be referred to by later instructions.
    struct InstrValue {
        llvm::Value* val;
        not_null<const Type*> astType;
    };
    SmallVectorSized<InstrValue, 8> instrValues;

    // This is an instruction in the entry block before which we prefer to insert allocas.
    llvm::AssertingVH<llvm::Instruction> allocaInsertionPoint;

    // A list of local variables that have been alloca-ed.
    struct LocalVar {
        Address addr;
        not_null<const Type*> astType;
        llvm::Type* nativeType;
    };
    SmallVectorSized<LocalVar, 8> locals;
};

} // namespace slang
