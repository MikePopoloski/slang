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

    llvm::Function* getFunction() { return generatedFunc; }

    llvm::Value* emit(const mir::Instr& instr);
    llvm::Value* emit(mir::MIRValue val);
    llvm::Value* emitSysCall(mir::SysCallKind kind, span<const mir::MIRValue> operands);

    llvm::Constant* emitConstant(const Type& type, const ConstantValue& cv);
    llvm::Constant* emitConstant(const Type& type, const SVInt& integer);

private:
    const Type& getTypeOf(mir::MIRValue val) const;
    llvm::Function* getSysFunc(mir::SysCallKind kind) const;

    CodeGenerator& codegen;
    CodeGenTypes& types;
    CGBuilder builder;
    llvm::LLVMContext& ctx;
    llvm::Function* generatedFunc;
};

} // namespace slang