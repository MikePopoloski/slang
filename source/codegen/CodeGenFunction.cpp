//------------------------------------------------------------------------------
// CodeGenFunction.cpp
// LLVM code generation for SystemVerilog procedures
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "CodeGenFunction.h"

#include "CodeGenTypes.h"

#include "slang/codegen/CodeGenerator.h"
#include "slang/mir/Procedure.h"
#include "slang/symbols/AllTypes.h"

namespace slang {

using namespace mir;

CodeGenFunction::CodeGenFunction(CodeGenerator& codegen, const Procedure& proc) :
    codegen(codegen), types(codegen.getTypes()), builder(codegen.getContext()),
    ctx(codegen.getContext()) {

    auto funcType = llvm::FunctionType::get(types.VoidType, /* isVarArg */ false);
    generatedFunc =
        llvm::Function::Create(funcType, llvm::Function::PrivateLinkage, "", codegen.getModule());

    auto bb = llvm::BasicBlock::Create(ctx, "", generatedFunc);
    builder.SetInsertPoint(bb);

    for (auto& instr : proc.getInstructions())
        emit(instr);

    builder.CreateRetVoid();
}

llvm::Value* CodeGenFunction::emit(const Instr& instr) {
    switch (instr.kind) {
        case InstrKind::syscall:
            return emitSysCall(instr.getSysCallKind(), instr.getOperands());
        case InstrKind::invalid:
            return builder.CreateUnreachable();
    }
    THROW_UNREACHABLE;
}

llvm::Value* CodeGenFunction::emit(MIRValue val) {
    switch (val.getKind()) {
        case MIRValue::Constant: {
            auto& tcv = val.asConstant();
            return emitConstant(tcv.type, tcv.value);
        }
        case MIRValue::InstrSlot:
        case MIRValue::Global:
        case MIRValue::Local:
        case MIRValue::Empty:
            // TODO:
            break;
    }
    THROW_UNREACHABLE;
}

llvm::Constant* CodeGenFunction::emitConstant(const Type& type, const ConstantValue& cv) {
    // TODO: other value types
    return emitConstant(type, cv.integer());
}

llvm::Constant* CodeGenFunction::emitConstant(const Type& type, const SVInt& integer) {
    auto& intType = type.as<IntegralType>();
    uint32_t bits = intType.bitWidth;
    if (intType.isFourState)
        bits *= 2;

    llvm::ArrayRef<uint64_t> data(integer.getRawPtr(), integer.getNumWords());
    if (bits <= codegen.getOptions().maxIntBits)
        return llvm::ConstantInt::get(ctx, llvm::APInt(bits, data));
    else
        return llvm::ConstantDataArray::get(ctx, data);
}

const Type& CodeGenFunction::getTypeOf(MIRValue val) const {
    switch (val.getKind()) {
        case MIRValue::Constant:
            return val.asConstant().type;
        case MIRValue::InstrSlot:
        case MIRValue::Global:
        case MIRValue::Local:
        case MIRValue::Empty:
            // TODO:
            break;
    }
    THROW_UNREACHABLE;
}

} // namespace slang