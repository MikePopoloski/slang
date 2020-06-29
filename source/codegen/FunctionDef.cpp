//------------------------------------------------------------------------------
// FunctionDef.cpp
// Executable function definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/codegen/FunctionDef.h"

#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>

#include "slang/codegen/CodeGenerator.h"
#include "slang/mir/Instr.h"

namespace slang {

using namespace mir;

FunctionDef::FunctionDef(const CodeGenerator& codegen, string_view name, llvm::Type* returnType,
                         span<const ParamDef> params) :
    returnType(returnType),
    name(name), params(params) {

    SmallVectorSized<llvm::Type*, 8> types;
    for (auto& param : params)
        types.append(param.nativeType);

    if (!returnType)
        returnType = llvm::Type::getVoidTy(codegen.getContext());

    auto funcType =
        llvm::FunctionType::get(returnType, llvm::ArrayRef<llvm::Type*>(types.begin(), types.end()),
                                /* isVarArg */ false);

    nativeFunc =
        llvm::Function::Create(funcType, llvm::Function::ExternalLinkage,
                               llvm::StringRef(name.data(), name.length()), codegen.getModule());
}

FunctionDef FunctionDef::getSystemFunc(CodeGenerator& codegen, SysCallKind kind) {
    auto& ctx = codegen.getContext();
    auto voidType = llvm::Type::getVoidTy(ctx);
    auto boolType = llvm::Type::getInt1Ty(ctx);
    auto int8Type = llvm::Type::getInt8Ty(ctx);
    auto int32Type = llvm::Type::getInt32Ty(ctx);

    SmallVectorSized<ParamDef, 8> params;
    switch (kind) {
        case SysCallKind::printChar:
            params.append({ int8Type });
            break;
        case SysCallKind::printInt:
            params.append({ codegen.getGenericIntPtrType() });
            params.append({ int8Type });
            params.append({ int32Type });
            params.append({ boolType });
            break;
        default:
            THROW_UNREACHABLE;
    }

    return FunctionDef(codegen, toString(kind), voidType, params.copy(codegen));
}

} // namespace slang