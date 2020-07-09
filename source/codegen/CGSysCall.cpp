//------------------------------------------------------------------------------
// CGSysCall.cpp
// CodeGenFunction methods related to system calls
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "CodeGenFunction.h"
#include "CodeGenTypes.h"

#include "slang/codegen/CodeGenerator.h"

namespace slang {

using namespace mir;

template<typename TRet, typename... TParam>
llvm::FunctionType* getFuncType(TRet&& ret, TParam&&... params) {
    return llvm::FunctionType::get(std::forward<TRet>(ret), { std::forward<TParam>(params)... },
                                   /* isVarArg */ false);
}

llvm::Function* CodeGenFunction::getSysFunc(mir::SysCallKind kind) const {
    llvm::FunctionType* ft;
    switch (kind) {
        case SysCallKind::printChar:
            ft = getFuncType(types.VoidType, types.Int8Type);
            break;
        case SysCallKind::printInt:
            ft = getFuncType(types.VoidType, llvm::PointerType::getUnqual(types.BoxedIntType),
                             types.Int8Type, types.Int32Type, types.BoolType);
            break;
        default:
            THROW_UNREACHABLE;
    }

    auto name = toString(kind);
    return llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                  llvm::StringRef(name.data(), name.length()), codegen.getModule());
}

llvm::Value* CodeGenFunction::emitSysCall(SysCallKind kind, span<const mir::MIRValue> operands) {
    auto func = codegen.getOrCreateSystemFunction(kind, [this, kind] { return getSysFunc(kind); });
    auto argIt = func->arg_begin();

    SmallVectorSized<llvm::Value*, 8> args;
    for (auto& op : operands) {
        // Emit the argument.
        auto val = emit(op);

        // If the argument should be boxed, do that now.
        ASSERT(argIt != func->arg_end());
        auto type = argIt->getType();
        if (type->isPointerTy() && type->getPointerElementType() == types.BoxedIntType)
            val = boxInt(val, getTypeOf(op)).getPointer();

        args.append(val);
        argIt++;
    }

    return builder.CreateCall(func, llvm::makeArrayRef(args.data(), args.size()));
}

} // namespace slang