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

// Simple wrapper to make getting function types more compact.
template<typename TRet, typename... TParam>
llvm::FunctionType* getFuncType(TRet&& ret, TParam&&... params) {
    return llvm::FunctionType::get(std::forward<TRet>(ret), { std::forward<TParam>(params)... },
                                   /* isVarArg */ false);
}

llvm::Function* CodeGenFunction::getSysFunc(mir::SysCallKind kind) const {
    auto ptr = [](auto type) { return llvm::PointerType::getUnqual(type); };

    llvm::FunctionType* ft;
    switch (kind) {
        case SysCallKind::flush:
            ft = getFuncType(types.Void, types.Int1);
            break;
        case SysCallKind::printStr:
            ft = getFuncType(types.Void, ptr(types.Int8), types.Size);
            break;
        case SysCallKind::printInt:
            ft = getFuncType(types.Void, ptr(types.BoxedInt), types.Int8, types.Int32, types.Int1);
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

        ASSERT(argIt != func->arg_end());
        auto expectedType = argIt->getType();
        argIt++;

        if (expectedType->isPointerTy() &&
            expectedType->getPointerElementType() == types.BoxedInt) {
            // If the argument should be boxed, do that now.
            args.append(boxInt(val, getTypeOf(op)).getPointer());
        }
        else if (val->getType() == types.StringObj) {
            // If the argument is a string object, decompose into two separate arguments,
            // the data pointer and the length.
            args.append(builder.CreateExtractValue(val, 0));
            args.append(builder.CreateExtractValue(val, 1));

            ASSERT(argIt != func->arg_end());
            argIt++;
        }
        else {
            // Otherwise, pass the argument directly.
            args.append(val);
        }
    }

    return builder.CreateCall(func, llvm::makeArrayRef(args.data(), args.size()));
}

} // namespace slang
