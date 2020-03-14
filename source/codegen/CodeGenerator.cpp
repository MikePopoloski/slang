//------------------------------------------------------------------------------
// CodeGenerator.cpp
// Executable code generation
// NOTE: Only included if slang is configured to use LLVM
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/codegen/CodeGenerator.h"

#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4996) // std::iterator deprecation warning
#endif
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#ifdef _MSC_VER
#    pragma warning(pop)
#endif

using namespace llvm;

namespace slang {

std::string CodeGenerator::run(const Symbol&) {
    // Just testing that LLVM is linked in and running properly.
    LLVMContext ctx;
    Module module("primary", ctx);

    auto funcType = FunctionType::get(Type::getInt32Ty(ctx), /* isVarArg */ false);
    auto func = Function::Create(funcType, Function::ExternalLinkage, "main", module);
    auto bb = BasicBlock::Create(ctx, "", func);
    
    IRBuilder<> ir(bb);
    ir.CreateRet(ConstantInt::get(Type::getInt32Ty(ctx), 0));

    bool bad = llvm::verifyModule(module, &errs());
    if (bad)
        return "";

    std::string result;
    raw_string_ostream os(result);
    module.print(os, nullptr);

    return os.str();
}

} // namespace slang