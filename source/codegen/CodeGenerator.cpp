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

#include "slang/symbols/ASTVisitor.h"
#include "slang/symbols/Symbol.h"

namespace slang {

CodeGenerator::CodeGenerator(Compilation& compilation) : compilation(compilation) {
    ctx = std::make_unique<llvm::LLVMContext>();
    module = std::make_unique<llvm::Module>("primary", *ctx);
}

CodeGenerator::~CodeGenerator() = default;

std::string CodeGenerator::run(const Symbol& symbol) {
    // Create a "main" function.
    auto intType = llvm::Type::getInt32Ty(*ctx);
    auto funcType = llvm::FunctionType::get(intType, /* isVarArg */ false);
    auto mainFunc =
        llvm::Function::Create(funcType, llvm::Function::ExternalLinkage, "main", *module);

    auto bb = llvm::BasicBlock::Create(*ctx, "", mainFunc);
    llvm::IRBuilder<> ir(bb);

    // Declare C puts function for printing.
    funcType = llvm::FunctionType::get(intType, { llvm::Type::getInt8PtrTy(*ctx) },
                                       /* isVarArg */ false);
    auto puts = llvm::Function::Create(funcType, llvm::Function::ExternalLinkage, "puts", *module);
    auto callPuts = [&](string_view text) {
        ir.CreateCall(puts,
                      { ir.CreateGlobalStringPtr(llvm::StringRef(text.data(), text.length())) });
    };

    // Visit all procedural blocks.
    symbol.visit(makeVisitor([&](const ProceduralBlockSymbol& block) {
        // Only look at initial blocks.
        if (block.procedureKind == ProceduralBlockKind::Initial) {
            // Find all subroutine calls.
            block.getBody().visit(makeVisitor([&](const CallExpression& call) {
                // Only look at $display calls.
                if (call.getSubroutineName() == "$display") {
                    // Emit a call to "puts" for every argument that has a known constant value.
                    for (auto arg : call.arguments()) {
                        EvalContext evalContext(compilation);
                        ConstantValue val = arg->eval(evalContext);
                        if (val) {
                            if (arg->isImplicitString())
                                callPuts(val.convertToStr().toString());
                            else
                                callPuts(val.toString());
                        }
                    }
                }
            }));
        }
    }));

    ir.CreateRet(llvm::ConstantInt::get(intType, 0));

    bool bad = llvm::verifyModule(*module, &llvm::errs());
    if (bad)
        return "";

    std::string result;
    llvm::raw_string_ostream os(result);
    module->print(os, nullptr);

    return os.str();
}

} // namespace slang