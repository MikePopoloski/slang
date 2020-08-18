//------------------------------------------------------------------------------
// CodeGenerator.cpp
// Executable code generation
// NOTE: Only included if slang is configured to use LLVM
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/codegen/CodeGenerator.h"

#include "CGBuilder.h"
#include "CodeGenFunction.h"
#include "CodeGenTypes.h"
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/TargetSelect.h>

#include "slang/compilation/Compilation.h"
#include "slang/mir/Procedure.h"

namespace slang {

GeneratedCode::GeneratedCode(std::unique_ptr<llvm::LLVMContext> context,
                             std::unique_ptr<llvm::Module> module) :
    context(std::move(context)),
    module(std::move(module)) {
}

GeneratedCode::GeneratedCode(GeneratedCode&&) = default;
GeneratedCode::~GeneratedCode() = default;

std::pair<std::unique_ptr<llvm::LLVMContext>, std::unique_ptr<llvm::Module>> GeneratedCode::
    release() {
    return { std::move(context), std::move(module) };
}

std::string GeneratedCode::toString() const {
    std::string result;
    llvm::raw_string_ostream os(result);
    module->print(os, nullptr);
    return os.str();
}

CodeGenerator::CodeGenerator(const Compilation& compilation) : compilation(compilation) {
    llvm::InitializeNativeTarget();
    llvm::InitializeNativeTargetAsmPrinter();
    llvm::InitializeNativeTargetAsmParser();

    ctx = std::make_unique<llvm::LLVMContext>();
    module = std::make_unique<llvm::Module>("primary", *ctx);
    types = std::make_unique<CodeGenTypes>(*this);

    // Create the main entry point.
    auto intType = llvm::Type::getInt32Ty(*ctx);
    auto funcType = llvm::FunctionType::get(intType, /* isVarArg */ false);
    mainFunc = llvm::Function::Create(funcType, llvm::Function::ExternalLinkage, "main", *module);

    // Create the first basic block that will run at the start of simulation
    // to initialize all static variables.
    globalInitBlock = llvm::BasicBlock::Create(*ctx, "", mainFunc);
}

CodeGenerator::~CodeGenerator() = default;

void CodeGenerator::emitAll(const mir::MIRBuilder& design) {
    for (auto& proc : design.getInitialProcs())
        emit(*proc);
}

void CodeGenerator::emit(const mir::Procedure& proc) {
    CodeGenFunction cgf(*this, proc);
    llvm::IRBuilder<> caller(globalInitBlock);
    caller.CreateCall(cgf.finalize(), {});
}

GeneratedCode CodeGenerator::finish() {
    // Insert all initial blocks into the main function.
    auto lastBlock = globalInitBlock;
    for (auto block : initialBlocks) {
        llvm::IRBuilder<>(lastBlock).CreateBr(block);
        lastBlock = block;
    }

    // Finish the main function.
    auto intType = llvm::Type::getInt32Ty(*ctx);
    llvm::IRBuilder<>(lastBlock).CreateRet(llvm::ConstantInt::get(intType, 0));

    // Verify all generated code.
    bool bad = llvm::verifyModule(*module, &llvm::errs());
    if (bad)
        module->print(llvm::errs(), nullptr); // ld: undefined symbol llvm::Module::dump()

    return GeneratedCode(std::move(ctx), std::move(module));
}

llvm::Function* CodeGenerator::getOrCreateSystemFunction(mir::SysCallKind kind,
                                                         function_ref<llvm::Function*()> factory) {
    auto it = sysFunctions.find(kind);
    if (it == sysFunctions.end())
        it = sysFunctions.emplace(kind, factory()).first;

    return it->second;
}

llvm::GlobalVariable* CodeGenerator::getOrCreateStringConstant(const std::string& str) {
    auto it = stringConstants.find(str);
    if (it == stringConstants.end()) {
        // TODO: alignment
        auto cda = llvm::ConstantDataArray::getString(*ctx, str, /* AddNull */ false);
        auto gv = new llvm::GlobalVariable(*module, cda->getType(), /* isConstant */ true,
                                           llvm::GlobalValue::PrivateLinkage, cda);
        gv->setAlignment(llvm::Align(llvm::Align::Constant<1>()));
        gv->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
        gv->setDSOLocal(true);

        it = stringConstants.emplace(str, gv).first;
    }
    return it->second;
}

// TODO:
// void CodeGenerator::genGlobal(const VariableSymbol& variable) {
//    ASSERT(variable.lifetime == VariableLifetime::Static);
//
//    auto& type = variable.getType();
//
//    bool needsInitializer = false;
//    llvm::Constant* constVal = nullptr;
//    if (auto init = variable.getInitializer()) {
//        EvalContext evCtx(compilation);
//        ConstantValue val = init->eval(evCtx);
//        if (val)
//            constVal = genConstant(type, val);
//        else
//            needsInitializer = true;
//    }
//
//    // If no initializer provided, use the default for the type.
//    if (!constVal)
//        constVal = genConstant(type, type.getDefaultValue());
//
//    auto global = new llvm::GlobalVariable(*module, genType(type), /* isConstant */ false,
//                                           llvm::GlobalValue::PrivateLinkage, constVal);
//    globalMap.emplace(&variable, global);
//
//    // If we set needsInitializer, the variable has an initializer expression
//    // but it's not constant. Emit it into the basic block that will run at
//    // the start of simulation.
//    if (needsInitializer) {
//        auto expr = genExpr(globalInitBlock, *variable.getInitializer());
//        llvm::IRBuilder<> ir(globalInitBlock);
//        ir.CreateStore(expr, global);
//    }
//}

} // namespace slang
