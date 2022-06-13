//------------------------------------------------------------------------------
//! @file CodeGenerator.h
//! @brief Executable code generation
//! @note Only included if slang is configured to use LLVM
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <memory>
#include <string>
#include <vector>

#include "slang/util/Function.h"
#include "slang/util/Hash.h"
#include "slang/util/Util.h"

namespace llvm {

class BasicBlock;
class Function;
class GlobalVariable;
class LLVMContext;
class Module;

} // namespace llvm

namespace slang {

class CodeGenTypes;
class Compilation;

namespace mir {

class MIRBuilder;
class Procedure;
enum class SysCallKind;

} // namespace mir

struct CodegenOptions {
    uint32_t maxIntBits = 128;
    bool flattenFourState = false;
};

class GeneratedCode {
public:
    GeneratedCode(std::unique_ptr<llvm::LLVMContext> context, std::unique_ptr<llvm::Module> module);
    GeneratedCode(GeneratedCode&&);
    ~GeneratedCode();

    std::pair<std::unique_ptr<llvm::LLVMContext>, std::unique_ptr<llvm::Module>> release();
    std::string toString() const;

private:
    std::unique_ptr<llvm::LLVMContext> context;
    std::unique_ptr<llvm::Module> module;
};

class CodeGenerator {
public:
    explicit CodeGenerator(const Compilation& compilation);
    ~CodeGenerator();

    void emitAll(const mir::MIRBuilder& design);

    void emit(const mir::Procedure& proc);

    GeneratedCode finish();

    llvm::LLVMContext& getContext() { return *ctx; }
    llvm::Module& getModule() { return *module; }
    CodeGenTypes& getTypes() { return *types; }
    const CodegenOptions& getOptions() const { return options; }
    const Compilation& getCompilation() const { return compilation; }

    llvm::Function* getOrCreateSystemFunction(mir::SysCallKind kind,
                                              function_ref<llvm::Function*()> factory);

    llvm::GlobalVariable* getOrCreateStringConstant(const std::string& str);

private:
    std::unique_ptr<llvm::LLVMContext> ctx;
    std::unique_ptr<llvm::Module> module;
    std::unique_ptr<CodeGenTypes> types;
    flat_hash_map<mir::SysCallKind, llvm::Function*> sysFunctions;
    flat_hash_map<std::string, llvm::GlobalVariable*> stringConstants;
    const Compilation& compilation;
    CodegenOptions options;
    llvm::BasicBlock* globalInitBlock;
    std::vector<llvm::BasicBlock*> initialBlocks;
    llvm::Function* mainFunc;
};

} // namespace slang
