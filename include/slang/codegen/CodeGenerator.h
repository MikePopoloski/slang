//------------------------------------------------------------------------------
//! @file CodeGenerator.h
//! @brief Executable code generation
//! @note Only included if slang is configured to use LLVM
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>
#include <memory>
#include <string>
#include <vector>

#include "slang/util/Util.h"

namespace llvm {

class BasicBlock;
class Constant;
class ConstantFolder;
class Function;
class IRBuilderDefaultInserter;
class LLVMContext;
class Module;
class Type;
class Value;

template<typename T, typename U>
class IRBuilder;

} // namespace llvm

namespace slang {

class Compilation;
class ConstantValue;
class Expression;
class InstanceSymbol;
class ProceduralBlockSymbol;
class Statement;
class SubroutineSymbol;
class SVInt;
class Symbol;
class SystemSubroutine;
class Type;
class VariableSymbol;

namespace mir {

class Instr;
class MIRValue;
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
    CodeGenerator(Compilation& compilation);
    ~CodeGenerator();

    void generate(const mir::Procedure& proc);

    GeneratedCode finish();

    void genInstance(const InstanceSymbol& instance);
    void genStmt(llvm::BasicBlock* bb, const Statement& stmt);

    llvm::Constant* genConstant(const Type& type, const ConstantValue& cv);
    llvm::Constant* genConstant(const Type& type, const SVInt& integer);
    llvm::Type* genType(const Type& type);
    llvm::Value* genExpr(llvm::BasicBlock* bb, const Expression& expr);
    llvm::Function* genSubroutine(const SubroutineSymbol& subroutine);
    llvm::Function* genSubroutine(const SystemSubroutine& subroutine);

private:
    using IRBuilder = llvm::IRBuilder<llvm::ConstantFolder, llvm::IRBuilderDefaultInserter>;

    llvm::Value* emit(IRBuilder& ir, const mir::Instr& instr);
    llvm::Value* emit(IRBuilder& ir, const mir::MIRValue& val);
    llvm::Value* emitSysCall(IRBuilder& ir, const mir::Instr& instr);

    llvm::Function* getSysFunc(mir::SysCallKind kind);

    void genGlobal(const VariableSymbol& variable);
    void genBlock(const ProceduralBlockSymbol& variable);

    std::unique_ptr<llvm::LLVMContext> ctx;
    std::unique_ptr<llvm::Module> module;
    flat_hash_map<const Type*, llvm::Type*> typeMap;
    flat_hash_map<const Symbol*, llvm::Value*> globalMap;
    flat_hash_map<const SubroutineSymbol*, llvm::Function*> userSubroutineMap;
    flat_hash_map<const SystemSubroutine*, llvm::Function*> sysSubroutineMap;
    flat_hash_map<mir::SysCallKind, llvm::Function*> sysFunctions;
    llvm::BasicBlock* globalInitBlock;
    std::vector<llvm::BasicBlock*> initialBlocks;
    llvm::Function* mainFunc;
    Compilation& compilation;
    CodegenOptions options;
};

} // namespace slang