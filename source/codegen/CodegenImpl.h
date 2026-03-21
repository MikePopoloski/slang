//------------------------------------------------------------------------------
// CodegenImpl.h
// Internal implementation types for LLVM-based code generation.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <string>
#include <string_view>
#include <vector>

#include "slang/codegen/CodeGenerator.h"
#include "slang/numeric/ConstantValue.h"
#include "slang/util/FlatMap.h"

#define STR2(x) #x
#define STR(x) STR2(x)

#define SLANG_UNIMPLEMENTED                                                                  \
    do {                                                                                     \
        SLANG_THROW(                                                                         \
            std::logic_error(__FILE__ ":" STR(__LINE__) ": operation not yet implemented")); \
    } while (0)

namespace slang::ast {

class Compilation;
class Expression;
class FormalArgumentSymbol;
class Scope;
class Statement;
class SubroutineSymbol;
class Symbol;
class Type;
class VariableSymbol;

} // namespace slang::ast

namespace slang::codegen {

using namespace ast;

class CodegenContext;

class TypeEmitter {
public:
    llvm::Type* VoidTy;
    llvm::IntegerType *Int8Ty, *Int16Ty, *Int32Ty, *Int64Ty;
    llvm::Type *FloatTy, *DoubleTy;

    explicit TypeEmitter(CodegenContext& context);

    llvm::Type* lower(const Type& type);

    llvm::IntegerType* twoStateFor(bitwidth_t bits);
    llvm::IntegerType* fourStateFor(bitwidth_t bits);

private:
    CodegenContext& context;
    flat_hash_map<const Type*, llvm::Type*> typeCache;
};

class CodegenContext {
public:
    std::unique_ptr<llvm::LLVMContext> ctx;
    std::unique_ptr<llvm::Module> module;
    Compilation& compilation;
    CodegenOptions options;
    TypeEmitter types;

    // Maps already-emitted subroutines to their LLVM functions (for forward/recursive calls).
    flat_hash_map<const SubroutineSymbol*, llvm::Function*> funcMap;

    CodegenContext(Compilation& compilation, std::string_view moduleName, CodegenOptions opts);
};

class IRBuilder : public llvm::IRBuilder<> {
public:
    TypeEmitter& types;

    explicit IRBuilder(CodegenContext& context);

    llvm::ConstantInt* getSVInt(const SVInt& val, bool isFourState);

    llvm::Value* createSVInt(llvm::Value* val, llvm::Value* unk, llvm::Type* type);

    llvm::Value* toFourState(llvm::Value* v);
    llvm::Value* toFourState(llvm::Value* v, llvm::Type* fourStateTy);

    llvm::Value* getValPart(llvm::Value* v) {
        unsigned n = llvm::cast<llvm::IntegerType>(v->getType())->getBitWidth() / 2;
        return CreateTrunc(v, getIntNTy(n));
    }

    llvm::Value* getUnkPart(llvm::Value* v) {
        unsigned n = llvm::cast<llvm::IntegerType>(v->getType())->getBitWidth() / 2;
        return CreateTrunc(CreateLShr(v, n), getIntNTy(n));
    }

    std::pair<llvm::Value*, llvm::Value*> getIntParts(llvm::Value* v) {
        return {getValPart(v), getUnkPart(v)};
    }
};

// Emits LLVM IR for a single subroutine.
class FunctionEmitter {
public:
    explicit FunctionEmitter(CodegenContext& context);

    llvm::Function* lower(const SubroutineSymbol& subroutine);

    void emitStmt(const Statement& stmt);
    void emitBlock(llvm::BasicBlock* bb, bool isFinished = false);
    void emitBranch(llvm::BasicBlock* target);

    llvm::Value* emitExpr(const Expression& expr);
    llvm::Value* emitLValue(const Expression& expr);
    llvm::Value* emitCond(const Expression& expr);

    ConstantValue tryEval(const Expression& expr);

    llvm::BasicBlock* createBasicBlock(const llvm::Twine& name = "",
                                       llvm::Function* parent = nullptr);

    llvm::AllocaInst* createLocal(const VariableSymbol& var);

    CodegenContext& context;
    IRBuilder builder;
    flat_hash_map<const Symbol*, llvm::AllocaInst*> locals;
    llvm::AssertingVH<llvm::Instruction> localInsertPt;
    llvm::BasicBlock* breakTarget = nullptr;
    llvm::BasicBlock* continueTarget = nullptr;
    llvm::BasicBlock* returnBlock = nullptr;
    llvm::AllocaInst* returnVal = nullptr;
    llvm::Function* currentFunc = nullptr;
};

class CodeGenerator::Impl {
public:
    CodegenContext context;

    Impl(Compilation& compilation, CodegenOptions options);

    void emitSubroutine(const SubroutineSymbol& subroutine);
    void emitScope(const Scope& scope);

    std::string getTextualIR() const;
    std::string writeIRToFile(std::string_view path) const;
    std::string writeBitcodeToFile(std::string_view path) const;
};

} // namespace slang::codegen
