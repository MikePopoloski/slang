//------------------------------------------------------------------------------
//! @file ExpressionEmitter.h
//! @brief Code emitter for expression trees
//! @note Only included if slang is configured to use LLVM
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/IRBuilder.h>

#include "slang/symbols/ASTVisitor.h"

namespace slang {

class CodeGenerator;

class ExpressionEmitter {
public:
    ExpressionEmitter(CodeGenerator& generator, llvm::BasicBlock* bb);

    llvm::Value* emit(const Expression& expr);

    // TODO: remove once all expressions are handled
    template<typename T>
    llvm::Value* visit(const T& expr) { return getUndef(*expr.type); }

    llvm::Value* visit(const IntegerLiteral& expr);
    llvm::Value* visit(const CallExpression& expr);

    llvm::Value* visitInvalid(const Expression&) { return ir.CreateUnreachable(); }

private:
    llvm::Value* getUndef(const Type& type);

    CodeGenerator& generator;
    llvm::IRBuilder<> ir;
};

} // namespace slang