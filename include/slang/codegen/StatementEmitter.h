//------------------------------------------------------------------------------
//! @file StatementEmitter.h
//! @brief Code emitter for statements
//! @note Only included if slang is configured to use LLVM
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/IRBuilder.h>

#include "slang/binding/Statements.h"

namespace slang {

class CodeGenerator;

class StatementEmitter {
public:
    StatementEmitter(CodeGenerator& generator, llvm::BasicBlock* bb);

    void emit(const Statement& stmt);

    // TODO: remove once all statements are handled
    template<typename T>
    void visit(const T&) {}

    void visit(const ExpressionStatement& stmt);

    void visitInvalid(const Statement&) {}

private:
    CodeGenerator& generator;
    llvm::IRBuilder<> ir;
};

} // namespace slang