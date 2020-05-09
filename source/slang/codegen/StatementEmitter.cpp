//------------------------------------------------------------------------------
// StatementEmitter.cpp
// Code emitter for statements
// NOTE: Only included if slang is configured to use LLVM
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/codegen/StatementEmitter.h"

#include "slang/codegen/CodeGenerator.h"
#include "slang/symbols/ASTVisitor.h"

namespace slang {

StatementEmitter::StatementEmitter(CodeGenerator& generator, llvm::BasicBlock* bb) :
    generator(generator), ir(bb) {
}

void StatementEmitter::emit(const Statement& stmt) {
    stmt.visit(*this);
}

void StatementEmitter::visit(const ExpressionStatement& stmt) {
    generator.genExpr(ir.GetInsertBlock(), stmt.expr);
}

} // namespace slang