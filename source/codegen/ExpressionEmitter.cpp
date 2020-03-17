//------------------------------------------------------------------------------
// ExpressionEmitter.cpp
// Code emitter for expression trees
// NOTE: Only included if slang is configured to use LLVM
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/codegen/ExpressionEmitter.h"

#include "slang/codegen/CodeGenerator.h"
#include "slang/symbols/ASTVisitor.h"

namespace slang {

ExpressionEmitter::ExpressionEmitter(CodeGenerator& generator, llvm::BasicBlock* bb) :
    generator(generator), ir(bb) {
}

llvm::Value* ExpressionEmitter::emit(const Expression& expr) {
    return expr.visit(*this);
}

llvm::Value* ExpressionEmitter::visit(const IntegerLiteral& expr) {
    return generator.genConstant(*expr.type, expr.getValue());
}

llvm::Value* ExpressionEmitter::visit(const CallExpression& expr) {
    return getUndef(*expr.type);
}

llvm::Value* ExpressionEmitter::getUndef(const Type& type) {
    return llvm::UndefValue::get(generator.genType(type));
}

} // namespace slang