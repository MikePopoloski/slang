//------------------------------------------------------------------------------
// CGExpr.cpp
// CodeGenFunction methods related to expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "CodeGenFunction.h"
#include "CodeGenTypes.h"

namespace slang {

llvm::Value* CodeGenFunction::emitNegate(const Type&, mir::MIRValue op) {
    llvm::Value* val = emit(op);
    return builder.CreateSub(llvm::Constant::getNullValue(val->getType()), val);
}

} // namespace slang
