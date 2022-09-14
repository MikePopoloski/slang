//------------------------------------------------------------------------------
// CGExpr.cpp
// CodeGenFunction methods related to expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "CodeGenFunction.h"
#include "CodeGenTypes.h"

namespace slang {

llvm::Value* CodeGenFunction::emitNegate(const Type&, mir::MIRValue op) {
    llvm::Value* val = emit(op);
    return builder.CreateSub(llvm::Constant::getNullValue(val->getType()), val);
}

} // namespace slang
