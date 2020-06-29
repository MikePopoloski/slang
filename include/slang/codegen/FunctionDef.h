//------------------------------------------------------------------------------
//! @file FunctionDef.h
//! @brief Executable function definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace llvm {

class Function;
class Module;
class Type;

} // namespace llvm

namespace slang {

class CodeGenerator;

namespace mir {
enum class SysCallKind;
}

struct ParamDef {
    llvm::Type* nativeType;
};

class FunctionDef {
public:
    FunctionDef(const CodeGenerator& codegen, string_view name, llvm::Type* returnType,
                span<const ParamDef> params);

    span<const ParamDef> parameters() const { return params; }
    llvm::Function* getNative() const { return nativeFunc; }

    static FunctionDef getSystemFunc(CodeGenerator& codegen, mir::SysCallKind kind);

private:
    llvm::Function* nativeFunc;
    llvm::Type* returnType;
    string_view name;
    span<const ParamDef> params;
};

} // namespace slang