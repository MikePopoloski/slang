//------------------------------------------------------------------------------
// CodeGenTypes.h
// Conversion between SystemVerilog types and LLVM generated types
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>

namespace llvm {

class Type;

} // namespace llvm

namespace slang {

class CodeGenerator;
class Type;

class CodeGenTypes {
public:
    explicit CodeGenTypes(CodeGenerator& codegen);

    llvm::Type* convertType(const Type& type);

    llvm::Type* VoidType;
    llvm::Type* BoolType;
    llvm::Type* Int8Type;
    llvm::Type* Int32Type;
    llvm::Type* Int64Type;
    llvm::Type* BoxedIntType;

private:
    CodeGenerator& codegen;
    flat_hash_map<const Type*, llvm::Type*> typeMap;
};

} // namespace slang