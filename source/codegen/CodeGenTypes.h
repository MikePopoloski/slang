//------------------------------------------------------------------------------
// CodeGenTypes.h
// Conversion between SystemVerilog types and LLVM generated types
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>

namespace llvm {

class IntegerType;
class PointerType;
class StructType;
class Type;

} // namespace llvm

namespace slang {

class CodeGenerator;
class Type;

class CodeGenTypes {
public:
    explicit CodeGenTypes(CodeGenerator& codegen);

    llvm::Type* convertType(const Type& type);

    llvm::Type* Void;
    llvm::IntegerType* Int1;
    llvm::IntegerType* Int8;
    llvm::IntegerType* Int32;
    llvm::IntegerType* Int64;
    llvm::IntegerType* Size;
    llvm::PointerType* Int8Ptr;
    llvm::StructType* StringObj;
    llvm::StructType* BoxedInt;

private:
    CodeGenerator& codegen;
    flat_hash_map<const Type*, llvm::Type*> typeMap;
};

} // namespace slang