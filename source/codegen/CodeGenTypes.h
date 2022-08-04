//------------------------------------------------------------------------------
// CodeGenTypes.h
// Conversion between SystemVerilog types and LLVM generated types
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <llvm/Support/Alignment.h>

#include "slang/util/Hash.h"

namespace llvm {

class IntegerType;
class PointerType;
class StructType;
class Type;

} // namespace llvm

namespace slang {

class CodeGenerator;
class Type;

struct AlignedType {
    llvm::Type* type;
    llvm::Align alignment;
};

class CodeGenTypes {
public:
    explicit CodeGenTypes(CodeGenerator& codegen);

    AlignedType convertType(const Type& type);

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
    flat_hash_map<const Type*, AlignedType> typeMap;
};

} // namespace slang
