//------------------------------------------------------------------------------
// CodeGenTypes.cpp
// Conversion between SystemVerilog types and LLVM generated types
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "CodeGenTypes.h"

#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Module.h>

#include "slang/codegen/CodeGenerator.h"
#include "slang/symbols/AllTypes.h"

namespace slang {

CodeGenTypes::CodeGenTypes(CodeGenerator& codegen) : codegen(codegen) {
    auto& ctx = codegen.getContext();
    VoidType = llvm::Type::getVoidTy(ctx);
    BoolType = llvm::Type::getInt1Ty(ctx);
    Int8Type = llvm::Type::getInt8Ty(ctx);
    Int32Type = llvm::Type::getInt32Ty(ctx);
    Int64Type = llvm::Type::getInt64Ty(ctx);

    // All boxed integers use this type. It needs to pass across FFI calls,
    // so there should probably be more ABI logic here.
    BoxedIntType = llvm::StructType::get(Int64Type, Int32Type, llvm::ArrayType::get(Int8Type, 4));
}

llvm::Type* CodeGenTypes::convertType(const Type& type) {
    // Unwrap aliases.
    if (type.isAlias())
        return convertType(type.getCanonicalType());

    // Check the cache.
    if (auto it = typeMap.find(&type); it != typeMap.end())
        return it->second;

    // TODO: handle other types
    if (!type.isIntegral())
        THROW_UNREACHABLE;

    // Underlying representation for integer types:
    // - Two state types: use the bitwidth as specified
    // - Four state types: double the specified bitwidth,
    //                     the upper bits indicate a 1 for unknowns
    // - If the actual width > configured limit, switch to an array of bytes
    auto& intType = type.as<IntegralType>();
    uint32_t bits = intType.bitWidth;
    if (intType.isFourState)
        bits *= 2;

    llvm::Type* result;
    if (bits > codegen.getOptions().maxIntBits)
        result = llvm::ArrayType::get(Int64Type, (bits + 63) / 64);
    else
        result = llvm::Type::getIntNTy(codegen.getContext(), bits);

    typeMap.emplace(&type, result);
    return result;
}

} // namespace slang