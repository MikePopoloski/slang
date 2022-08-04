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
#include "slang/types/AllTypes.h"

namespace slang {

CodeGenTypes::CodeGenTypes(CodeGenerator& codegen) : codegen(codegen) {
    // TODO: ABI concerns
    auto& ctx = codegen.getContext();
    Void = llvm::Type::getVoidTy(ctx);
    Int1 = llvm::Type::getInt1Ty(ctx);
    Int8 = llvm::Type::getInt8Ty(ctx);
    Int32 = llvm::Type::getInt32Ty(ctx);
    Int64 = llvm::Type::getInt64Ty(ctx);
    Size = Int64;
    Int8Ptr = llvm::Type::getInt8PtrTy(ctx);
    StringObj = llvm::StructType::get(Int8Ptr, Int64);
    BoxedInt = llvm::StructType::get(Int64, Int32, Int8, Int8);
}

AlignedType CodeGenTypes::convertType(const Type& type) {
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

    llvm::Type* lt;
    if (bits > codegen.getOptions().maxIntBits)
        lt = llvm::ArrayType::get(Int64, (bits + 63) / 64);
    else
        lt = llvm::Type::getIntNTy(codegen.getContext(), bits);

    // TODO: alignment
    AlignedType result{ lt, llvm::Align::Constant<8>() };
    typeMap.emplace(&type, result);
    return result;
}

} // namespace slang
