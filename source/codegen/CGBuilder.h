//------------------------------------------------------------------------------
// CGBuilder.h
// Wrapper around LLVM IRBuilder
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4702) // unreachable code
#endif
#include <llvm/IR/IRBuilder.h>
#ifdef _MSC_VER
#    pragma warning(pop)
#endif

#include "CodeGenTypes.h"

#include "slang/util/Util.h"

namespace slang {

class Address {
public:
    Address(llvm::Value* pointer, llvm::Align align) : ptr(pointer), align(align) {}

    static Address invalid() { return Address(nullptr, llvm::Align()); }
    bool isValid() const { return ptr != nullptr; }
    explicit operator bool() const { return isValid(); }

    llvm::Value* getPointer() const {
        ASSERT(ptr);
        return ptr;
    }

    llvm::Align getAlignment() const { return align; }

private:
    llvm::Value* ptr;
    llvm::Align align;
};

class CGBuilder : public llvm::IRBuilder<llvm::ConstantFolder, llvm::IRBuilderDefaultInserter> {
public:
    CGBuilder(const CodeGenTypes& types, llvm::LLVMContext& ctx) : IRBuilder(ctx), types(types) {}

    llvm::ConstantInt* getSize(uint64_t n) { return llvm::ConstantInt::get(types.Size, n); }

    llvm::LoadInst* CreateLoad(Address addr, llvm::Type* type) {
        return CreateAlignedLoad(type, addr.getPointer(), addr.getAlignment());
    }

    llvm::StoreInst* CreateStore(llvm::Value* value, Address addr) {
        return CreateAlignedStore(value, addr.getPointer(), addr.getAlignment());
    }

    Address CreateStructGEP(llvm::Type* type, Address addr, unsigned index) {
        // Figure out the offset of the struct member so that we can know
        // the alignment of the GEP result address.
        llvm::StructType* elementType = llvm::cast<llvm::StructType>(type);
        const llvm::DataLayout& dl = BB->getParent()->getParent()->getDataLayout();
        const llvm::StructLayout* layout = dl.getStructLayout(elementType);

        uint64_t offset = layout->getElementOffset(index);
        llvm::Align align(llvm::MinAlign(addr.getAlignment().value(), offset));

        return Address(IRBuilder::CreateStructGEP(type, addr.getPointer(), index), align);
    }

    Address CreateConstArrayGEP(llvm::Type* type, Address addr, uint64_t index) {
        llvm::ArrayType* elementType = llvm::cast<llvm::ArrayType>(type);
        const llvm::DataLayout& dl = BB->getParent()->getParent()->getDataLayout();

        llvm::TypeSize size = dl.getTypeAllocSize(elementType->getElementType());
        llvm::Align align(llvm::MinAlign(addr.getAlignment().value(), size * index));

        llvm::Value* ptr = addr.getPointer();
        llvm::Type* ptrType = ptr->getType()->getScalarType()->getPointerElementType();
        return Address(CreateInBoundsGEP(ptrType, ptr, { getSize(0), getSize(index) }, ""), align);
    }

private:
    const CodeGenTypes& types;
};

} // namespace slang
