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

namespace slang {

class CGBuilder : public llvm::IRBuilder<llvm::ConstantFolder, llvm::IRBuilderDefaultInserter> {
public:
    explicit CGBuilder(llvm::LLVMContext& ctx) : IRBuilder(ctx) {}
};

} // namespace slang