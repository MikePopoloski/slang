//------------------------------------------------------------------------------
//! @file CodeGenerator.h
//! @brief Executable code generation
//! @note Only included if slang is configured to use LLVM
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <memory>
#include <string>

#include "slang/util/Util.h"

namespace llvm {

class LLVMContext;
class Module;

} // namespace llvm

namespace slang {

class Compilation;
class Symbol;

class CodeGenerator {
public:
    CodeGenerator(Compilation& compilation);
    ~CodeGenerator();

    std::string run(const Symbol& symbol);

private:
    std::unique_ptr<llvm::LLVMContext> ctx;
    std::unique_ptr<llvm::Module> module;
    Compilation& compilation;
};

} // namespace slang