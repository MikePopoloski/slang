//------------------------------------------------------------------------------
//! @file CodeGenerator.h
//! @brief Executable code generation
//! @note Only included if slang is configured to use LLVM
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <string>

namespace slang {

class Symbol;

class CodeGenerator {
public:
    std::string run(const Symbol& symbol);
};

} // namespace slang