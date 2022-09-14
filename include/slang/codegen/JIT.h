//------------------------------------------------------------------------------
//! @file JIT.h
//! @brief Just-in-time code execution
//! @note Only included if slang is configured to use LLVM
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/codegen/CodeGenerator.h"

namespace llvm {
namespace orc {
class LLLazyJIT;
}
} // namespace llvm

namespace slang {

class JIT {
public:
    JIT();
    ~JIT();

    void addCode(GeneratedCode code);
    int run();

private:
    std::unique_ptr<llvm::orc::LLLazyJIT> jit;
};

} // namespace slang
