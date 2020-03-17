//------------------------------------------------------------------------------
//! @file SystemCallEmitter.h
//! @brief Code emitter for system calls (tasks and functions)
//! @note Only included if slang is configured to use LLVM
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/IRBuilder.h>

#include "slang/util/Util.h"

namespace slang {

class CodeGenerator;
class Expression;
class Scope;
class SystemSubroutine;

class SystemCallEmitter {
public:
private:
};

} // namespace slang