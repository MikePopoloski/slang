//------------------------------------------------------------------------------
//! @file JIT.h
//! @brief LLVM-based JIT compilation engine for SystemVerilog subroutines
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <expected.hpp>
#include <memory>
#include <string>
#include <string_view>

#include "slang/util/Util.h"

namespace slang::codegen {

class CodeGenerator;

/// @brief JIT compilation engine for SystemVerilog subroutines.
///
/// A JIT takes ownership of a @ref CodeGenerator's IR module, compiles it to
/// native machine code on demand, and allows the caller to look up compiled
/// functions and invoke them via plain C function pointers.
///
class SLANG_EXPORT JIT {
public:
    /// Creates a JIT engine from a CodeGenerator.
    ///
    /// Ownership of the generated IR module is transferred from @a gen into
    /// the new JIT engine. The @a gen object must not be used after this call.
    ///
    /// @returns the ready-to-use JIT on success, or an error description on failure.
    static nonstd::expected<JIT, std::string> create(CodeGenerator&& gen);

    ~JIT();
    JIT(JIT&&) noexcept;
    JIT& operator=(JIT&&) noexcept;

    /// Looks up a JIT-compiled function by its unmangled IR name.
    ///
    /// The returned pointer is valid for the lifetime of the JIT object.
    /// Calling the function after the JIT is destroyed is undefined behaviour.
    ///
    /// @returns the function's native code address cast to @c void*, or an
    ///          error description on failure.
    nonstd::expected<void*, std::string> lookup(std::string_view name);

    /// Looks up a JIT-compiled function by its unmangled IR name,
    /// calls it, and returns the result as a string.
    ///
    /// The function must not take any arguments and must return a simple
    /// return type (or void) for which we know how to translate and stringify.
    ///
    /// @returns the result of calling the function, or an error description on failure.
    nonstd::expected<std::string, std::string> runFunction(std::string_view name);

private:
    JIT();

    class Impl;
    std::unique_ptr<Impl> impl;
};

} // namespace slang::codegen
