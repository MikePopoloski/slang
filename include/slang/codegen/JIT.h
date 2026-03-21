//------------------------------------------------------------------------------
//! @file JIT.h
//! @brief LLVM-based JIT compilation engine for SystemVerilog subroutines
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <expected.hpp>
#include <filesystem>
#include <memory>
#include <span>
#include <string>
#include <string_view>

#include "slang/numeric/ConstantValue.h"
#include "slang/util/Util.h"

namespace slang::ast {
class SubroutineSymbol;
}

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

    /// Links a native library file into the JIT engine.
    ///
    /// @a path must point to one of:
    ///   - a compiled object file (.o on Unix, .obj on Windows)
    ///   - an LLVM bitcode file (.bc)
    ///   - a static archive (.a or .lib)
    ///   - a shared/dynamic library (.so, .dll, or .dylib)
    ///
    /// This must be called before the first call to @ref lookup or @ref runFunction
    /// so that symbols from the library are available for JIT linking.
    ///
    /// @returns an empty string on success, or an error description on failure.
    [[nodiscard]] std::string linkLibrary(const std::filesystem::path& path);

    /// Looks up a JIT-compiled function by its unmangled IR name.
    ///
    /// The returned pointer is valid for the lifetime of the JIT object.
    /// Calling the function after the JIT is destroyed is undefined behaviour.
    ///
    /// @returns the function's native code address cast to @c void*, or an
    ///          error description on failure.
    nonstd::expected<void*, std::string> lookup(std::string_view name);

    /// Looks up a JIT-compiled DPI-exported function by its C identifier,
    /// calls it with the given arguments, and returns the result as a ConstantValue.
    ///
    /// The function must be a DPI-exported function whose argument and return
    /// types are compatible with the DPI calling convention.
    ///
    /// @returns the result of calling the function, or an error description on failure.
    nonstd::expected<ConstantValue, std::string> runFunction(std::string_view name,
                                                             std::span<const ConstantValue> args);

private:
    JIT();

    nonstd::expected<std::string, std::string> createTrampoline(
        std::string_view funcName, const ast::SubroutineSymbol& target,
        std::span<const ConstantValue> args);

    class Impl;
    std::unique_ptr<Impl> impl;
};

} // namespace slang::codegen
