//------------------------------------------------------------------------------
//! @file CodeGenerator.h
//! @brief Top-level code generation API
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <memory>
#include <string>
#include <string_view>
#include <vector>

#include "slang/util/Util.h"

namespace slang::ast {

class Compilation;
class Scope;
class SubroutineSymbol;

} // namespace slang::ast

namespace slang::codegen {

/// Options that control code generation.
struct SLANG_EXPORT CodegenOptions {
    /// If true, run optimization passes before emitting.
    bool optimize = false;

    /// If true, attach debug information to the generated IR.
    bool debugInfo = false;
};

/// @brief Entry point for code generation.
class SLANG_EXPORT CodeGenerator {
public:
    /// Constructs a code generator for @a compilation.
    explicit CodeGenerator(ast::Compilation& compilation, CodegenOptions options = {});
    ~CodeGenerator();

    CodeGenerator(CodeGenerator&&) noexcept;
    CodeGenerator& operator=(CodeGenerator&&) noexcept;

    /// Emits IR for a single subroutine.
    void emitSubroutine(const ast::SubroutineSymbol& subroutine);

    /// Emits IR for every subroutine that is a direct member of @a scope.
    void emitScope(const ast::Scope& scope);

    /// Returns the generated IR as a human-readable string.
    [[nodiscard]] std::string getTextualIR() const;

    /// Writes the textual IR to the given file path.
    /// @returns an error message on failure, or an empty string on success.
    [[nodiscard]] std::string writeIRToFile(std::string_view path) const;

    /// Writes the bitcode to the given file path.
    /// @returns an error message on failure, or an empty string on success.
    [[nodiscard]] std::string writeBitcodeToFile(std::string_view path) const;

private:
    friend class JIT;

    class Impl;
    std::unique_ptr<Impl> impl;
};

} // namespace slang::codegen
