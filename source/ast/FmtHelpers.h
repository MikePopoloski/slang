//------------------------------------------------------------------------------
// FmtHelpers.h
// Helpers for implementing the string formatting system functions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <optional>
#include <span>
#include <string>

#include "slang/text/SourceLocation.h"

namespace slang::ast {

class ASTContext;
class Expression;
class EvalContext;
class Scope;

/// A collection of static helper methods for implementing
/// string formatting system functions and tasks.
class FmtHelpers {
public:
    /// Performs correctness checking of %display style
    /// system task arguments.
    static bool checkDisplayArgs(const ASTContext& context,
                                 const std::span<const Expression* const>& args);

    /// Performs correctness checking of $sformatf style
    /// system function arguments.
    static bool checkSFormatArgs(const ASTContext& context,
                                 const std::span<const Expression* const>& args);

    /// Formats the given arguments according to the provided format string.
    /// This is the implementation of the $sformatf system function.
    static std::optional<std::string> formatArgs(std::string_view formatString,
                                                 const Expression& formatExpr, const Scope& scope,
                                                 EvalContext& context,
                                                 const std::span<const Expression* const>& args);

    /// Formats the given arguments as if they were provided to a $display style
    /// system task or function.
    static std::optional<std::string> formatDisplay(const Scope& scope, EvalContext& context,
                                                    const std::span<const Expression* const>& args);

    /// Performs correctness checking for the "finish number" argument of several
    /// system tasks (e.g. $finish).
    static void checkFinishNum(const ASTContext& context, const Expression& arg);

private:
    FmtHelpers() = default;
};

} // namespace slang::ast
