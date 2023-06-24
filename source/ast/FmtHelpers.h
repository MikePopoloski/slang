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

class FmtHelpers {
public:
    static bool checkDisplayArgs(const ASTContext& context,
                                 const std::span<const Expression* const>& args);

    static bool checkSFormatArgs(const ASTContext& context,
                                 const std::span<const Expression* const>& args);

    static std::optional<std::string> formatArgs(std::string_view formatString, SourceLocation loc,
                                                 const Scope& scope, EvalContext& context,
                                                 const std::span<const Expression* const>& args,
                                                 bool isStringLiteral);

    static std::optional<std::string> formatDisplay(const Scope& scope, EvalContext& context,
                                                    const std::span<const Expression* const>& args);

    static bool checkFinishNum(const ASTContext& context, const Expression& arg);

private:
    FmtHelpers() = default;
};

} // namespace slang::ast
