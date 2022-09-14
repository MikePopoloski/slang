//------------------------------------------------------------------------------
//! @file DiagArgFormatter.h
//! @brief Interface for formatting custom diagnostic argument types
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <any>
#include <fmt/args.h>
#include <fmt/core.h>

namespace slang {

class Diagnostic;

using FormatArgStore = fmt::dynamic_format_arg_store<fmt::format_context>;

class DiagArgFormatter {
public:
    virtual ~DiagArgFormatter() {}

    virtual void startMessage(const Diagnostic&) {}
    virtual void format(FormatArgStore& argStore, const std::any& arg) = 0;
};

} // namespace slang
