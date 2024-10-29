//------------------------------------------------------------------------------
//! @file DiagArgFormatter.h
//! @brief Interface for formatting custom diagnostic argument types
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <any>
#include <string>

#include "slang/slang_export.h"

namespace slang {

class Diagnostic;

class SLANG_EXPORT DiagArgFormatter {
public:
    virtual ~DiagArgFormatter() {}

    virtual void startMessage(const Diagnostic&) {}
    virtual std::string format(const std::any& arg) = 0;
};

} // namespace slang
