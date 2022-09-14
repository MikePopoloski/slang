//------------------------------------------------------------------------------
//! @file MIRPrinter.h
//! @brief MIR pretty printing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <string>

#include "slang/mir/Procedure.h"

namespace slang::mir {

class MIRPrinter {
public:
    explicit MIRPrinter(const MIRBuilder& builder) : builder(builder) {}

    MIRPrinter& print(const Procedure& proc);
    MIRPrinter& print(const Instr& instr, size_t index);
    MIRPrinter& print(const MIRValue& value);

    MIRPrinter& printGlobals();

    std::string& str() { return buffer; }
    const std::string& str() const { return buffer; }

private:
    const MIRBuilder& builder;
    std::string buffer;
};

} // namespace slang::mir
