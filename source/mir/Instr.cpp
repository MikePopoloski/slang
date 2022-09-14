//------------------------------------------------------------------------------
// Instr.cpp
// MIR instruction definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/mir/Instr.h"

#include "slang/mir/MIRPrinter.h"

namespace slang::mir {

span<const MIRValue> Instr::getOperands() const {
    switch (kind) {
        case InstrKind::syscall:
            return varOps;
        default:
            break;
    }
    return immOps;
}

} // namespace slang::mir
