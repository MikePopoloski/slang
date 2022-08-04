//------------------------------------------------------------------------------
// Instr.cpp
// MIR instruction definitions
//
// File is under the MIT license; see LICENSE for details
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
