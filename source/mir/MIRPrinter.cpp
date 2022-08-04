//------------------------------------------------------------------------------
// MIRPrinter.cpp
// MIR pretty printing
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/mir/MIRPrinter.h"

#include <fmt/format.h>

#include "slang/symbols/VariableSymbols.h"
#include "slang/types/Type.h"

namespace slang::mir {

MIRPrinter& MIRPrinter::print(const Procedure& proc) {
    size_t index = 0;
    for (auto& local : proc.getLocals()) {
        buffer += fmt::format("L{} {}: {}", index++, local->name, local->getType().toString());
        buffer += '\n';
    }

    index = 0;
    for (auto& instr : proc.getInstructions()) {
        print(instr, index++);
        buffer += '\n';
    }

    return *this;
}

MIRPrinter& MIRPrinter::print(const Instr& instr, size_t index) {
    buffer += fmt::format("%{} = {}", index, toString(instr.kind));

    if (instr.kind == InstrKind::syscall)
        buffer += fmt::format(" ${}", toString(instr.getSysCallKind()));

    auto ops = instr.getOperands();
    if (!ops.empty()) {
        buffer += ' ';
        for (auto& op : ops) {
            print(op);
            buffer += ", "sv;
        }
        buffer.resize(buffer.size() - 2);
    }

    return *this;
}

MIRPrinter& MIRPrinter::print(const MIRValue& value) {
    switch (value.getKind()) {
        case MIRValue::Constant: {
            auto& tcv = value.asConstant();
            buffer += fmt::format("{}: {}", tcv.value.toString(), tcv.type.toString());
            break;
        }
        case MIRValue::InstrSlot:
            buffer += fmt::format("%{}", value.asIndex());
            break;
        case MIRValue::Local:
            buffer += fmt::format("L{}", value.asIndex());
            break;
        case MIRValue::Global:
            buffer += fmt::format("G{}[{}]", value.asIndex(), builder.getGlobal(value).name);
            break;
        default:
            break;
    }
    return *this;
}

MIRPrinter& MIRPrinter::printGlobals() {
    size_t index = 0;
    for (auto& global : builder.getGlobals()) {
        buffer += fmt::format("G{} {}: {}", index++, global->name, global->getType().toString());
        buffer += '\n';
    }
    return *this;
}

} // namespace slang::mir
