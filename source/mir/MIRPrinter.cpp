//------------------------------------------------------------------------------
// MIRPrinter.cpp
// MIR pretty printing
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/mir/MIRPrinter.h"

#include <fmt/format.h>

#include "slang/symbols/Type.h"

namespace {

using namespace slang::mir;

// clang-format off
string_view instrName(InstrKind kind) {
    switch (kind) {
        case InstrKind::Invalid: return "<invalid>"sv;
        case InstrKind::SysCall: return "syscall"sv;
    }
    THROW_UNREACHABLE;
}

string_view syscallName(SysCallKind kind) {
    switch (kind) {
        case SysCallKind::PrintChar: return "$printChar"sv;
    }
    THROW_UNREACHABLE;
}
// clang-format on

} // namespace

namespace slang::mir {

MIRPrinter& MIRPrinter::print(const Procedure& proc) {
    size_t index = 0;
    for (auto& instr : proc.getInstructions()) {
        print(instr, index++);
        buffer += '\n';
    }
    return *this;
}

MIRPrinter& MIRPrinter::print(const Instr& instr, size_t index) {
    buffer += fmt::format("%{} = {}", index, instrName(instr.kind));

    if (instr.kind == InstrKind::SysCall) {
        buffer += ' ';
        buffer += syscallName(instr.getSysCallKind());
    }

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
            buffer += fmt::format("{}: {}", tcv.type.toString(), tcv.value.toString());
            break;
        }
        case MIRValue::Slot:
            buffer += fmt::format("%{}", value.asInstrSlot());
            break;
        default:
            break;
    }
    return *this;
}

} // namespace slang::mir