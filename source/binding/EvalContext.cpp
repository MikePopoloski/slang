//------------------------------------------------------------------------------
// EvalContext.cpp
// Expression evaluation context.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "EvalContext.h"

#include "fmt/format.h"

#include "symbols/MemberSymbols.h"
#include "symbols/TypeSymbols.h"

namespace slang {

EvalContext::EvalContext() {
    stack.emplace_back(Frame{});
}

ConstantValue* EvalContext::createLocal(const ValueSymbol* symbol, ConstantValue value) {
    ConstantValue& result = stack.back().temporaries[symbol];
    ASSERT(!result);

    if (!value)
        result = symbol->getType().getDefaultValue();
    else {
        // TODO: The provided initial value must be the correct bit width when it's an integer.
        //ASSERT(!value.isInteger() || value.integer().getBitWidth() == symbol->getType().getBitWidth());
        result = std::move(value);
    }

    return &result;
}

ConstantValue* EvalContext::findLocal(const ValueSymbol* symbol) {
    auto it = stack.back().temporaries.find(symbol);
    if (it == stack.back().temporaries.end())
        return nullptr;
    return &it->second;
}

void EvalContext::pushFrame(const SubroutineSymbol& subroutine) {
    Frame frame;
    frame.subroutine = &subroutine;
    stack.emplace_back(std::move(frame));
}

ConstantValue EvalContext::popFrame() {
    ConstantValue result;
    Frame& frame = stack.back();
    if (frame.subroutine) {
        ConstantValue* storage = findLocal(frame.subroutine->returnValVar);
        ASSERT(storage);
        result = std::move(*storage);
    }

    stack.pop_back();
    return result;
}

void EvalContext::setReturned(ConstantValue value) {
    Frame& frame = stack.back();
    frame.hasReturned = true;

    const SubroutineSymbol* subroutine = frame.subroutine;
    ASSERT(subroutine);

    ConstantValue* storage = findLocal(subroutine->returnValVar);
    ASSERT(storage);

    *storage = std::move(value);
}

std::string EvalContext::dumpStack() const {
    fmt::MemoryWriter writer;
    int index = 0;
    for (const Frame& frame : stack) {
        writer.write("{}: {}\n", index++, frame.subroutine ? frame.subroutine->name : "<global>");
        for (auto& [symbol, value] : frame.temporaries)
            writer.write("    {} = {}\n", symbol->name, value.toString());
    }
    return writer.str();
}

}