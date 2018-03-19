//------------------------------------------------------------------------------
// EvalContext.cpp
// Expression evaluation context.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "EvalContext.h"

#include "symbols/MemberSymbols.h"
#include "symbols/TypeSymbols.h"

namespace slang {

EvalContext::EvalContext() {
    stack.emplace(Frame{});
}

ConstantValue* EvalContext::createLocal(const ValueSymbol* symbol, ConstantValue value) {
    ConstantValue& result = stack.top().temporaries[symbol];
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
    auto it = stack.top().temporaries.find(symbol);
    if (it == stack.top().temporaries.end())
        return nullptr;
    return &it->second;
}

void EvalContext::pushFrame(const SubroutineSymbol& subroutine) {
    Frame frame;
    frame.subroutine = &subroutine;
    stack.emplace(std::move(frame));
}

ConstantValue EvalContext::popFrame() {
    ConstantValue result;
    Frame& frame = stack.top();
    if (frame.subroutine) {
        ConstantValue* storage = findLocal(frame.subroutine->returnValVar);
        ASSERT(storage);
        result = std::move(*storage);
    }

    stack.pop();
    return result;
}

void EvalContext::setReturned(ConstantValue value) {
    Frame& frame = stack.top();
    frame.hasReturned = true;

    const SubroutineSymbol* subroutine = frame.subroutine;
    ASSERT(subroutine);

    ConstantValue* storage = findLocal(subroutine->returnValVar);
    ASSERT(storage);

    *storage = std::move(value);
}

}