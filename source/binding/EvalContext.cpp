//------------------------------------------------------------------------------
// EvalContext.cpp
// Expression evaluation context.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "EvalContext.h"

namespace slang {

EvalContext::EvalContext() {
    stack.emplace(Frame{});
}

ConstantValue* EvalContext::createLocal(const Symbol* symbol, ConstantValue value) {
    ConstantValue& result = stack.top().temporaries[symbol];
    ASSERT(!result);
    result = std::move(value);
    return &result;
}

ConstantValue* EvalContext::findLocal(const Symbol* symbol) {
    auto it = stack.top().temporaries.find(symbol);
    if (it == stack.top().temporaries.end())
        return nullptr;
    return &it->second;
}

void EvalContext::pushFrame() {
    stack.emplace(Frame{});
}

ConstantValue EvalContext::popFrame() {
    ConstantValue result = stack.top().returnValue;
    stack.pop();
    return result;
}

}