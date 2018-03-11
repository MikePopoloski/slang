//------------------------------------------------------------------------------
// EvalContext.cpp
// Expression evaluation context.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "EvalContext.h"

namespace slang {

ConstantValue LValue::load(EvalContext& context) const {
    // Find the root. TODO: handle concatenations
    auto symbol = std::get<const ValueSymbol*>(root);
    if (!symbol)
        return nullptr;

    ConstantValue* local = context.findLocal(symbol);
    if (!local)
        return nullptr;

    return *local;
}

void LValue::store(EvalContext& context, const ConstantValue& value) {
    // Find the root. TODO: handle concatenations
    auto symbol = std::get<const ValueSymbol*>(root);
    if (!symbol)
        return;

    ConstantValue* local = context.findLocal(symbol);
    if (!local)
        return;

    *local = value;
}

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