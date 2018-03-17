//------------------------------------------------------------------------------
// EvalContext.h
// Expression evaluation context.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <map>
#include <stack>
#include <vector>

#include "binding/ConstantValue.h"
#include "symbols/Symbol.h"

namespace slang {

/// A container for all context required to evaluate an expression.
/// Mostly this involves tracking the callstack and maintaining
/// storage for local variables.
class EvalContext {
public:
    EvalContext();

    /// Creates storage for a local variable in the current frame.
    ConstantValue* createLocal(const Symbol* symbol, ConstantValue value);

    /// Gets the current value for the given local variable symbol.
    /// Returns nullptr if the symbol cannot be found.
    ConstantValue* findLocal(const Symbol* symbol);

    /// Push a new frame onto the call stack.
    void pushFrame();

    /// Pop the active frame from the call stack and returns its value, if any.
    ConstantValue popFrame();

    // TODO: get rid of this
    bool hasReturned() { return stack.top().hasReturned; }
    void setReturned(ConstantValue value) { stack.top().hasReturned = true; stack.top().returnValue = std::move(value); }

private:
    // Represents a single frame in the call stack.
    struct Frame {
        // A set of temporary values materialized within the stack frame.
        // Use a map so that the values don't move around in memory.
        std::map<const Symbol*, ConstantValue> temporaries;

        // Set to non-null when a return has been issued in this frame.
        ConstantValue returnValue;
        bool hasReturned = false;
    };

    std::stack<Frame> stack;
};

}