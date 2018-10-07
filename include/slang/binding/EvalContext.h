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

#include "slang/binding/ConstantValue.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/Symbol.h"

namespace slang {

class SubroutineSymbol;

/// A container for all context required to evaluate an expression.
/// Mostly this involves tracking the callstack and maintaining
/// storage for local variables.
class EvalContext {
public:
    /// Represents a single frame in the call stack.
    struct Frame {
        /// A set of temporary values materialized within the stack frame.
        /// Uses a map so that the values don't move around in memory.
        std::map<const ValueSymbol*, ConstantValue> temporaries;

        /// The function that is being executed in this frame, if any.
        const SubroutineSymbol* subroutine = nullptr;

        /// The source location of the function call site.
        SourceLocation callLocation;

        /// The lookup location of the function call site.
        LookupLocation lookupLocation;

        // TODO: remove this
        bool hasReturned = false;
    };

    explicit EvalContext(bool isScriptEval = false);

    /// Creates storage for a local variable in the current frame.
    ConstantValue* createLocal(const ValueSymbol* symbol, ConstantValue value = nullptr);

    /// Gets the current value for the given local variable symbol.
    /// Returns nullptr if the symbol cannot be found.
    ConstantValue* findLocal(const ValueSymbol* symbol);

    /// Push a new frame onto the call stack.
    void pushFrame(const SubroutineSymbol& subroutine, SourceLocation callLocation,
                   LookupLocation lookupLocation);

    /// Pop the active frame from the call stack and returns its value, if any.
    ConstantValue popFrame();

    /// Indicates whether this evaluation context is for a script session
    /// (not used during normal compilation flow).
    bool isScriptEval() const { return isScriptEval_; }

    /// Gets the top of the call stack.
    const Frame& topFrame() const { return stack.back(); }

    // TODO: get rid of this
    bool hasReturned() { return stack.back().hasReturned; }
    void setReturned(ConstantValue value);

    /// Dumps the contents of the call stack to a string for debugging.
    std::string dumpStack() const;

    /// Gets the set of diagnostics that have been produced during constant evaluation.
    const Diagnostics& getDiagnostics() const { return diags; }

    /// Reports a diagnostic under the current evaluation context.
    Diagnostic& addDiag(DiagCode code, SourceLocation location);
    Diagnostic& addDiag(DiagCode code, SourceRange range);

private:
    void reportStack();

    std::deque<Frame> stack;
    Diagnostics diags;
    bool reportedCallstack = false;
    bool isScriptEval_ = false;
};

} // namespace slang