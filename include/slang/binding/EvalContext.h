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

enum class EvalFlags : uint8_t {
    None = 0,
    IsScript = 1,
    IsVerifying = 2
};
BITMASK_DEFINE_MAX_ELEMENT(EvalFlags, IsVerifying);

/// A container for all context required to evaluate a statement or expression.
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
    };

    explicit EvalContext(bitmask<EvalFlags> flags = {});

    /// Creates storage for a local variable in the current frame.
    ConstantValue* createLocal(const ValueSymbol* symbol, ConstantValue value = nullptr);

    /// Gets the current value for the given local variable symbol.
    /// Returns nullptr if the symbol cannot be found.
    ConstantValue* findLocal(const ValueSymbol* symbol);

    /// Push a new frame onto the call stack.
    void pushFrame(const SubroutineSymbol& subroutine, SourceLocation callLocation,
                   LookupLocation lookupLocation);

    /// Pop the active frame from the call stack.
    void popFrame();

    /// Indicates whether this evaluation context is for a script session
    /// (not used during normal compilation flow).
    bool isScriptEval() const { return (flags & EvalFlags::IsScript) != 0; }

    /// Indicates whether this context is for verifying const-ness
    /// without actually evaluating anything.
    bool isVerifying() const { return (flags & EvalFlags::IsVerifying) != 0; }

    /// Gets the top of the call stack.
    const Frame& topFrame() const { return stack.back(); }

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
    bitmask<EvalFlags> flags;
    bool reportedCallstack = false;
};

} // namespace slang