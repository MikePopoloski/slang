//------------------------------------------------------------------------------
//! @file EvalContext.h
//! @brief Expression evaluation context
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <map>
#include <stack>
#include <vector>

#include "slang/numeric/ConstantValue.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/Symbol.h"

namespace slang {

class BindContext;
class SubroutineSymbol;

enum class EvalFlags : uint8_t { None = 0, IsScript = 1, IsVerifying = 2 };
BITMASK(EvalFlags, IsVerifying);

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

    explicit EvalContext(const Compilation& compilation, bitmask<EvalFlags> flags = {});

    /// Creates storage for a local variable in the current frame.
    ConstantValue* createLocal(const ValueSymbol* symbol, ConstantValue value = nullptr);

    /// Gets the current value for the given local variable symbol.
    /// Returns nullptr if the symbol cannot be found.
    ConstantValue* findLocal(const ValueSymbol* symbol);

    /// Push a new frame onto the call stack.
    [[nodiscard]] bool pushFrame(const SubroutineSymbol& subroutine, SourceLocation callLocation,
                                 LookupLocation lookupLocation);

    /// Pop the active frame from the call stack.
    void popFrame();

    /// Records the fact that we are executing another statement. This is used to count
    /// the number of statements executed so far to detect if we've been evaluating
    /// a single constant function for too long.
    [[nodiscard]] bool step(SourceLocation loc);

    /// Indicates whether this evaluation context is for a script session
    /// (not used during normal compilation flow).
    bool isScriptEval() const { return (flags & EvalFlags::IsScript) != 0; }

    /// Indicates whether this context is for verifying const-ness
    /// without actually evaluating anything.
    bool isVerifying() const { return (flags & EvalFlags::IsVerifying) != 0; }

    /// Gets the top of the call stack.
    const Frame& topFrame() const { return stack.back(); }

    /// If a disable statement has been evaluated, this returns a pointer to the
    /// block that should be disabled (presumed to be higher up in the stack).
    /// Otherwise returns nullptr.
    const Symbol* getDisableTarget() const { return disableTarget; }

    /// If a disable statement has been evaluated, this returns the source
    /// range denoting where that statement occurred. Otherwise returns an empty range.
    SourceRange getDisableRange() const { return disableRange; }

    /// Sets the target block that should be disabled, based on evaluating a
    /// disable statement. This can be set to nullptr to clear out the target
    /// once it has been found the disable is completed.
    void setDisableTarget(const Symbol* symbol, SourceRange range) {
        disableTarget = symbol;
        disableRange = range;
    }

    /// Dumps the contents of the call stack to a string for debugging.
    std::string dumpStack() const;

    /// Gets the set of diagnostics that have been produced during constant evaluation.
    const Diagnostics& getDiagnostics() const { return diags; }

    /// Records a diagnostic under the current evaluation context.
    Diagnostic& addDiag(DiagCode code, SourceLocation location);
    Diagnostic& addDiag(DiagCode code, SourceRange range);
    void addDiags(const Diagnostics& diags);

    /// Issues all recorded diagnostics to the given binding context.
    void reportDiags(const BindContext& context);

    /// Reports the current function call stack as notes to the given diagnostic.
    void reportStack(Diagnostic& diag) const;

private:
    const Compilation& compilation;
    uint32_t steps = 0;
    bitmask<EvalFlags> flags;
    const Symbol* disableTarget = nullptr;
    SmallVectorSized<Frame, 4> stack;
    Diagnostics diags;
    SourceRange disableRange;
};

} // namespace slang