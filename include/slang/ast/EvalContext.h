//------------------------------------------------------------------------------
//! @file EvalContext.h
//! @brief Expression evaluation context
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <map>

#include "slang/ast/ASTContext.h"
#include "slang/numeric/ConstantValue.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/ScopeGuard.h"

namespace slang::ast {

class Compilation;
class LValue;
class SubroutineSymbol;
class ValueSymbol;

/// @brief A container for all context required to evaluate a statement or expression.
///
/// Mostly this involves tracking the callstack and maintaining
/// storage for local variables.
class SLANG_EXPORT EvalContext {
public:
    /// The AST context in which the evaluation is occurring.
    ASTContext astCtx;

    /// Flags that control evaluation.
    bitmask<EvalFlags> flags;

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

    /// Constructs a new EvalContext instance.
    explicit EvalContext(const ASTContext& astCtx, bitmask<EvalFlags> flags = {}) :
        astCtx(astCtx), flags(flags) {}

    /// Gets the compilation associated with the context.
    Compilation& getCompilation() const { return astCtx.getCompilation(); }

    /// Resets the evaluation context back to an initial constructed state.
    void reset();

    /// Creates storage for a local variable in the current frame.
    ConstantValue* createLocal(const ValueSymbol* symbol, ConstantValue value = nullptr);

    /// Gets the current value for the given local variable symbol.
    /// Returns nullptr if the symbol cannot be found.
    ConstantValue* findLocal(const ValueSymbol* symbol);

    /// Removes a previously created local. Pointers to the local's
    /// storage will be invalidated.
    void deleteLocal(const ValueSymbol* symbol);

    /// Push a new frame onto the call stack.
    [[nodiscard]] bool pushFrame(const SubroutineSymbol& subroutine, SourceLocation callLocation,
                                 LookupLocation lookupLocation);

    /// Pushes an empty frame onto the call stack. Intended for use with
    /// on-the-fly evaluation in a scripting context.
    void pushEmptyFrame();

    /// Pop the active frame from the call stack.
    void popFrame();

    /// Pushes an lvalue onto the stack for later reference during evaluation.
    /// NOTE: the lvalue storage must remain alive for as long as it remains
    /// on the eval context's lvalue stack.
    void pushLValue(LValue& lval);

    /// Pops the top of the lvalue stack (requires that the stack be non-empty).
    void popLValue();

    /// Gets the top of the lvalue stack, or nullptr if the stack is empty.
    LValue* getTopLValue() const;

    /// Records the fact that we are executing another statement. This is used to count
    /// the number of statements executed so far to detect if we've been evaluating
    /// a single constant function for too long.
    [[nodiscard]] bool step(SourceLocation loc);

    /// Returns true if the context is currently within a function call, and false if
    /// this is a top-level expression.
    bool inFunction() const { return !stack.empty(); }

    /// Indicates whether the results of evaluating expressions using this context
    /// can be cached in each expression's `constant` pointer.
    bool cacheResults() const { return !inFunction() && flags.has(EvalFlags::CacheResults); }

    /// If result caching is enabled, this method disables it and returns an
    /// object that when destructed will restore the previous caching mode.
    /// Otherwise does nothing.
    [[nodiscard]] auto disableCaching() {
        auto guard = ScopeGuard(
            [this, saved = flags.has(EvalFlags::CacheResults), pushed = !inFunction()] {
                if (pushed)
                    popFrame();

                if (saved)
                    flags |= EvalFlags::CacheResults;
                else
                    flags &= ~EvalFlags::CacheResults;
            });

        flags &= ~EvalFlags::CacheResults;
        if (!inFunction())
            pushEmptyFrame();

        return guard;
    }

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

    /// Sets the target queue value for use with unbounded '$' expressions.
    /// If set to nullptr, the target is cleared.
    void setQueueTarget(const ConstantValue* cv) { queueTarget = cv; }

    /// Gets the target queue value for use with unbounded '$' expressions.
    /// Returns nullptr if there is no queue target active.
    const ConstantValue* getQueueTarget() const { return queueTarget; }

    /// Dumps the contents of the call stack to a string for debugging.
    std::string dumpStack() const;

    /// Gets the set of diagnostics that have been produced during constant evaluation.
    Diagnostics getAllDiagnostics() const;

    /// Records a diagnostic under the current evaluation context.
    Diagnostic& addDiag(DiagCode code, SourceLocation location);

    /// Records a diagnostic under the current evaluation context.
    Diagnostic& addDiag(DiagCode code, SourceRange range);

    /// Issues all recorded diagnostics to the associated AST context.
    void reportAllDiags();

    /// Issues only warnings to the associated AST context.
    void reportWarnings();

    /// Reports the current function call stack as notes to the given diagnostic.
    void reportStack(Diagnostic& diag) const;

private:
    void reportDiags(Diagnostics& diagSet);

    uint32_t steps = 0;
    const Symbol* disableTarget = nullptr;
    const ConstantValue* queueTarget = nullptr;
    SmallVector<Frame> stack;
    SmallVector<LValue*> lvalStack;
    Diagnostics diags;
    Diagnostics warnings;
    SourceRange disableRange;
    bool backtraceReported = false;
};

} // namespace slang::ast
