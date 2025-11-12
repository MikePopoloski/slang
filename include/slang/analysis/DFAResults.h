//------------------------------------------------------------------------------
//! @file DFAResults.h
//! @brief Results of running data flow analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Function.h"
#include "slang/util/IntervalMap.h"
#include "slang/util/SmallMap.h"
#include "slang/util/SmallVector.h"

namespace slang::ast {

class CallExpression;
class EvalContext;
class Expression;
class Statement;
class Symbol;
class TimingControl;
class ValueSymbol;

} // namespace slang::ast

namespace slang::analysis {

class AnalysisContext;
class AnalyzedProcedure;

using SymbolBitMap = IntervalMap<uint64_t, std::monostate, 3>;
using SymbolLSPMap = IntervalMap<uint64_t, const ast::Expression*, 5>;

/// Contains the results of running data flow analysis on a procedure.
///
/// Derived classes must perform the walking of the procedure body and
/// fill out various bits of information that is then queried during
/// creation of AnalyzedProcedures.
class SLANG_EXPORT DFAResults {
public:
    /// Set to true if the procedure has any return statements.
    bool hasReturnStatements = false;

    /// Set to true if the end of the procedure is reachable by at
    /// least one control flow path.
    bool endIsReachable = false;

    /// Gets all of the analyzed statements that have timing controls
    /// associated with them.
    std::span<const ast::Statement* const> getTimedStatements() const { return timedStatements; }

    /// Gets all of the concurrent assertions, procedural checkers, and assertion
    /// instance expressions in the procedure.
    std::span<std::variant<const ast::Statement*, const ast::Expression*> const> getAssertions()
        const {
        return concurrentAssertions;
    }

    /// Gets all of the subroutine calls in the procedure.
    std::span<const ast::CallExpression* const> getCallExpressions() const {
        return callExpressions;
    }

    /// Determines whether the given symbol is referenced anywhere in
    /// the procedure, either as an lvalue or an rvalue.
    bool isReferenced(const ast::ValueSymbol& symbol) const {
        return symbolToSlot.contains(&symbol) || rvalues.contains(&symbol);
    }

    /// Determines whether the given subset of the symbol (via the provided
    /// longest static prefix expression) is referenced anywhere in
    /// the procedure, either as an lvalue or an rvalue.
    bool isReferenced(ast::EvalContext& evalContext, const ast::ValueSymbol& symbol,
                      const ast::Expression& lsp) const;

    /// Gets the inferred clock for the procedure, if one exists.
    const ast::TimingControl* inferClock(AnalysisContext& context, const ast::Symbol& symbol,
                                         ast::EvalContext& evalContext,
                                         const AnalyzedProcedure* parentProcedure) const;

    /// Returns true if the given symbol is definitely assigned at the current point.
    bool isDefinitelyAssigned(const ast::ValueSymbol& symbol) const;

    using AssignedSymbolCB = function_ref<void(const ast::Symbol&, const ast::Expression&)>;

    /// Visits all of the symbols that are assigned anywhere in the procedure
    /// and aren't definitely assigned by the end of the procedure.
    void visitPartiallyAssigned(bool skipAutomatic, AssignedSymbolCB cb) const;

    /// Visits all of the symbols (and LSP ranges) that are definitely assigned at
    /// the current point in the procedure.
    void visitDefinitelyAssigned(bool skipAutomatic, AssignedSymbolCB cb) const;

    /// Tracks assigned ranges of symbols used as lvalues in the procedure.
    struct LValueSymbol {
        /// The symbol used as an lvalue.
        not_null<const ast::ValueSymbol*> symbol;

        /// The assigned bit ranges of the symbol.
        SymbolLSPMap assigned;

        LValueSymbol(const ast::ValueSymbol& symbol) : symbol(&symbol) {}
    };

    /// Gets all of the lvalues used in the procedure.
    std::span<const LValueSymbol> getLValues() const { return lvalues; }

protected:
    DFAResults(AnalysisContext& context, const SmallVectorBase<SymbolBitMap>& stateRef);

    /// An allocator for assigned symbol bit ranges.
    SymbolBitMap::allocator_type bitMapAllocator;

    /// An allocator for assigned symbol LSP ranges.
    SymbolLSPMap::allocator_type lspMapAllocator;

    /// Maps visited symbols to slots in assigned vectors.
    SmallMap<const ast::ValueSymbol*, uint32_t, 4> symbolToSlot;

    /// Tracks the assigned ranges of each variable across the entire procedure,
    /// even if not all branches assign to it.
    SmallVector<LValueSymbol> lvalues;

    /// All of the nets and variables that have been read in the procedure.
    SmallMap<const ast::ValueSymbol*, SymbolBitMap, 4> rvalues;

    /// All statements that have timing controls associated with them.
    SmallVector<const ast::Statement*> timedStatements;

    /// All concurrent assertions, checkers, and assertion instance expressions in the procedure.
    SmallVector<std::variant<const ast::Statement*, const ast::Expression*>> concurrentAssertions;

    /// All call expressions in the procedure.
    SmallVector<const ast::CallExpression*> callExpressions;

    /// The currently assigned state of symbols.
    not_null<const SmallVectorBase<SymbolBitMap>*> stateRef;
};

} // namespace slang::analysis
