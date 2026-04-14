//------------------------------------------------------------------------------
//! @file AnalyzedProcedure.h
//! @brief Analysis support for procedures
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <span>

#include "slang/analysis/AnalyzedAssertion.h"
#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang::ast {

class CallExpression;
class EvalContext;
class Statement;
class SubroutineSymbol;
class Symbol;
class TimingControl;
class ValueSymbol;

} // namespace slang::ast

namespace slang::analysis {

class AnalysisContext;
class DFAResults;
class ValueDriver;

/// A bit range read from a symbol within a procedure.
struct ReadRange {
    /// The symbol being read.
    not_null<const ast::ValueSymbol*> symbol;

    /// The bit range of the symbol being read.
    std::pair<uint64_t, uint64_t> bitRange;
};

/// Describes the effective sensitivity list for a SystemVerilog procedure.
///
/// The sensitivity list represents the set of signals that, when they change,
/// cause the procedure to re-evaluate.
struct SensitivityList {
    /// The kind of sensitivity list.
    enum class Kind {
        /// No event-based sensitivity: the procedure runs unconditionally
        /// (e.g. @c initial, @c final) or has no event timing control.
        None,

        /// Explicit sensitivity list specified in source
        /// (e.g. @c always_ff \@(posedge clk) or @c always \@(a or b)).
        Explicit,

        /// Implicit sensitivity list derived from the signals read by the
        /// procedure (e.g. @c always_comb, @c always_latch, or @c always \@*).
        /// Locally-declared symbols are excluded.
        Implicit,

        /// Procedures that contain multiple event controls, or event controls not
        /// at the start of the block (such as inside complicated flow control,
        /// fork join blocks, etc).
        Dynamic
    };

    /// The kind of this sensitivity list.
    Kind kind = Kind::None;

    /// For Kind::Explicit: the timing control containing the explicit sensitivity.
    const ast::TimingControl* timingControl = nullptr;

    /// The set of (symbol, bitRange) entries forming the sensitivity list.
    SmallVector<ReadRange, 2> reads;
};

/// Represents an analyzed procedure.
///
/// Note that this can include continuous assignments, which are not
/// technically procedures but are treated as such for analysis purposes.
class SLANG_EXPORT AnalyzedProcedure {
public:
    /// The symbol that was analyzed.
    not_null<const ast::Symbol*> analyzedSymbol;

    /// The procedure that contains this one, if any.
    /// Only possible for procedural checker instances.
    const AnalyzedProcedure* parentProcedure;

    /// Constructs a new AnalyzedProcedure object.
    AnalyzedProcedure(const ast::Symbol& symbol, const AnalyzedProcedure* parentProcedure);

    /// Constructs a new AnalyzedProcedure object.
    AnalyzedProcedure(AnalysisContext& context, const ast::Symbol& symbol,
                      const AnalyzedProcedure* parentProcedure, DFAResults& analysis);

    /// Returns the inferred clocking block for the procedure, if available.
    ///
    /// @note Clock inference is only performed if the procedure contains
    /// at least one concurrent assertion.
    const ast::TimingControl* getInferredClock() const { return inferredClock; }

    /// Gets all of the drivers in the procedure.
    std::span<const ValueDriver* const> getDrivers() const { return drivers; }

    /// Gets all of the subroutine calls in the procedure.
    std::span<const ast::CallExpression* const> getCallExpressions() const {
        return callExpressions;
    }

    /// Gets all of the timing control statements directly in the procedure
    std::span<const ast::Statement* const> getTimingControls() const { return timingControls; }

    /// The set of symbols read within a single @* timing region.
    struct ImplicitEventReadSet {
        /// The @* timed statement this read set belongs to.
        not_null<const ast::Statement*> statement;

        /// Symbols (and bit ranges) read in this @* region.
        SmallVector<ReadRange> reads;
    };

    /// Gets all symbols (and bit ranges) read anywhere in the procedure.
    std::span<const ReadRange> getReadSet() const { return readSet; }

    /// Gets the per-region read sets for each @* timing control in the procedure.
    std::span<const ImplicitEventReadSet> getImplicitEventReadSets() const {
        return implicitEventReadSets;
    }

    /// Gets the effective sensitivity list for this procedure.
    const SensitivityList& getSensitivityList() const { return sensitivityList; }

private:
    void buildSensitivityList(AnalysisContext& context, DFAResults& analysis,
                              ast::EvalContext& evalContext,
                              std::span<const ValueDriver* const> funcDrivers);

    const ast::TimingControl* inferredClock = nullptr;
    SmallVector<const ValueDriver*, 2> drivers;
    SensitivityList sensitivityList;
    SmallVector<const ast::CallExpression*, 2> callExpressions;
    SmallVector<const ast::Statement*, 2> timingControls;
    SmallVector<ReadRange, 2> readSet;
    SmallVector<ImplicitEventReadSet, 2> implicitEventReadSets;
};

} // namespace slang::analysis
