//------------------------------------------------------------------------------
// ClockResolution.h
// Clock resolution AST visitors and helpers
//
// SPDX-FileCopyrightText: ISP RAS
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/diagnostics/CompilationDiags.h"

namespace slang::ast::clk_res {

using namespace syntax;

struct ClockingEvent {
    using EventList = SmallVector<const Symbol*>;

    enum ClockingEventKind { None, SeqProp, Default, Always } kind;
    bool initialize(ClockingEventKind eventKind, const SignalEventControl* sEC,
                    Compilation& compilation);
    bool operator==(const ClockingEvent&) const;

    /// For diagnostics
    SourceRange sourceRange;
    /// For simple event expression with just edge wrapped signals
    EventList events;
    EdgeKind edge;
    /// For storing complex event expression (with `iff` also).
    /// Storing AST as a string is necessary in order to determine if there are any identical events
    /// by comparing strings.
    std::string strEvent;
};

/// Visitor checks the properties and sequences at `clocking` blocks to determine it's signal event
/// list
class ClockingBlockVisitor : public ASTVisitor<ClockingBlockVisitor, true, true> {
public:
    ClockingBlockVisitor(Compilation& compilation, const SignalEventControl* clkBlkSEC,
                         const SourceLocation sLoc) :
        compilation(compilation), clkBlkSEC(clkBlkSEC), sLoc(sLoc) {}

    void handle(const AssertionInstanceExpression&);
    void handle(const SignalEventControl&);

private:
    Compilation& compilation;
    /// Clocking block signal event control expression
    const SignalEventControl* clkBlkSEC;
    /// Stack for storing current assertion instance context to get it's scope later
    SmallVector<const AssertionInstanceExpression*> aInstP;
    /// For diagnostics
    const SourceLocation sLoc;
};

/// Endpoint of analysis which is represented by possible leaf nodes.
/// It emits an error if any leaf was reached with no determined clock event but adds it
/// into the context if not.
#define REPORT_INFERRED(EXPR)                                                      \
    void handle(const EXPR&) {                                                     \
        if (clkEvents.empty()) {                                                   \
            if (inferred.empty())                                                  \
                compilation.getRoot().addDiag(diag::NoClockResolved, sourceRange); \
            else                                                                   \
                addUniqueCE(inferred.back());                                      \
        }                                                                          \
    }

/// Sequence verify visitor
class SequenceVisitor : public ASTVisitor<SequenceVisitor, true, true> {
public:
    SequenceVisitor(Compilation& compilation, SourceRange sourceRange,
                    SmallVector<ClockingEvent>& inferred, SmallVector<ClockingEvent>& clkEvents,
                    bool ignoreSubSeq) :
        compilation(compilation), sourceRange(sourceRange), inferred(inferred),
        clkEvents(clkEvents), ignoreSubSeq(ignoreSubSeq) {}

    SmallVector<ClockingEvent> merge(const SmallVector<ClockingEvent>& first,
                                     const SmallVector<ClockingEvent>& second);
    /// Check the clocking event presense in visitor clocking event lists and add into it if not
    void addUniqueCE(const ClockingEvent&);
    REPORT_INFERRED(ValueExpressionBase)
    REPORT_INFERRED(CallExpression)
    REPORT_INFERRED(IntegerLiteral)
    REPORT_INFERRED(RealLiteral)
    REPORT_INFERRED(TimeLiteral)
    REPORT_INFERRED(UnbasedUnsizedIntegerLiteral)
    REPORT_INFERRED(NullLiteral)
    REPORT_INFERRED(UnboundedLiteral)
    REPORT_INFERRED(StringLiteral)
    void handle(const BinaryAssertionExpr&);
    void handle(const SequenceConcatExpr&);
    void handle(const ClockingAssertionExpr&);

private:
    Compilation& compilation;
    /// For diagnostics
    SourceRange sourceRange;
    /// Sequence inferred clock events
    SmallVector<ClockingEvent>& inferred;
    /// List of all current context clocking events
    SmallVector<ClockingEvent>& clkEvents;
    /// Store binary and concat operators left and right part clocking event lists
    /// to compare it later
    SmallVector<ClockingEvent> binClkEvents;
    /// Flag to ignore checking nested nodes in the case of assumptions or restrictions being made.
    bool ignoreSubSeq;
};

/// Concurrent assertion visitor
class ConcurrentAssertionVisitor : public ASTVisitor<ConcurrentAssertionVisitor, true, true> {
public:
    ConcurrentAssertionVisitor(Compilation& compilation, SourceRange sourceRange,
                               SmallVector<ClockingEvent>& inferred, bool explicitClocking) :
        compilation(compilation), sourceRange(sourceRange), inferred(inferred) {
        // Below is a implementation of the VCS check which emits an error for such type of sequence
        // property
        //   `sequence seqX; @(negedge clk) a ##1 @(posedge clk_n)b; endsequence`
        //   `always @(posedge_clk) assert property (seqX);`
        if (!explicitClocking && inferred.size() && inferred.back().kind == ClockingEvent::Always) {
            clkEvents.push_back(inferred.back());
        }
    }

    void addUniqueCE(const ClockingEvent&);
    REPORT_INFERRED(ValueExpressionBase)
    REPORT_INFERRED(CallExpression)
    REPORT_INFERRED(IntegerLiteral)
    REPORT_INFERRED(RealLiteral)
    REPORT_INFERRED(TimeLiteral)
    REPORT_INFERRED(UnbasedUnsizedIntegerLiteral)
    REPORT_INFERRED(NullLiteral)
    REPORT_INFERRED(UnboundedLiteral)
    REPORT_INFERRED(StringLiteral)
    void handle(const AbortAssertionExpr&);
    void handle(const ConditionalAssertionExpr&);
    void handle(const CaseAssertionExpr&);
    void handle(const SequenceConcatExpr&);
    void handle(const ClockingAssertionExpr&);
    void handle(const UnaryAssertionExpr&);
    void handle(const BinaryAssertionExpr&);
    void handle(const AssertionInstanceExpression&);

    /// List of current context clocking events
    SmallVector<ClockingEvent> clkEvents;

private:
    Compilation& compilation;
    /// For diagnostics
    SourceRange sourceRange;
    /// Sequence/property inferred clock events
    SmallVector<ClockingEvent>& inferred;
    /// Flag to ignore checking nested nodes in the case of assumptions or restrictions being made.
    bool ignoreSubSeq = false;
};

/// Visitor to collect all possible inferred clocks at `SignalEventControl` expression
class AlwaysTimingVisitor : public ASTVisitor<AlwaysTimingVisitor, true, true> {
public:
    AlwaysTimingVisitor(Compilation& compilation, SmallVector<ClockingEvent>& inferred,
                        ClockingEvent& checkerInferredClock) :
        compilation(compilation), inferred(inferred), checkerInferredClock(checkerInferredClock) {}

    void handle(const SignalEventControl&);

private:
    Compilation& compilation;
    /// List of inferred clocks
    SmallVector<ClockingEvent>& inferred;
    /// Previously stored checker instance inferred clock
    ClockingEvent& checkerInferredClock;
};

/// Visitor to erase from a list of inferred clocking events that signals which is used outside
/// assertions (that isn't a real clock due to SystemVerilog LRM).
/// It also checks that delay are not present before assertion.
class AlwaysTimingCheckUseVisitor : public ASTVisitor<AlwaysTimingCheckUseVisitor, true, true> {
public:
    AlwaysTimingCheckUseVisitor(Compilation& compilation, SmallVector<ClockingEvent>& inferred) :
        compilation(compilation), inferred(inferred) {
        delayBeforeAssert = nullptr;
    }

    void handle(const ConcurrentAssertionStatement&) {
        if (delayBeforeAssert) {
            compilation.getRoot().addDiag(diag::AssertAfterTimingControl,
                                          delayBeforeAssert->sourceRange);
            delayBeforeAssert = nullptr;
        }
        // No `defaultVisit` for ignoring subsidaries
    }

    void handle(const ImmediateAssertionStatement&) {
        // IEEE Std 1800-2017 16.14.6.c.2
        // Ignore subsidaries
    }

    void handle(const ValueExpressionBase& vEB) {
        for (auto& iter : inferred) {
            auto& iterEvList = iter.events;
            if (iter.kind == ClockingEvent::Always &&
                (std::find(iterEvList.begin(), iterEvList.end(), &vEB.symbol) != iterEvList.end()))
                iterEvList.clear();
        }

        inferred.erase(std::remove_if(inferred.begin(), inferred.end(),
                                      [](const auto& cE) { return cE.events.empty(); }),
                       inferred.end());
    }

    void handle(const TimingControl& tC) {
        if ((tC.as_if<DelayControl>() || tC.as_if<SignalEventControl>()) && !delayBeforeAssert)
            delayBeforeAssert = &tC;
    }

private:
    Compilation& compilation;
    /// List of `always` block inferred clocks
    SmallVector<ClockingEvent>& inferred;
    // For delay storing which is present before assertion
    const TimingControl* delayBeforeAssert;
};

/// Instance body helper visitor - visiting should start at InstanceBody symbol
class InstanceBodyVisitor : public ASTVisitor<InstanceBodyVisitor, true, true> {
public:
    InstanceBodyVisitor(Compilation& compilation, ClockingEvent& ce, bool skipCheckerBody = true) :
        compilation(compilation), skipCheckerBody(skipCheckerBody) {
        if (ce.events.size() || ce.strEvent != "")
            inferred.push_back(ce);
    }

    void processPropSeq(const Symbol&) const;

    /// If skipCheckerBody is set to false, then we skip the current checker instance body to
    /// process it later by using the instances array at the ProceduralCheckerStatement handler
    /// below. In reality, a checker instance can be located, for example, inside an always block,
    /// but according to the AST, it may appear outside, preventing a correct understanding of the
    /// context of inferred clocks. Therefore, the processing of checker instances can be delayed.
    void handle(const CheckerInstanceBodySymbol& sym) {
        if (!skipCheckerBody)
            visitDefault(sym);
    }
    void handle(const ProceduralCheckerStatement&);
    void handle(const ProceduralBlockSymbol&);
    void handle(const PropertySymbol&);
    void handle(const SequenceSymbol&);
    void handle(const ConcurrentAssertionStatement&);
    void handle(const ClockingBlockSymbol&);

    /// Skip instance body members because the outermost top-level `ClockResolutionVisitor`
    /// already handles it.
    void handle(const InstanceBodySymbol&) {}

private:
    Compilation& compilation;
    /// For emitting clocking block nested sequences
    const SignalEventControl* clkBlkSEC{};
    /// List for storing found inferred clocks
    SmallVector<ClockingEvent> inferred;
    /// For storing checker instance context inferred clock
    ClockingEvent checkerInferredClock;
    /// Checker instance body skipping control
    bool skipCheckerBody = true;
};

/// Visitor helper for checking nested invalid nodes to ignore their parents later
class MarkInvalidVisitor : public ASTVisitor<MarkInvalidVisitor, true, true> {
public:
    void handle(const ClockingAssertionExpr& e) {
        if (e.clocking.bad())
            invalid = true;
        visitDefault(e);
    }

    void handle(const SimpleAssertionExpr& e) {
        if (e.expr.bad())
            invalid = true;
        visitDefault(e);
    }

    bool invalid = false;
};

class ClockResolutionVisitor : public ASTVisitor<ClockResolutionVisitor, false, false> {
public:
    ClockResolutionVisitor(Compilation& compilation) : compilation(compilation) {}
    void handle(const InstanceBodySymbol&);

private:
    Compilation& compilation;
};
} // namespace slang::ast::clk_res
