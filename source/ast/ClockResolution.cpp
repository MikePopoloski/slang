//------------------------------------------------------------------------------
// ClockResolution.cpp
// Clock resolution AST visitors and helpers
//
// SPDX-FileCopyrightText: ISP RAS
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/ClockResolution.h"

#include "slang/diagnostics/CompilationDiags.h"
#include "slang/text/Json.h"

namespace slang::ast::clk_res {

using namespace syntax;

static std::string getSECAsString(const SignalEventControl* sEC, Compilation& compilation) {
    JsonWriter writer;
    writer.setPrettyPrint(false);
    ASTSerializer ser(compilation, writer);
    ser.setIncludeAddresses(false);
    ser.serialize(*sEC);
    return std::string(writer.view());
}

static ClockingEvent::EventList concatEventLists(ClockingEvent::EventList& left,
                                                 ClockingEvent::EventList& right) {
    ClockingEvent::EventList res = left;
    for (auto rIter : right) {
        if (std::find(left.begin(), left.end(), rIter) == left.end())
            res.push_back(rIter);
    }
    return res;
}

static ClockingEvent::EventList getEventList(const Expression& exp) {
    if (const auto* bin = exp.as_if<const BinaryExpression>()) {
        switch (bin->op) {
            case BinaryOperator::BinaryAnd:
            case BinaryOperator::BinaryOr:
            case BinaryOperator::BinaryXor:
            case BinaryOperator::BinaryXnor:
            case BinaryOperator::LogicalAnd:
            case BinaryOperator::LogicalOr: {
                auto left = getEventList(bin->left());
                auto right = getEventList(bin->right());
                if (!left.empty() && !right.empty())
                    return concatEventLists(left, right);
                return {};
            }
            default:
                break;
        }
    }

    ClockingEvent::EventList res;
    if (const auto* sym = exp.getSymbolReference())
        res.push_back(sym);
    return res;
}

template<typename T>
void addUniqueSignalEvent(T* visitor, const SignalEventControl* sEC, Compilation& compilation,
                          SmallVector<ClockingEvent>& inferred) {
    if (const auto* cEE = sEC->expr.as_if<const ClockingEventExpression>()) {
        if (const auto* extractedSEC = cEE->timingControl.as_if<const SignalEventControl>())
            sEC = extractedSEC;
    }

    if (const auto* call = sEC->expr.as_if<const CallExpression>()) {
        if (call->getSubroutineName() == "$inferred_clock") {
            if (!inferred.empty()) {
                visitor->addUniqueCE(inferred.back());
                return;
            }
        }
    }

    ClockingEvent ce;
    if (ce.initialize(ClockingEvent::SeqProp, sEC, compilation))
        visitor->addUniqueCE(ce);
}

bool ClockingEvent::initialize(ClockingEventKind eventKind, const SignalEventControl* sEC,
                               Compilation& compilation) {
    const auto* lSEC = sEC;
    sourceRange = sEC->sourceRange;
    if (lSEC->edge != EdgeKind::PosEdge && lSEC->edge != EdgeKind::NegEdge) {
        // `clocking negedge_clk @(negadge clk)`
        if (const auto* symb = lSEC->expr.getSymbolReference()) {
            if (const auto* cbl = symb->as_if<const ClockingBlockSymbol>()) {
                if (const auto* sSevc = cbl->getEvent().as_if<const SignalEventControl>())
                    lSEC = sSevc;
            }
        }
    }

    if (const auto* clEv = lSEC->expr.as_if<const ClockingEventExpression>()) {
        // `checker c1(event clk);`
        if (const auto* ssEvC = clEv->timingControl.as_if<const SignalEventControl>();
            ssEvC != nullptr)
            lSEC = ssEvC;
    }

    if (eventKind == Always && lSEC->edge != EdgeKind::PosEdge && lSEC->edge != EdgeKind::NegEdge) {
        // See IEEE Std 1800-2017 16.14.6.c.1
        return false;
    }

    kind = eventKind;
    events = getEventList(lSEC->expr);

    // Store string representation of complex event expression to compare it with anothers later
    if (events.size() != 1 || lSEC->iffCondition)
        strEvent = getSECAsString(lSEC, compilation);

    edge = lSEC->edge;
    return true;
}

bool ClockingEvent::operator==(const ClockingEvent& ce) const {
    // if `strEvent`s not empty then there are at least one complex clocking event
    if (!strEvent.empty() || !ce.strEvent.empty())
        return strEvent == ce.strEvent;

    // check `edge` direction
    if (edge != ce.edge)
        return false;

    // Check simple single clocked clocking events
    if (size_t sz = events.size(); sz != ce.events.size())
        return false;
    else if (sz == 1)
        return events[0] == ce.events[0];

    return true;
}

void ClockingBlockVisitor::handle(const AssertionInstanceExpression& aInst) {
    aInstP.push_back(&aInst);
    visitDefault(aInst);
    SLANG_ASSERT(!aInstP.empty());
    aInstP.pop_back();
}

void ClockingBlockVisitor::handle(const SignalEventControl& se) {
    if (clkBlkSEC && !aInstP.empty()) {
        auto& sym = aInstP.back()->symbol;
        auto scope = sym.getParentScope();
        auto& scopeSym = scope->asSymbol();
        if (!ClockingBlockSymbol::isKind(scopeSym.kind)) {
            auto* seCl = se.expr.as_if<const NamedValueExpression>();
            auto* clkBlkSECCl = clkBlkSEC->expr.as_if<const NamedValueExpression>();
            auto* seSym = seCl ? &seCl->symbol : nullptr;
            auto* clkBlkSECSym = clkBlkSECCl ? &clkBlkSECCl->symbol : nullptr;
            if (se.edge != clkBlkSEC->edge || seSym != clkBlkSECSym || clkBlkSECSym == nullptr) {
                // If a named sequence that is defined outside the clocking block is used, its
                // clock, if specified, must be identical to the clocking block's clock
                compilation.getRoot().addDiag(diag::DiffClockInClockinBlock, sLoc);
            }
        }
        else {
            // See SystemVerilog LRM 16.16 section - "clocking block" rules.
            // No explicit event control is allowed in any property or sequence declaration
            // in clocking block
            compilation.getRoot().addDiag(diag::ClockinBlockClockEvent, se.sourceRange);
        }
    }
    visitDefault(se);
}

void SequenceVisitor::addUniqueCE(const ClockingEvent& infer) {
    if (std::find(binClkEvents.begin(), binClkEvents.end(), infer) != binClkEvents.end())
        return;
    binClkEvents.push_back(infer);

    if (ignoreSubSeq)
        return;

    if (std::find(clkEvents.begin(), clkEvents.end(), infer) != clkEvents.end())
        return;

    clkEvents.push_back(infer);
}

SmallVector<ClockingEvent> SequenceVisitor::merge(const SmallVector<ClockingEvent>& first,
                                                  const SmallVector<ClockingEvent>& second) {
    SmallVector<ClockingEvent> res = first;
    for (const auto& r : second) {
        if (std::find(res.begin(), res.end(), r) == res.end())
            res.push_back(r);
    }
    return res;
}

void SequenceVisitor::handle(const BinaryAssertionExpr& binExp) {
    SmallVector<ClockingEvent> binClkEventsPrev = binClkEvents;
    binClkEvents.clear();

    binExp.left.visit(*this);

    SmallVector<ClockingEvent> leftBinClkEvents = binClkEvents;
    binClkEvents.clear();

    bool ignoreSubSeqPrev = ignoreSubSeq;
    // See 16.16.1 section of SystemVerilog LRM:
    // The set of semantic leading clocks of "q1 and q2" is the union of the set of semantic leading
    // clocks of q1 with the set of semantic leading clocks of q2. And also The set of semantic
    // leading clocks of "q1 or q2" is the union of the set of semantic leading clocks of q1 with
    // the set of semantic leading clocks of q2.
    // From the other hand LRM doesn't specify a behaviour in case of other binary operator
    // types. Therefore, the right side is not considered during check.
    bool isAndOr = (binExp.op == BinaryAssertionOperator::And) ||
                   (binExp.op == BinaryAssertionOperator::Or);
    // See "ignoreRightOfBOp" description - in case of not `and`/`or` binary operator don't ignore
    // right-hand part of sequence if "ignoreRightOfBOp" is set to "false"
    bool isInsideAlways = (!compilation.getOptions().ignoreRightOfBOp && !inferred.empty() &&
                           inferred.back().kind == ClockingEvent::Always);
    ignoreSubSeq = (isAndOr || isInsideAlways) ? ignoreSubSeq : true;
    binExp.right.visit(*this);
    ignoreSubSeq = ignoreSubSeqPrev;

    // When the (sub)sequence `binBlkEvents` list is empty then sequence is unclocked
    if (!leftBinClkEvents.empty() && !binClkEvents.empty() && leftBinClkEvents != binClkEvents) {
        std::stringstream ss;
        ss << binExp.op;
        compilation.getRoot().addDiag(diag::SingleClockBinSeqExpected, sourceRange) << ss.str();
    }
    // Store binary left and right parts clocking events.
    binClkEvents = merge(binClkEvents, leftBinClkEvents);
    binClkEvents = merge(binClkEvents, binClkEventsPrev);
}

void SequenceVisitor::handle(const SequenceConcatExpr& conExp) {
    bool ignoreSubSeqPrev = ignoreSubSeq;

    SmallVector<ClockingEvent> binClkEventsPrev = binClkEvents;
    binClkEvents.clear();

    SmallVector<ClockingEvent> binClkEventsFirst;
    SmallVector<ClockingEvent> binClkEventsLast;
    bitmask<NondegeneracyStatus> prevStatus;

    for (const auto& elem : conExp.elements) {
        binClkEventsLast = binClkEvents;
        binClkEvents.clear();

        const auto& elemSeq = elem.sequence;
        elemSeq->visit(*this);

        // See the section 16.16.1 of SystemVerilog LRM - the semantic leading clock of m1 ##1(##0)
        // m2 is equal to the semantic leading clock of m1. Accordingly to this if the concatenation
        // subsequences are multiclocked then the clock events of all but the first can be ignored.
        ignoreSubSeq = true;

        if (binClkEventsLast.empty()) {
            binClkEventsFirst = binClkEvents;
            prevStatus = elemSeq->checkNondegeneracy();
            continue;
        }
        if (!binClkEventsLast.empty() && !binClkEvents.empty() &&
            (binClkEventsLast != binClkEvents)) {

            // When the (sub)sequence `binBlkEvents` list is empty then sequence is unclocked.
            // See the section 16.13.1 of SystemVerilog LRM - When concatenating differently clocked
            // sequences, the maximal singly clocked subsequences are required to admit only
            // nonempty matches.
            if ((elemSeq->checkNondegeneracy() | prevStatus).has(NondegeneracyStatus::AdmitsEmpty))
                compilation.getRoot().addDiag(diag::MultiClkConcatAdmitsEmpty, sourceRange);

            if (elem.delay.max > 1U)
                compilation.getRoot().addDiag(diag::SingleClockDelaySeqExpected, sourceRange)
                    << elem.delay.max.value_or(UINT32_MAX);
        }
        prevStatus = elemSeq->checkNondegeneracy();
    }

    // Merge clocking events from the left hand of concatenation expression due to causes written
    // above
    binClkEvents = merge(binClkEventsPrev, binClkEventsFirst);
    ignoreSubSeq = ignoreSubSeqPrev;
}

void SequenceVisitor::handle(const ClockingAssertionExpr& clkExp) {
    if (const auto* sevc = clkExp.clocking.as_if<const SignalEventControl>())
        addUniqueSignalEvent(this, sevc, compilation, inferred);
}

void ConcurrentAssertionVisitor::addUniqueCE(const ClockingEvent& infer) {
    if (ignoreSubSeq)
        return;

    if (std::find(clkEvents.begin(), clkEvents.end(), infer) != clkEvents.end())
        return;

    clkEvents.push_back(infer);
}

void ConcurrentAssertionVisitor::handle(const AbortAssertionExpr& abortExp) {
    // Process a `accept_on`/`reject_on`/`sync_accept_on`/`sync_reject_on` property
    // expression.
    if (abortExp.isSync) {
        if (!inferred.empty())
            addUniqueCE(inferred.back());

        bool ignoreSubSeqPrev = ignoreSubSeq;
        ignoreSubSeq = true;
        abortExp.expr.visit(*this);
        ignoreSubSeq = ignoreSubSeqPrev;
    }
    else {
        abortExp.expr.visit(*this);
    }
}

void ConcurrentAssertionVisitor::handle(const ConditionalAssertionExpr& condExp) {
    // The set of semantic leading clocks of `if (b) q1 else q2 is {inherited}`.
    if (!inferred.empty())
        addUniqueCE(inferred.back());

    bool ignoreSubSeqPrev = ignoreSubSeq;
    ignoreSubSeq = true;
    condExp.ifExpr.visit(*this);
    if (condExp.elseExpr)
        condExp.elseExpr->visit(*this);
    ignoreSubSeq = ignoreSubSeqPrev;
}

void ConcurrentAssertionVisitor::handle(const CaseAssertionExpr& caseExp) {
    // The set of semantic leading clocks of:
    //    `case (b) b1: q1 … bn: qn [default: qd] endcase`
    // is {inherited}.
    if (!inferred.empty())
        addUniqueCE(inferred.back());

    bool ignoreSubSeqPrev = ignoreSubSeq;
    ignoreSubSeq = true;
    for (const auto& item : caseExp.items) {
        item.body->visit(*this);
    }

    if (caseExp.defaultCase)
        caseExp.defaultCase->visit(*this);
    ignoreSubSeq = ignoreSubSeqPrev;
}

void ConcurrentAssertionVisitor::handle(const SequenceConcatExpr& conExp) {
    SequenceVisitor visitor(compilation, sourceRange, inferred, clkEvents, ignoreSubSeq);
    conExp.visit(visitor);
}

void ConcurrentAssertionVisitor::handle(const ClockingAssertionExpr& clkExp) {
    if (const auto* sevc = clkExp.clocking.as_if<const SignalEventControl>())
        addUniqueSignalEvent(this, sevc, compilation, inferred);

    if (!(SimpleAssertionExpr::isKind(clkExp.expr.kind)))
        visitDefault(clkExp);
}

void ConcurrentAssertionVisitor::handle(const UnaryAssertionExpr& unaryExp) {
    bool ignoreSubSeqPrev = ignoreSubSeq;
    // See SystemVerilog LRM 16.16.1 section
    switch (unaryExp.op) {
        case UnaryAssertionOperator::NextTime:
        case UnaryAssertionOperator::SNextTime:
        // The set of semantic leading clocks of `nexttime q is {inherited}`.
        case UnaryAssertionOperator::Always:
        case UnaryAssertionOperator::SAlways:
        // The set of semantic leading clocks of `always q is {inherited}`.
        case UnaryAssertionOperator::SEventually:
            // The set of semantic leading clocks of `s_eventually q is {inherited}`.
            if (clkEvents.empty()) {
                if (inferred.empty())
                    compilation.getRoot().addDiag(diag::NoClockResolved, sourceRange);
                else
                    addUniqueCE(inferred.back());
            }
            ignoreSubSeq = true;
            break;
        default:
            break;
    }

    visitDefault(unaryExp);
    ignoreSubSeq = ignoreSubSeqPrev;
}

void ConcurrentAssertionVisitor::handle(const BinaryAssertionExpr& binExp) {
    switch (binExp.op) {
        case BinaryAssertionOperator::OverlappedImplication:
        case BinaryAssertionOperator::NonOverlappedImplication:
        case BinaryAssertionOperator::OverlappedFollowedBy:
        case BinaryAssertionOperator::NonOverlappedFollowedBy: {
            SequenceVisitor visitor(compilation, sourceRange, inferred, clkEvents, ignoreSubSeq);
            binExp.left.visit(visitor);

            bool ignoreSubSeqPrev = ignoreSubSeq;
            // See 16.16.1 section of SystemVerilog LRM:
            // The set of semantic leading clocks of "q1 and q2" is the union of the set of semantic
            // leading clocks of q1 with the set of semantic leading clocks of q2. And also The set
            // of semantic leading clocks of "q1 or q2" is the union of the set of semantic leading
            // clocks of q1 with the set of semantic leading clocks of q2. From the other hand LRM
            // doesn't specify a behaviour in case of other binary operator types. Therefore, the
            // right side is not considered during check. See "ignoreRightOfBOp" description -
            // in case of not `and`/`or` binary operator don't ignore right-hand part of sequence if
            // "ignoreRightOfBOp" is set to "false"
            bool isInsideAlways = (!compilation.getOptions().ignoreRightOfBOp &&
                                   !inferred.empty() &&
                                   inferred.back().kind == ClockingEvent::Always);
            if (!isInsideAlways)
                ignoreSubSeq = true;
            binExp.right.visit(*this);
            ignoreSubSeq = ignoreSubSeqPrev;
            break;
        }
        case BinaryAssertionOperator::Until:
        case BinaryAssertionOperator::SUntil:
        case BinaryAssertionOperator::UntilWith:
        case BinaryAssertionOperator::SUntilWith: {
            bool ignoreSubSeqPrev = ignoreSubSeq;
            if (!inferred.empty())
                addUniqueCE(inferred.back());
            ignoreSubSeq = true;
            visitDefault(binExp);
            ignoreSubSeq = ignoreSubSeqPrev;
            break;
        }
        case BinaryAssertionOperator::And:
        case BinaryAssertionOperator::Or:
        default:
            visitDefault(binExp);
            break;
    }
}

void ConcurrentAssertionVisitor::handle(const AssertionInstanceExpression& aIE) {
    if (!inferred.empty() && inferred.back().kind == ClockingEvent::Always) {
        // Assertion inside an always block
        if (const auto* scope = aIE.symbol.getParentScope()) {
            if (ClockingBlockSymbol::isKind(scope->asSymbol().kind)) {
                // `assert property (posedge_clk.q4)`;
                // legal: will be queued (pending) on negedge clk, then
                // (if matured) checked at next posedge clk (see 16.14.6)
                return;
            }
        }
    }

    if (aIE.type->isSequenceType()) {
        SequenceVisitor visitor(compilation, sourceRange, inferred, clkEvents, ignoreSubSeq);
        aIE.visit(visitor);
        return;
    }

    if (const auto* scope = aIE.symbol.getParentScope()) {
        if (const auto& scopeSym = scope->asSymbol(); ClockingBlockSymbol::isKind(scopeSym.kind)) {
            const auto& blkSym = scopeSym.as<const ClockingBlockSymbol>();
            if (const auto* sevc = blkSym.getEvent().as_if<const SignalEventControl>()) {
                ClockingEvent ce;
                if (ce.initialize(ClockingEvent::SeqProp, sevc, compilation)) {
                    addUniqueCE(ce);
                    return;
                }
            }
        }
    }
    visitDefault(aIE);
}

void AlwaysTimingVisitor::handle(const SignalEventControl& sEC) {
    const auto* curSEC = &sEC;
    if (const auto* cee = curSEC->expr.as_if<const ClockingEventExpression>()) {
        if (const auto* extractedSEC = cee->timingControl.as_if<const SignalEventControl>())
            curSEC = extractedSEC;
    }

    if (const auto* call = curSEC->expr.as_if<const CallExpression>()) {
        if (call->getSubroutineName() == "$inferred_clock") {
            if (checkerInferredClock.kind != ClockingEvent::SeqProp) {
                inferred.push_back(checkerInferredClock);
                return;
            }
        }
    }

    ClockingEvent ce;
    if (ce.initialize(ClockingEvent::Always, curSEC, compilation))
        inferred.push_back(ce);
}

void InstanceBodyVisitor::handle(const ProceduralCheckerStatement& stmt) {
    for (unsigned i = 0; i < stmt.instances.size(); i++) {
        const auto* checker = stmt.instances[i];
        ClockingEvent ce;
        if (const auto* checkerInst = checker->as_if<CheckerInstanceSymbol>()) {
            if (const auto* defClock = compilation.getDefaultClocking(checkerInst->body)) {
                if (const auto* clockingBlock = defClock->as_if<const ClockingBlockSymbol>()) {
                    if (const auto* sevc =
                            clockingBlock->getEvent().as_if<const SignalEventControl>())
                        ce.initialize(ClockingEvent::Default, sevc, compilation);
                }
            }
        }

        InstanceBodyVisitor visitor(compilation, ce, /* skipCheckerBody = */ false);
        if (!inferred.empty())
            visitor.checkerInferredClock = inferred.back();
        checker->visit(visitor);
    }
}

void InstanceBodyVisitor::handle(const ProceduralBlockSymbol& procBlock) {
    // Store collected list of inferred clocks
    SmallVector<ClockingEvent> inferredOld = inferred;
    if (procBlock.procedureKind == ProceduralBlockKind::Always || procBlock.isSingleDriverBlock() ||
        procBlock.procedureKind == ProceduralBlockKind::Initial) {
        const auto& stmt = procBlock.getBody();
        if (stmt.bad())
            return;

        if (const auto* timed = stmt.as_if<const TimedStatement>()) {
            AlwaysTimingVisitor visitor(compilation, inferred, checkerInferredClock);
            timed->timing.visit(visitor);
            AlwaysTimingCheckUseVisitor useVisitor(compilation, inferred);
            timed->stmt.visit(useVisitor);
        }
    }

    visitDefault(procBlock);
    inferred = inferredOld;
}

void InstanceBodyVisitor::processPropSeq(const Symbol& sym) const {
    if (clkBlkSEC && (sym.as_if<PropertySymbol>() || sym.as_if<SequenceSymbol>())) {
        // Get a clocking event from a clocking block
        auto& expr = AssertionInstanceExpression::makeDefault(sym);
        ClockingBlockVisitor visitor(compilation, clkBlkSEC, sym.location);
        expr.visit(visitor);
    }
}

void InstanceBodyVisitor::handle(const PropertySymbol& propSym) {
    visitDefault(propSym);
    processPropSeq(propSym);
}

void InstanceBodyVisitor::handle(const SequenceSymbol& seqSym) {
    visitDefault(seqSym);
    processPropSeq(seqSym);
}

void InstanceBodyVisitor::handle(const ConcurrentAssertionStatement& stmt) {
    bool explicitClocking = false;
    if (ClockingAssertionExpr::isKind(stmt.propertySpec.kind)) {
        const auto& clocking = stmt.propertySpec.as<const ClockingAssertionExpr>();
        if (SimpleAssertionExpr::isKind(clocking.expr.kind))
            explicitClocking = true;
    }

    ConcurrentAssertionVisitor visitor(compilation, stmt.sourceRange, inferred, explicitClocking);
    stmt.propertySpec.visit(visitor);
    // Emit an error if clocking event is not single for assertion expression
    if (visitor.clkEvents.size() > 1) {
        auto& diag = compilation.getRoot().addDiag(diag::NotUniqueLeadingClock, stmt.sourceRange);
        for (unsigned i = 0; i < visitor.clkEvents.size(); i++)
            diag.addNote(diag::FoundClocks, visitor.clkEvents[i].sourceRange);
    }
    else if (visitor.clkEvents.empty()) {
        compilation.getRoot().addDiag(diag::NoClockResolved, stmt.sourceRange);
    }
    else {
        if (inferred.empty() && !(SimpleAssertionExpr::isKind(stmt.propertySpec.kind) ||
                                  ClockingAssertionExpr::isKind(stmt.propertySpec.kind))) {
            // Check no default, inferred, or explicit leading
            // clocking event and maximal property is not an instance
            compilation.getRoot().addDiag(diag::MaxPropBadClkEven, stmt.sourceRange);
        }
    }
}

void InstanceBodyVisitor::handle(const ClockingBlockSymbol& clkSym) {
    // Update current `SignalEvent` during visiting members of current clocking block
    clkBlkSEC = clkSym.getEvent().as_if<const SignalEventControl>();
    if (clkBlkSEC) {
        visitDefault(clkSym);
        // Empty clocking event means that the clocking block processing is done
        clkBlkSEC = nullptr;
    }
}

void ClockResolutionVisitor::handle(const InstanceBodySymbol& body) {
    ClockingEvent ce;
    // Extract default clocking
    if (const auto defClock = compilation.getDefaultClocking(body)) {
        if (const auto* clockingBlock = defClock->as_if<const ClockingBlockSymbol>()) {
            if (const auto* sevc = clockingBlock->getEvent().as_if<const SignalEventControl>())
                ce.initialize(ClockingEvent::Default, sevc, compilation);
        }
    }

    // Check for invalid nodes and ignore members contained within them. slang can mark certain
    // nodes as <invalid> without triggering any errors or warnings.
    MarkInvalidVisitor invVisitor;
    InstanceBodyVisitor visitor(compilation, ce);
    for (const auto& memb : body.members()) {
        memb.visit(invVisitor);
        if (!invVisitor.invalid)
            memb.visit(visitor);
        invVisitor.invalid = false;
    }

    visitDefault(body);
}
} // namespace slang::ast::clk_res
