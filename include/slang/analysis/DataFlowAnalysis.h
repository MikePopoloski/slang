//------------------------------------------------------------------------------
//! @file DataFlowAnalysis.h
//! @brief Data flow analysis pass
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/analysis/AbstractFlowAnalysis.h"
#include "slang/analysis/AnalysisManager.h"
#include "slang/analysis/DFAResults.h"
#include "slang/analysis/ValueDriver.h"
#include "slang/ast/LSPUtilities.h"

namespace slang::analysis {

namespace detail {

// A helper type that diagnoses conflicting unsequenced operations
// within a single expression tree, such as in the expression:
//    j = i++ + (i = i - 1);
//
class SLANG_EXPORT ExpressionSequenceChecker {
public:
    ExpressionSequenceChecker(FlowAnalysisBase& base, AnalysisContext* context);

    bool isEnabled() const { return context != nullptr; }

    void clear();

    void noteUse(const ValueSymbol& symbol, DriverBitRange bounds, const Expression& lsp,
                 bool isLValue);

    // Sequence regions form a tree, with child regions being unsequenced
    // with respect to their parents, and sequenced with respect to their
    // siblings. When we're done with a region we merge it into its parent.
    uint32_t allocSeq() {
        seqTree.push_back(currRegion);
        return uint32_t(seqTree.size() - 1u);
    }

    void mergeSeq(uint32_t seq) { seqTree[seq].merged = true; }

    // A stack frame that captures lvalue references and stores them so that
    // they can be registered after visiting sub-expressions. This is to model
    // the behavior of assignment expressions, where the write to the lhs is
    // sequenced after evaluation of both the lhs and rhs.
    struct LValueFrame {
        LValueFrame(ExpressionSequenceChecker& parent, bool isAlsoRVal) :
            parent(parent), prevFrame(std::exchange(parent.currFrame, this)),
            readRegion(parent.allocSeq()), writeRegion(parent.allocSeq()),
            parentRegion(std::exchange(parent.currRegion, readRegion)), isAlsoRVal(isAlsoRVal) {}

        ~LValueFrame() {
            parent.currRegion = writeRegion;
            parent.applyPendingLValues();
            parent.currFrame = prevFrame;

            parent.currRegion = parentRegion;
            parent.mergeSeq(readRegion);
            parent.mergeSeq(writeRegion);
        }

        ExpressionSequenceChecker& parent;
        SmallVector<std::tuple<const ValueSymbol*, DriverBitRange, const Expression*>> lvals;
        LValueFrame* prevFrame;
        uint32_t readRegion;
        uint32_t writeRegion;
        uint32_t parentRegion;
        bool isAlsoRVal;
    };

    struct RValueFrame {
        RValueFrame(ExpressionSequenceChecker& parent) :
            parent(parent), prevFrame(std::exchange(parent.currFrame, nullptr)) {}

        ~RValueFrame() { parent.currFrame = prevFrame; }

    private:
        ExpressionSequenceChecker& parent;
        LValueFrame* prevFrame;
    };

    LValueFrame* currFrame = nullptr;
    uint32_t currRegion = 0;

private:
    friend struct LValueFrame;

    void applyPendingLValues();
    void checkUsage(const ValueSymbol& symbol, DriverBitRange bounds, const Expression& lsp,
                    bool isMod);
    bool isUnsequenced(uint32_t seq);
    uint32_t representative(uint32_t seq);

    FlowAnalysisBase& base;
    AnalysisContext* context;

    // A region within an expression that may be sequenced with respect to some other region.
    struct SeqRegion {
        uint32_t parent : 31;
        bool merged : 1;
        SeqRegion(uint32_t parent) : parent(parent), merged(false) {}
    };

    SmallVector<SeqRegion> seqTree;
    flat_hash_map<const ValueSymbol*, TaggedLSPMap> trackedUses;
};

} // namespace detail

/// The base class for data flow analysis implementations.
///
/// Augments the AbstractFlowAnalysis class with logic for tracking assigned
/// states of symbols within the procedure.
template<typename TDerived, typename TState>
class DataFlowAnalysis : public AbstractFlowAnalysis<TDerived, TState>, public DFAResults {
public:
    using AFABase = AbstractFlowAnalysis<TDerived, TState>;

    /// The context used to perform analysis.
    AnalysisContext& context;

    /// Runs the analysis.
    void run() {
        const Symbol& sym = this->rootSymbol;
        switch (sym.kind) {
            case SymbolKind::ProceduralBlock:
                AFABase::run(sym.as<ProceduralBlockSymbol>().getBody());
                break;
            case SymbolKind::Subroutine:
                AFABase::run(sym.as<SubroutineSymbol>().getBody());
                break;
            case SymbolKind::ContinuousAssign: {
                auto& assign = sym.as<ContinuousAssignSymbol>();
                if (auto delay = assign.getDelay())
                    handleTiming(*delay);

                AFABase::run(assign.getAssignment());
                break;
            }
            default:
                SLANG_UNREACHABLE;
        }

        hasReturnStatements = !this->getReturnStates().empty();
        endIsReachable = this->getState().reachable;
    }

protected:
    friend AFABase;

    using LValueFrame = detail::ExpressionSequenceChecker::LValueFrame;
    using RValueFrame = detail::ExpressionSequenceChecker::RValueFrame;

    /// Constructs a new DataFlowAnalysis object.
    DataFlowAnalysis(AnalysisContext& context, const Symbol& symbol, bool reportDiags) :
        AFABase(symbol, context.manager->getOptions(),
                reportDiags ? &context.diagnostics : nullptr),
        DFAResults(context, this->getState().assigned), context(context),
        sequenceChecker(*this, reportDiags ? &context : nullptr),
        lspVisitor(*static_cast<TDerived*>(this)) {}

    template<typename T>
        requires(std::is_base_of_v<Expression, T> && !IsSelectExpr<T>)
    void handle(const T& expr) {
        lspVisitor.clear();
        this->visitExpr(expr);
    }

    template<typename T>
        requires(IsSelectExpr<T>)
    void handle(const T& expr) {
        lspVisitor.handle(expr);
    }

    template<typename T>
        requires(IsAnyOf<T, TimedStatement, WaitStatement, WaitOrderStatement, WaitForkStatement>)
    void handle(const T& stmt) {
        if constexpr (std::is_same_v<T, TimedStatement>) {
            handleTiming(stmt.timing);
        }

        timedStatements.push_back(&stmt);
        this->visitStmt(stmt);
    }

    void handle(const ProceduralAssignStatement& stmt) {
        // Procedural force statements don't act as drivers
        // of their lvalue target.
        if (stmt.isForce && stmt.assignment.kind == ExpressionKind::Assignment) {
            auto& assign = stmt.assignment.as<AssignmentExpression>();
            this->visit(assign.left());
            this->visit(assign.right());
        }
        else {
            this->visitStmt(stmt);
        }
    }

    void handle(const AssignmentExpression& expr) {
        if (expr.isLValueArg()) {
            // This is a pseudo-assignment expression fabricated for
            // things like output ports, so there is no rhs to visit.
            visitLValue(expr.left());
            return;
        }

        // If there is an intra-assignment timing control there is a guaranteed
        // order between the lhs and the rhs (unless it's a compound assignment
        // since then we need to eval the lhs as part of the operator anyway).
        if (expr.timingControl) {
            handleTiming(*expr.timingControl);

            if (!expr.isCompound()) {
                visitSequenced<true>(expr.right(), expr.left());
                return;
            }
        }

        // The write to the lhs is sequenced after evaluation of both
        // the lhs and the rhs.
        LValueFrame lvalFrame(sequenceChecker, expr.isCompound());
        visitLValue(expr.left());

        RValueFrame rvalFrame(sequenceChecker);
        this->visit(expr.right());
    }

    void handle(const CallExpression& expr) {
        // Writes to lvalue args (output, inout, ref) are sequenced
        // after the called subroutine runs.
        LValueFrame lvalFrame(sequenceChecker, /* isAlsoRVal */ true);

        callExpressions.push_back(&expr);
        expr.visitExprsNoArgs(*this);

        auto visitArg = [&](const Expression& arg) {
            if (auto assign = arg.as_if<AssignmentExpression>()) {
                if (assign->isLValueArg()) {
                    this->visit(arg);
                    return;
                }
            }

            RValueFrame rval(sequenceChecker);
            this->visit(arg);
        };

        if (auto sysCall = std::get_if<CallExpression::SystemCallInfo>(&expr.subroutine)) {
            auto& sub = *sysCall->subroutine;

            size_t argIndex = 0;
            for (auto arg : expr.arguments()) {
                if (!sub.isArgUnevaluated(argIndex)) {
                    if (sub.isArgByRef(argIndex))
                        visitLValue(*arg);
                    else
                        visitArg(*arg);
                }
                argIndex++;
            }

            if (sub.neverReturns)
                this->setUnreachable();
        }
        else {
            auto subroutine = std::get<const SubroutineSymbol*>(expr.subroutine);
            auto formals = subroutine->getArguments();
            auto args = expr.arguments();
            SLANG_ASSERT(formals.size() == args.size());

            for (size_t i = 0; i < formals.size(); i++) {
                // Non-const ref args are special because they don't have an assignment
                // expression generated for them but still act as lvalues.
                auto& formal = *formals[i];
                if (formal.direction == ArgumentDirection::Ref &&
                    !formal.flags.has(VariableFlags::Const)) {
                    visitLValue(*args[i]);
                }
                else {
                    visitArg(*args[i]);
                }
            }
        }
    }

    void handle(const UnaryExpression& expr) {
        if (OpInfo::isLValue(expr.op))
            visitLValue(expr.operand());
        else
            this->visitExpr(expr);
    }

    void handle(const BinaryExpression& expr) {
        lspVisitor.clear();

        if (!OpInfo::isShortCircuit(expr.op)) {
            this->visitExpr(expr);
            return;
        }

        // Short-circuit ops have a well defined sequencing of
        // evaluation, so model that here.
        auto firstRegion = sequenceChecker.allocSeq();
        auto secondRegion = sequenceChecker.allocSeq();

        auto parentRegion = std::exchange(sequenceChecker.currRegion, firstRegion);
        this->visitShortCircuitOp(expr, [&] { sequenceChecker.currRegion = secondRegion; });

        sequenceChecker.currRegion = parentRegion;
        sequenceChecker.mergeSeq(firstRegion);
        sequenceChecker.mergeSeq(secondRegion);
    }

    void handle(const ConditionalExpression& expr) {
        lspVisitor.clear();

        // The condition expression is sequenced before evaluating
        // the selected value expression. Note that there is *not* a
        // defined sequence between the left and right value expression
        // because the handling of conditions with unknowns means that
        // both sides can end up being evaluated.
        auto firstRegion = sequenceChecker.allocSeq();
        auto secondRegion = sequenceChecker.allocSeq();

        auto parentRegion = std::exchange(sequenceChecker.currRegion, firstRegion);
        this->visitExpr(expr, [&] { sequenceChecker.currRegion = secondRegion; });

        sequenceChecker.currRegion = parentRegion;
        sequenceChecker.mergeSeq(firstRegion);
        sequenceChecker.mergeSeq(secondRegion);
    }

    void handle(const ExpressionStatement& stmt) {
        this->visitStmt(stmt);

        if (stmt.expr.kind == ExpressionKind::Assignment) {
            auto& assignment = stmt.expr.as<AssignmentExpression>();
            if (assignment.timingControl) {
                this->bad |= assignment.timingControl->bad();
                timedStatements.push_back(&stmt);
            }
        }
    }

    void handle(const ConcurrentAssertionStatement& stmt) {
        concurrentAssertions.push_back(&stmt);
        this->visitStmt(stmt);
    }

    void handle(const ProceduralCheckerStatement& stmt) {
        concurrentAssertions.push_back(&stmt);
        this->visitStmt(stmt);
    }

    void handle(const AssertionInstanceExpression& expr) {
        concurrentAssertions.push_back(&expr);
        this->visitExpr(expr);
    }

    void handle(const EventTriggerStatement& stmt) {
        if (stmt.timing)
            handleTiming(*stmt.timing);
        this->visitStmt(stmt);
    }

    void finishExpr(const Expression&) { sequenceChecker.clear(); }

    // **** State Management ****

    void joinState(TState& result, const TState& other) {
        if (result.reachable == other.reachable) {
            if (result.assigned.size() > other.assigned.size())
                result.assigned.resize(other.assigned.size());

            for (size_t i = 0; i < result.assigned.size(); i++) {
                result.assigned[i] = result.assigned[i].intersection(other.assigned[i],
                                                                     bitMapAllocator);
            }
        }
        else if (!result.reachable) {
            result = copyState(other);
        }
    }

    void meetState(TState& result, const TState& other) {
        if (!other.reachable) {
            result.reachable = false;
            return;
        }

        // Union the assigned state across each variable.
        if (result.assigned.size() < other.assigned.size())
            result.assigned.resize(other.assigned.size());

        for (size_t i = 0; i < other.assigned.size(); i++) {
            for (auto it = other.assigned[i].begin(); it != other.assigned[i].end(); ++it)
                result.assigned[i].unionWith(it.bounds(), *it, bitMapAllocator);
        }
    }

    TState copyState(const TState& source) {
        TState result;
        result.reachable = source.reachable;
        result.assigned.reserve(source.assigned.size());
        for (size_t i = 0; i < source.assigned.size(); i++)
            result.assigned.emplace_back(source.assigned[i].clone(bitMapAllocator));
        return result;
    }

    TState unreachableState() const {
        TState result;
        result.reachable = false;
        return result;
    }

    TState topState() const { return {}; }

private:
    detail::ExpressionSequenceChecker sequenceChecker;

    template<typename TOwner>
    friend struct ast::LSPVisitor;

    LSPVisitor<TDerived> lspVisitor;
    bool isLValue = false;

    void visitLValue(const Expression& expr) {
        SLANG_ASSERT(!isLValue);
        isLValue = true;
        this->visit(expr);
        isLValue = false;
    }

    template<bool SecondIsLVal = false>
    void visitSequenced(const Expression& first, const Expression& second) {
        auto firstRegion = sequenceChecker.allocSeq();
        auto secondRegion = sequenceChecker.allocSeq();

        auto parentRegion = std::exchange(sequenceChecker.currRegion, firstRegion);
        this->visit(first);

        sequenceChecker.currRegion = secondRegion;
        if (SecondIsLVal)
            visitLValue(second);
        else
            this->visit(second);

        sequenceChecker.currRegion = parentRegion;
        sequenceChecker.mergeSeq(firstRegion);
        sequenceChecker.mergeSeq(secondRegion);
    }

    void handleTiming(const TimingControl& timing) {
        if (timing.bad()) {
            this->bad = true;
            return;
        }

        // The timing expressions don't contribute to data flow but we still
        // want to analyze them for various correctness checks.
        context.manager->analyzeNonProceduralExprs(timing, this->rootSymbol);
    }

    [[nodiscard]] auto saveLValueFlag() {
        // This is called by LSPVisitor when we're entering a non-lvalue portion
        // of an lhs expression, such as the index portion of an element select.
        // We need to save off the lvalue flag, and also the current sequence
        // checker frame that may be buffering lvalue writes.
        auto guard = ScopeGuard([this, savedLVal = isLValue,
                                 savedFrame = std::exchange(sequenceChecker.currFrame, nullptr)] {
            isLValue = savedLVal;
            sequenceChecker.currFrame = savedFrame;
        });
        isLValue = false;
        return guard;
    }

    void noteReference(const ValueSymbol& symbol, const Expression& lsp);
};

template<typename TDerived, typename TState>
void DataFlowAnalysis<TDerived, TState>::noteReference(const ValueSymbol& symbol,
                                                       const Expression& originalLsp) {
    // This feels icky but we don't count a symbol as being referenced in the procedure
    // if it's only used inside an unreachable flow path. The alternative would just
    // frustrate users, but the reason it's icky is because whether a path is reachable
    // is based on whatever level of heuristics we're willing to implement rather than
    // some well defined set of rules in the LRM.
    auto& currState = this->getState();
    if (!currState.reachable)
        return;

    const Expression* lsp = &originalLsp;
    if (this->inUnrolledForLoop) {
        // During unrolled for loop evaluation the LSPs we evaluate can depend
        // on otherwise non-constant values, so we need to clone the LSP tree
        // and save the constants while we have them.
        lsp = &LSPUtilities::cloneLSP(context.alloc, originalLsp, this->getEvalContext());
    }

    auto bounds = LSPUtilities::getBounds(*lsp, this->getEvalContext(), symbol.getType());
    if (!bounds) {
        // This probably cannot be hit given that we early out elsewhere for
        // invalid expressions.
        return;
    }

    sequenceChecker.noteUse(symbol, *bounds, *lsp, isLValue);

    if (isLValue) {
        auto [it, inserted] = symbolToSlot.try_emplace(&symbol, (uint32_t)lvalues.size());
        if (inserted) {
            lvalues.emplace_back(symbol);
            SLANG_ASSERT(lvalues.size() == symbolToSlot.size());
        }

        auto index = it->second;
        if (index >= currState.assigned.size())
            currState.assigned.resize(index + 1);

        currState.assigned[index].unionWith(*bounds, {}, bitMapAllocator);

        auto& lspMap = lvalues[index].assigned;
        for (auto lspIt = lspMap.find(*bounds); lspIt != lspMap.end();) {
            // If we find an existing entry that completely contains
            // the new bounds we can just keep that one and ignore the
            // new one. Otherwise we will insert a new entry.
            auto itBounds = lspIt.bounds();
            if (itBounds.first <= bounds->first && itBounds.second >= bounds->second)
                return;

            // If the new bounds completely contain the existing entry, we can remove it.
            if (bounds->first < itBounds.first && bounds->second > itBounds.second) {
                lspMap.erase(lspIt, lspMapAllocator);
                lspIt = lspMap.find(*bounds);
            }
            else {
                ++lspIt;
            }
        }
        lspMap.insert(*bounds, lsp, lspMapAllocator);
    }
    else {
        rvalues[&symbol].unionWith(*bounds, {}, bitMapAllocator);
    }
}

/// Represents the state of a data flow analysis at a single point in a procedure.
struct SLANG_EXPORT DataFlowState {
    /// Each tracked variable has its assigned intervals stored here.
    SmallVector<SymbolBitMap, 2> assigned;

    /// Whether the control flow that arrived at this point is reachable.
    bool reachable = true;

    DataFlowState() = default;
    DataFlowState(DataFlowState&& other) = default;
    DataFlowState& operator=(DataFlowState&& other) = default;
};

/// The default concrete implementation of data flow analysis.
class SLANG_EXPORT DefaultDFA : public DataFlowAnalysis<DefaultDFA, DataFlowState> {
public:
    DefaultDFA(AnalysisContext& context, const Symbol& symbol, bool reportDiags) :
        DataFlowAnalysis(context, symbol, reportDiags) {}
};

} // namespace slang::analysis
