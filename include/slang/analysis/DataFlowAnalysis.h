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

    /// Constructs a new DataFlowAnalysis object.
    DataFlowAnalysis(AnalysisContext& context, const Symbol& symbol, bool reportDiags) :
        AFABase(symbol, context.manager->getOptions(),
                reportDiags ? &context.diagnostics : nullptr),
        DFAResults(context, this->getState().assigned), context(context),
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
        if (stmt.isForce) {
            prohibitLValue = true;
            this->visitStmt(stmt);
            prohibitLValue = false;
        }
        else {
            this->visitStmt(stmt);
        }
    }

    void handle(const AssignmentExpression& expr) {
        // Note that this method mirrors the logic in the base class
        // handler but we need to track the LValue status of the lhs.
        if (!prohibitLValue) {
            SLANG_ASSERT(!isLValue);
            isLValue = true;
            this->visit(expr.left());
            isLValue = false;
        }
        else {
            this->visit(expr.left());
        }

        if (!expr.isLValueArg())
            this->visit(expr.right());

        if (expr.timingControl)
            handleTiming(*expr.timingControl);
    }

    void handle(const CallExpression& expr) {
        expr.visitExprsNoArgs(*this);

        if (auto sysCall = std::get_if<CallExpression::SystemCallInfo>(&expr.subroutine)) {
            auto& sub = *sysCall->subroutine;

            size_t argIndex = 0;
            for (auto arg : expr.arguments()) {
                if (!sub.isArgUnevaluated(argIndex)) {
                    if (sub.isArgByRef(argIndex)) {
                        isLValue = true;
                        this->visit(*arg);
                        isLValue = false;
                    }
                    else {
                        this->visit(*arg);
                    }
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
                // expression generated for them but still act as output drivers.
                auto& formal = *formals[i];
                if (formal.direction == ArgumentDirection::Ref &&
                    !formal.flags.has(VariableFlags::Const)) {
                    isLValue = true;
                    this->visit(*args[i]);
                    isLValue = false;
                }
                else {
                    this->visit(*args[i]);
                }
            }
        }

        callExpressions.push_back(&expr);
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
    template<typename TOwner>
    friend struct ast::LSPVisitor;

    LSPVisitor<TDerived> lspVisitor;
    bool isLValue = false;
    bool prohibitLValue = false;

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
        auto guard = ScopeGuard([this, savedLVal = isLValue] { isLValue = savedLVal; });
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
