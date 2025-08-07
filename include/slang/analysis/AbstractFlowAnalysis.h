//------------------------------------------------------------------------------
//! @file AbstractFlowAnalysis.h
//! @brief Base class for flow analysis passes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/analysis/AnalysisOptions.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/util/FlatMap.h"
#include "slang/util/TypeTraits.h"

namespace slang::analysis {

using namespace ast;

/// A base class for flow analysis passes that contains
/// non-specialized helper functions.
class SLANG_EXPORT FlowAnalysisBase {
public:
    /// The symbol being analyzed (procedure, function, etc).
    const Symbol& rootSymbol;

    /// Various options controlling the behavior of the analysis.
    AnalysisOptions options;

    /// Set to true if the analysis detected an error.
    bool bad = false;

    /// Gets an evaluation context for use during analysis.
    EvalContext& getEvalContext() const { return evalContext; }

protected:
    /// Constructs a new flow analysis pass.
    FlowAnalysisBase(const Symbol& symbol, AnalysisOptions options,
                     Diagnostics* diagnostics = nullptr);

    ConstantValue tryEvalBool(const Expression& expr) const;

    enum class WillExecute { Yes, No, Maybe };
    WillExecute tryGetLoopIterValues(const ForLoopStatement& stmt,
                                     SmallVector<ConstantValue>& values,
                                     SmallVector<ConstantValue*>& localPtrs);

    bool isFullyCovered(const CaseStatement& stmt, const Statement* knownBranch,
                        bool isKnown) const;

    /// Tracking for how many steps we've taken while analyzing the body of a loop.
    uint32_t forLoopSteps = 0;

    /// An optional diagnostics collection. If provided, warnings encountered during
    /// analysis will be added to it.
    Diagnostics* diagnostics;

    /// An EvalContext that can be used for constant evaluation during analysis.
    mutable EvalContext evalContext;
};

/// An abstract class for flow analysis passes over SystemVerilog code.
///
/// This class provides a framework for implementing flow analysis passes
/// by modeling control flow through the AST. Derived classes implement
/// the actual state that gets tracked.
///
/// See background on lattice flow analysis:
/// https://en.wikipedia.org/wiki/Data-flow_analysis
/// https://clang.llvm.org/docs/DataFlowAnalysisIntro.html
///
template<typename TDerived, typename TState>
class AbstractFlowAnalysis : public FlowAnalysisBase {
#define DERIVED *static_cast<TDerived*>(this)
public:
    /// Run the analysis.
    void run(const Statement& stmt) {
        state = (DERIVED).topState();
        visit(stmt);
    }

    /// Run the analysis.
    void run(const Expression& expr) {
        state = (DERIVED).topState();
        visit(expr);
    }

protected:
    using FlowAnalysisBase::FlowAnalysisBase;

    /// Gets the current flow state.
    TState& getState() { return state; }

    /// Gets the current flow state.
    const TState& getState() const { return state; }

    /// Sets the current flow state to the given value.
    void setState(TState newState) {
        isStateSplit = false;
        state = std::move(newState);
        stateWhenTrue = {};
        stateWhenFalse = {};
    }

    /// Puts the current state into a split conditional state,
    /// with the provided true and false state values.
    void setConditionalState(TState whenTrue, TState whenFalse) {
        isStateSplit = true;
        state = {};
        stateWhenTrue = std::move(whenTrue);
        stateWhenFalse = std::move(whenFalse);
    }

    /// Splits the current state into separate true / false states.
    void split() {
        if (!isStateSplit) {
            auto copied = (DERIVED).copyState(state);
            setConditionalState(std::move(copied), std::move(state));
        }
    }

    /// Unsplits the current state if it was split by joining
    /// the true and false states.
    void unsplit() {
        if (isStateSplit) {
            (DERIVED).joinState(stateWhenTrue, stateWhenFalse);
            setState(std::move(stateWhenTrue));
        }
    }

    /// Sets the current state as unreachable.
    void setUnreachable() {
        SLANG_ASSERT(!isStateSplit);
        state = (DERIVED).unreachableState();
    }

    /// Gets the set of states at various return points in a subroutine.
    std::span<const TState> getReturnStates() const { return returnStates; }

    // **** Statement Visitors ****

    void visitStmt(const InvalidStatement&) { bad = true; }

    void visitStmt(const ExpressionStatement& stmt) { visit(stmt.expr); }
    void visitStmt(const TimedStatement& stmt) { visit(stmt.stmt); }
    void visitStmt(const EventTriggerStatement& stmt) { visit(stmt.target); }
    void visitStmt(const ProceduralAssignStatement& stmt) { visit(stmt.assignment); }
    void visitStmt(const ProceduralDeassignStatement& stmt) { visit(stmt.lvalue); }

    void visitStmt(const StatementList& stmt) {
        for (auto s : stmt.list)
            visit(*s);
    }

    void visitStmt(const BlockStatement& stmt) {
        // This block could be the target of a disable statement.
        if (stmt.blockSymbol) {
            auto [it, inserted] = disableBranches.try_emplace(stmt.blockSymbol,
                                                              SmallVector<TState>{});
            SLANG_ASSERT(inserted);
        }

        if (stmt.blockKind == StatementBlockKind::Sequential) {
            visit(stmt.body);
        }
        else {
            auto stmtPtr = &stmt.body;
            auto statements = stmt.body.kind == StatementKind::List
                                  ? stmt.body.as<StatementList>().list
                                  : std::span(&stmtPtr, 1);
            size_t numLocalDecls = 0;
            for (auto s : statements) {
                // Variable declaration initializers happen before
                // we fork the remaining statements.
                if (s->kind == StatementKind::VariableDeclaration) {
                    visit(*s);
                    numLocalDecls++;
                }
                else {
                    break;
                }
            }
            statements = statements.subspan(numLocalDecls);

            // Each remaining statement is executed in parallel.
            auto currState = (DERIVED).copyState(state);
            auto finalState = std::move(state);
            for (auto s : statements) {
                setState((DERIVED).copyState(currState));
                visit(*s);

                switch (stmt.blockKind) {
                    case StatementBlockKind::JoinAny:
                        // If there's only one statement (a pathological case)
                        // then we can meet it; otherwise we must join since
                        // there is uncertainty about which path was taken.
                        if (statements.size() == 1)
                            (DERIVED).meetState(finalState, state);
                        else
                            (DERIVED).joinState(finalState, state);
                        break;
                    case StatementBlockKind::JoinAll:
                        // All paths must be taken, so we meet the states.
                        (DERIVED).meetState(finalState, state);
                        break;
                    case StatementBlockKind::JoinNone:
                        // No paths will be taken by the time the fork
                        // moves on so we discard this state.
                        break;
                    default:
                        SLANG_UNREACHABLE;
                }
            }
            setState(std::move(finalState));
        }

        // Once we're done with a block we remove it as a disable target.
        // A disable statement can target any block in the hierarchy but
        // we don't analyze the control flow implications for targets that
        // aren't part of the current execution stack.
        if (stmt.blockSymbol) {
            auto it = disableBranches.find(stmt.blockSymbol);
            SLANG_ASSERT(it != disableBranches.end());

            for (auto& branchState : it->second)
                (DERIVED).joinState(state, branchState);

            disableBranches.erase(it);
        }
    }

    void visitStmt(const VariableDeclStatement& stmt) {
        // Static variables are not initialized as part of
        // the normal block flow, so they get ignored.
        if (stmt.symbol.lifetime != VariableLifetime::Static) {
            if (auto init = stmt.symbol.getInitializer())
                visit(*init);
        }
    }

    void visitStmt(const ReturnStatement& stmt) {
        if (stmt.expr)
            visit(*stmt.expr);

        returnStates.emplace_back(std::move(state));
        setUnreachable();
    }

    void visitStmt(const BreakStatement&) {
        breakStates.emplace_back(std::move(state));
        setUnreachable();
    }

    void visitStmt(const ContinueStatement&) { setUnreachable(); }

    void visitStmt(const DisableStatement& stmt) {
        // If the target is within our currently executing
        // hierarchy then we will jump to the end of it.
        // Otherwise we will ignore the disable statement.
        if (auto target = stmt.target.getSymbolReference()) {
            if (auto it = disableBranches.find(target); it != disableBranches.end()) {
                it->second.emplace_back(std::move(state));
                setUnreachable();
            }
            else if (target == &rootSymbol) {
                // This is possible for disable statements that target
                // the containing task.
                returnStates.emplace_back(std::move(state));
                setUnreachable();
            }
        }
    }

    void visitStmt(const ConditionalStatement& stmt) {
        auto falseState = (DERIVED).unreachableState();
        for (auto& cond : stmt.conditions) {
            visitCondition(*cond.expr);

            if (cond.pattern)
                visit(*cond.pattern);

            (DERIVED).joinState(falseState, stateWhenFalse);
            setState(std::move(stateWhenTrue));
        }

        visit(stmt.ifTrue);

        auto trueState = std::move(state);
        setState(std::move(falseState));
        if (stmt.ifFalse)
            visit(*stmt.ifFalse);

        (DERIVED).joinState(state, trueState);
    }

    void visitStmt(const CaseStatement& stmt) {
        visit(stmt.expr);

        // If the branch is known we can visit it explicitly,
        // otherwise we need to merge states for all case items.
        auto [knownBranch, isKnown] = stmt.getKnownBranch(evalContext);

        auto initialState = std::move(state);
        auto finalState = (DERIVED).unreachableState();

        for (auto& item : stmt.items) {
            if (isKnown && knownBranch != item.stmt)
                setUnreachable();
            else
                setState((DERIVED).copyState(initialState));

            for (auto itemExpr : item.expressions)
                visit(*itemExpr);

            visit(*item.stmt);
            (DERIVED).joinState(finalState, state);
        }

        // Determine whether the case statement has full coverage of all possible
        // inputs, such that we're guaranteed to select one of the case items.
        const bool covered = isFullyCovered(stmt, knownBranch, isKnown);

        if (stmt.defaultCase) {
            // If the case input is fully covered by item expressions,
            // or if we have a statically known branch that is not the
            // default, then we know the default case is never hit.
            if (covered || (isKnown && knownBranch != stmt.defaultCase))
                setUnreachable();
            else
                setState((DERIVED).copyState(initialState));

            visit(*stmt.defaultCase);
            (DERIVED).joinState(finalState, state);
        }
        else if (!isKnown && !covered) {
            // Branch is not statically known and the case input is
            // not fully covered, so we have to assume that no item
            // may be selected and that the initial state is relevant.
            (DERIVED).joinState(finalState, initialState);
        }

        setState(std::move(finalState));
    }

    void visitStmt(const PatternCaseStatement& stmt) {
        // TODO: match handling for regular CaseStatements
        visit(stmt.expr);

        auto initialState = std::move(state);
        auto finalState = (DERIVED).unreachableState();

        for (auto& item : stmt.items) {
            setState((DERIVED).copyState(initialState));

            visit(*item.pattern);

            if (item.filter) {
                visitCondition(*item.filter);
                setState(std::move(stateWhenTrue));
            }

            visit(*item.stmt);
            (DERIVED).joinState(finalState, state);
        }

        if (stmt.defaultCase) {
            setState((DERIVED).copyState(initialState));
            visit(*stmt.defaultCase);
            (DERIVED).joinState(finalState, state);
        }
        else {
            (DERIVED).joinState(finalState, initialState);
        }

        setState(std::move(finalState));
    }

    void visitStmt(const RandCaseStatement& stmt) {
        auto initialState = std::move(state);
        auto finalState = (DERIVED).unreachableState();
        bool anyReachable = false;

        for (auto& item : stmt.items) {
            setState((DERIVED).copyState(initialState));
            auto cv = visitCondition(*item.expr);
            anyReachable |= cv.isTrue();

            setState(std::move(stateWhenTrue));
            visit(*item.stmt);
            (DERIVED).joinState(finalState, state);
        }

        // If the final state is still unreachable then
        // none of the randcase items can ever be selected,
        // so take the initial state.
        if (anyReachable)
            setState(std::move(finalState));
        else
            setState(std::move(initialState));
    }

    void visitStmt(const ForLoopStatement& stmt) {
        for (auto init : stmt.initializers)
            visit(*init);

        for (auto var : stmt.loopVars) {
            if (auto init = var->getInitializer())
                visit(*init);
        }

        SmallVector<ConstantValue> iterValues;
        SmallVector<ConstantValue*> localPtrs;
        auto oldForLoopSteps = forLoopSteps;
        auto bodyWillExecute = WillExecute::Maybe;
        TState bodyState, exitState;
        if (stmt.stopExpr) {
            auto cv = visitCondition(*stmt.stopExpr);
            bodyState = std::move(stateWhenTrue);
            exitState = std::move(stateWhenFalse);

            // If we had a non-constant stop expression (which should be pretty rare)
            // we will try to determine whether the loop will iterate at least once
            // guaranteed, and if so whether we can know exactly how many times.
            // If we have a deterministic set of iteration values we can "unroll" the
            // loop and get finer grained tracking of data flow within it.
            if (!cv)
                bodyWillExecute = tryGetLoopIterValues(stmt, iterValues, localPtrs);
        }
        else {
            // If there's no stop expression, the loop is infinite.
            bodyState = std::move(state);
            exitState = (DERIVED).unreachableState();
        }

        auto oldBreakStates = std::move(breakStates);
        breakStates.clear();
        setState(std::move(bodyState));

        if (iterValues.empty()) {
            if (bodyWillExecute == WillExecute::No)
                setUnreachable();

            visit(stmt.body);
            for (auto step : stmt.steps)
                visit(*step);
        }
        else {
            // We have a set of iteration values that we can use to unroll the loop.
            for (size_t i = 0; i < iterValues.size();) {
                for (auto local : localPtrs)
                    *local = std::move(iterValues[i++]);

                // TODO: give up if state becomes unreachable?
                visit(stmt.body);
                for (auto step : stmt.steps)
                    visit(*step);
            }
        }

        // Clean up any locals we may have created.
        if (!localPtrs.empty()) {
            for (auto var : stmt.loopVars)
                evalContext.deleteLocal(var);
        }

        forLoopSteps = oldForLoopSteps;

        if (bodyWillExecute == WillExecute::Yes)
            (DERIVED).meetState(exitState, state);

        loopTail(std::move(exitState), std::move(oldBreakStates));
    }

    void visitStmt(const RepeatLoopStatement& stmt) {
        auto cv = visitCondition(stmt.count);
        unsplit();

        auto currState = (DERIVED).copyState(state);
        auto oldBreakStates = std::move(breakStates);
        breakStates.clear();
        visit(stmt.body);

        // If the repeat count is known to be positive we know the
        // body will execute at least once so we can keep our current
        // state; otherwise we need to join with the pre-loop state.
        if (cv.isTrue())
            loopTail(std::move(state), std::move(oldBreakStates));
        else
            loopTail(std::move(currState), std::move(oldBreakStates));
    }

    void visitStmt(const ForeachLoopStatement& stmt) {
        visit(stmt.arrayRef);

        auto currState = (DERIVED).copyState(state);
        auto oldBreakStates = std::move(breakStates);
        breakStates.clear();
        visit(stmt.body);

        // If all loop dims are fixed size then the loop is guaranteed to execute.
        bool allFixed = !stmt.loopDims.empty();
        for (auto& dim : stmt.loopDims) {
            if (dim.loopVar && !dim.range) {
                allFixed = false;
                break;
            }
        }

        if (allFixed)
            loopTail(std::move(state), std::move(oldBreakStates));
        else
            loopTail(std::move(currState), std::move(oldBreakStates));
    }

    void visitStmt(const WhileLoopStatement& stmt) {
        visitCondition(stmt.cond);

        auto exitState = std::move(stateWhenFalse);
        setState(std::move(stateWhenTrue));

        auto oldBreakStates = std::move(breakStates);
        breakStates.clear();
        visit(stmt.body);

        loopTail(std::move(exitState), std::move(oldBreakStates));
    }

    void visitStmt(const DoWhileLoopStatement& stmt) {
        auto oldBreakStates = std::move(breakStates);
        breakStates.clear();
        visit(stmt.body);

        visitCondition(stmt.cond);

        loopTail(std::move(stateWhenFalse), std::move(oldBreakStates));
    }

    void visitStmt(const ForeverLoopStatement& stmt) {
        auto oldBreakStates = std::move(breakStates);
        breakStates.clear();
        visit(stmt.body);

        // The exit state is by default unreachable but
        // if there are break statements that could change.
        loopTail((DERIVED).unreachableState(), std::move(oldBreakStates));
    }

    void visitStmt(const WaitStatement& stmt) {
        visitCondition(stmt.cond);

        // The body is never executed until the condition is true.
        setState(std::move(stateWhenTrue));
        visit(stmt.stmt);
    }

    void visitStmt(const WaitOrderStatement& stmt) {
        for (auto expr : stmt.events)
            visit(*expr);

        auto initialState = (DERIVED).copyState(state);
        if (stmt.ifTrue) {
            visit(*stmt.ifTrue);
            std::swap(state, initialState);
        }

        if (stmt.ifFalse)
            visit(*stmt.ifFalse);

        (DERIVED).joinState(state, initialState);
    }

    void visitStmt(const RandSequenceStatement& stmt) {
        // TODO: could check for unreachable productions
        // TODO: handle special break / return rules
        auto initialState = (DERIVED).copyState(state);
        auto finalState = std::move(state);

        for (auto production : stmt.productions) {
            for (auto& rule : production->getRules()) {
                setState((DERIVED).copyState(initialState));

                if (rule.weightExpr)
                    visit(*rule.weightExpr);

                if (rule.randJoinExpr)
                    visit(*rule.randJoinExpr);

                using RSPS = RandSeqProductionSymbol;

                for (auto prod : rule.prods) {
                    switch (prod->kind) {
                        case RSPS::ProdKind::Item:
                            ((const RSPS::ProdItem*)prod)->visitExprs(DERIVED);
                            break;
                        case RSPS::ProdKind::CodeBlock: {
                            auto blockBody =
                                ((const RSPS::CodeBlockProd*)prod)->block->tryGetStatement();
                            if (blockBody)
                                visit(*blockBody);
                            break;
                        }
                        case RSPS::ProdKind::IfElse: {
                            auto& iep = *(const RSPS::IfElseProd*)prod;
                            visitCondition(*iep.expr);

                            auto falseState = std::move(stateWhenFalse);
                            setState(std::move(stateWhenTrue));
                            iep.ifItem.visitExprs(DERIVED);

                            auto trueState = std::move(state);
                            setState(std::move(falseState));
                            if (iep.elseItem)
                                iep.elseItem->visitExprs(DERIVED);

                            (DERIVED).joinState(state, trueState);
                            break;
                        }
                        case RSPS::ProdKind::Repeat: {
                            auto& rp = *(const RSPS::RepeatProd*)prod;
                            visit(*rp.expr);

                            auto currState = (DERIVED).copyState(state);
                            rp.item.visitExprs(DERIVED);

                            setState(std::move(currState));
                            break;
                        }
                        case RSPS::ProdKind::Case: {
                            auto& cp = *(const RSPS::CaseProd*)prod;
                            visit(*cp.expr);

                            auto caseInitial = std::move(state);
                            auto caseFinal = (DERIVED).unreachableState();

                            for (auto& item : cp.items) {
                                setState((DERIVED).copyState(caseInitial));
                                for (auto itemExpr : item.expressions)
                                    visit(*itemExpr);

                                item.item.visitExprs(DERIVED);
                                (DERIVED).joinState(caseFinal, state);
                            }

                            if (cp.defaultItem) {
                                setState((DERIVED).copyState(caseInitial));
                                cp.defaultItem->visitExprs(DERIVED);
                                (DERIVED).joinState(caseFinal, state);
                            }
                            else {
                                (DERIVED).joinState(caseFinal, caseInitial);
                            }

                            setState(std::move(caseFinal));
                            break;
                        }
                    }
                }

                if (rule.codeBlock) {
                    if (auto blockBody = rule.codeBlock->block->tryGetStatement())
                        visit(*blockBody);
                }

                (DERIVED).joinState(finalState, state);
            }
        }

        setState(std::move(finalState));
    }

    void visitStmt(const ImmediateAssertionStatement& stmt) {
        visitCondition(stmt.cond);

        if (stmt.isDeferred) {
            // Deferred assertion action blocks don't execute until
            // a later phase of simulation so ignore them here.
            unsplit();
        }
        else {
            auto trueState = std::move(stateWhenTrue), falseState = std::move(stateWhenFalse);
            if (stmt.ifTrue) {
                setState(std::move(trueState));
                visit(*stmt.ifTrue);
                trueState = std::move(state);
            }

            setState(std::move(falseState));
            if (stmt.ifFalse)
                visit(*stmt.ifFalse);

            (DERIVED).joinState(state, trueState);
        }
    }

    void visitStmt(const ConcurrentAssertionStatement&) {
        // Concurrent assertions do not affect the immediate control
        // or data flow. However, we may want to visit the assertion
        // expression in the future because the current values of automatic
        // variables and const expressions are captured here, though right
        // now nothing depends on us doing that.
    }

    void visitStmt(const ProceduralCheckerStatement&) {
        // Similarly to concurrent assertions, procedural checkers
        // do not affect the immediate control or data flow but they
        // can take arguments which we may want to model.
    }

    // Nothing to do for these statements.
    void visitStmt(const EmptyStatement&) {}
    void visitStmt(const WaitForkStatement&) {}
    void visitStmt(const DisableForkStatement&) {}

    // **** Expression Visitors ****

    void visitExpr(const InvalidExpression&) { bad = true; }

    void visitExpr(const UnaryExpression& expr) {
        // For logical not we can treat it as a condition
        // that flips its states.
        if (expr.op == UnaryOperator::LogicalNot) {
            visitCondition(expr.operand());
            setConditionalState(std::move(stateWhenFalse), std::move(stateWhenTrue));
        }
        else {
            visit(expr.operand());
        }
    }

    void visitExpr(const BinaryExpression& expr) {
        if (OpInfo::isShortCircuit(expr.op)) {
            visitShortCircuitOp(expr);
            return;
        }

        if (OpInfo::isComparison(expr.op) || expr.op == BinaryOperator::LogicalEquivalence)
            tryEvalBool(expr);

        visit(expr.left());
        visit(expr.right());
    }

    void visitExpr(const InsideExpression& expr) {
        tryEvalBool(expr);
        visit(expr.left());
        for (auto range : expr.rangeList())
            visit(*range);
    }

    void visitShortCircuitOp(const BinaryExpression& expr) {
        // Visit the LHS -- after this the state is guaranteed to be split.
        visitCondition(expr.left());

        // The state when visiting the RHS depends on the operator;
        // for logical OR we know we won't visit the RHS unless the
        // LHS is false, so we can set the state to the false state.
        // The opposite is true for logical AND and implication.
        auto trueState = std::move(stateWhenTrue), falseState = std::move(stateWhenFalse);
        setState(expr.op == BinaryOperator::LogicalOr ? std::move(falseState)
                                                      : std::move(trueState));
        visitCondition(expr.right());

        // Join the states from the two branches. For example,
        // for logical OR, we only got here if the LHS was false
        // so we join the true state with the true state after visiting
        // the RHS, since either being true leads to the same outcome.
        if (expr.op == BinaryOperator::LogicalOr)
            (DERIVED).joinState(stateWhenTrue, trueState);
        else if (expr.op == BinaryOperator::LogicalAnd)
            (DERIVED).joinState(stateWhenFalse, falseState);
        else {
            // Reminder that logical implication (a -> b) is
            // equivalent to (!a || b)
            SLANG_ASSERT(expr.op == BinaryOperator::LogicalImplication);
            (DERIVED).joinState(stateWhenTrue, falseState);
        }

        // Allow the full binary operator to set a constant
        // state if the full expression is constant.
        adjustConditionalState(expr);
    }

    void visitExpr(const ConditionalExpression& expr) {
        // TODO: handle the special ambiguous 'x merging of both sides
        ConstantValue knownVal = SVInt::One;
        auto falseState = (DERIVED).unreachableState();
        for (auto& cond : expr.conditions) {
            auto cv = visitCondition(*cond.expr);
            if (cv && knownVal)
                knownVal = SVInt(knownVal.isTrue() && cv.isTrue() ? 1 : 0);
            else
                knownVal = nullptr;

            if (cond.pattern)
                visit(*cond.pattern);

            (DERIVED).joinState(falseState, stateWhenFalse);
            setState(std::move(stateWhenTrue));
        }

        auto visitSide = [this](const Expression& expr, TState&& newState) {
            setState(std::move(newState));
            visitNoJoin(expr);
        };

        auto trueState = std::move(state);
        if (knownVal) {
            // Special case: if the condition is constant, we will visit
            // the opposing side first and then essentially throw that
            // state away instead of joining it.
            if (knownVal.isTrue()) {
                visitSide(expr.right(), std::move(falseState));
                visitSide(expr.left(), std::move(trueState));
            }
            else {
                visitSide(expr.left(), std::move(trueState));
                visitSide(expr.right(), std::move(falseState));
            }
        }
        else {
            // Otherwise visit both sides and join as needed.
            visitSide(expr.left(), std::move(trueState));

            bool conditionalAfterLeft = isStateSplit;
            TState trueAfterLeft, falseAfterLeft;
            if (conditionalAfterLeft) {
                trueAfterLeft = std::move(stateWhenTrue);
                falseAfterLeft = std::move(stateWhenFalse);
            }
            else {
                trueAfterLeft = (DERIVED).copyState(state);
                falseAfterLeft = std::move(state);
            }

            visitSide(expr.right(), std::move(falseState));
            if (!conditionalAfterLeft && !isStateSplit) {
                (DERIVED).joinState(state, trueAfterLeft);
            }
            else {
                split();
                (DERIVED).joinState(stateWhenTrue, trueAfterLeft);
                (DERIVED).joinState(stateWhenFalse, falseAfterLeft);
            }
        }
    }

    void visitExpr(const AssignmentExpression& expr) {
        // Of note, if this is a nonblocking assignment we
        // still visit the left and right sides now, but the
        // actual assignment won't happen immediately.
        visit(expr.left());
        if (!expr.isLValueArg())
            visit(expr.right());
    }

    void visitExpr(const CallExpression& expr) {
        expr.visitExprsNoArgs(DERIVED);

        auto sysCall = std::get_if<CallExpression::SystemCallInfo>(&expr.subroutine);
        size_t argIndex = 0;
        for (auto arg : expr.arguments()) {
            if (!sysCall || !sysCall->subroutine->isArgUnevaluated(argIndex))
                visit(*arg);
            argIndex++;
        }

        if (sysCall && sysCall->subroutine->neverReturns)
            setUnreachable();
    }

    void visitExpr(const MinTypMaxExpression& expr) {
        // Only the selected expression is actually evaluated.
        visitNoJoin(expr.selected());
    }

    void visitExpr(const ConversionExpression& expr) { visitNoJoin(expr.operand()); }

    void visitExpr(const AssertionInstanceExpression&) {
        // The assertion instance doesn't affect control flow but
        // we may want to model the argument passing in the future.
    }

    // None of these affect control or data flow state.
    void visitExpr(const IntegerLiteral&) {}
    void visitExpr(const RealLiteral&) {}
    void visitExpr(const TimeLiteral&) {}
    void visitExpr(const UnbasedUnsizedIntegerLiteral&) {}
    void visitExpr(const NullLiteral&) {}
    void visitExpr(const UnboundedLiteral&) {}
    void visitExpr(const StringLiteral&) {}
    void visitExpr(const NamedValueExpression&) {}
    void visitExpr(const HierarchicalValueExpression&) {}
    void visitExpr(const DataTypeExpression&) {}
    void visitExpr(const TypeReferenceExpression&) {}
    void visitExpr(const ArbitrarySymbolExpression&) {}
    void visitExpr(const EmptyArgumentExpression&) {}
    void visitExpr(const ClockingEventExpression&) {}
    void visitExpr(const LValueReferenceExpression&) {}

    // These all just use the default behavior of visiting their children.
    template<typename T>
        requires(IsAnyOf<T, ConcatenationExpression, ReplicationExpression,
                         StreamingConcatenationExpression, ElementSelectExpression,
                         RangeSelectExpression, MemberAccessExpression,
                         SimpleAssignmentPatternExpression, StructuredAssignmentPatternExpression,
                         ReplicatedAssignmentPatternExpression, ValueRangeExpression,
                         DistExpression, NewArrayExpression, NewClassExpression,
                         NewCovergroupExpression, CopyClassExpression, TaggedUnionExpression>)
    void visitExpr(const T& expr) {
        expr.visitExprs(DERIVED);
    }

    // This is the primary visitor function; if provided a base type
    // (expression or statement) it will dispatch to the concrete type
    // using the AST visitor system. Otherwise if our derived analysis
    // class provides a handler we will call that, and if not we will
    // dispatch to our own handler for that concrete type.
    template<typename T>
        requires(std::is_base_of_v<Statement, T> || std::is_base_of_v<Expression, T> ||
                 std::is_base_of_v<Constraint, T> || std::is_base_of_v<Pattern, T>)
    void visit(const T& t) {
        if constexpr (std::is_same_v<T, Statement> || std::is_same_v<T, Expression> ||
                      std::is_same_v<T, Constraint> || std::is_same_v<T, Pattern>) {
            // We don't have a concrete type, we need to dispatch.
            t.visit(DERIVED);
        }
        else {
            // If the derived type provides a handler then dispatch to it.
            // Otherwise dispatch to our own handler for whatever this is.
            if constexpr (requires { (DERIVED).handle(t); })
                (DERIVED).handle(t);
            else if constexpr (std::is_base_of_v<Statement, T>)
                visitStmt(t);
            else if constexpr (std::is_base_of_v<Expression, T>)
                visitExpr(t);
            else if constexpr (std::is_base_of_v<Constraint, T> || std::is_base_of_v<Pattern, T>)
                t.visitExprs(DERIVED);
            else
                static_assert(always_false<T>::value);

            if constexpr (std::is_base_of_v<Statement, T>) {
                // Sanity check that we finished all split state at
                // the end of the statement.
                SLANG_ASSERT(!isStateSplit);
                SLANG_ASSERT(!inCondition);
            }
            else if constexpr (std::is_base_of_v<Expression, T> ||
                               std::is_base_of_v<Constraint, T> || std::is_base_of_v<Pattern, T>) {
                // Note: most expressions don't create branches, but there are
                // a few that do:
                // - conditional operator
                // - short circuiting binary operators
                // Usually we want to rejoin states after visiting expressions,
                // unless we're visiting a condition or a child of one of the
                // previously mentioned expressions.
                if (!inCondition)
                    unsplit();
            }
        }
    }

private:
    friend class ast::Expression;
    friend class ast::Statement;
    friend class ast::Constraint;
    friend class ast::Pattern;

    TState state;
    TState stateWhenTrue;
    TState stateWhenFalse;
    bool isStateSplit = false;
    bool inCondition = false;

    SmallVector<TState> breakStates;
    SmallVector<TState> returnStates;
    flat_hash_map<const Symbol*, SmallVector<TState>> disableBranches;

    template<typename T>
    struct always_false : std::false_type {};

    ConstantValue adjustConditionalState(const Expression& expr) {
        auto cv = tryEvalBool(expr);
        if (cv) {
            unsplit();
            if (cv.isTrue())
                setConditionalState(std::move(state), (DERIVED).unreachableState());
            else
                setConditionalState((DERIVED).unreachableState(), std::move(state));
        }
        else {
            split();
        }
        return cv;
    }

    void loopTail(TState exitState, SmallVector<TState>&& oldBreakStates) {
        for (auto& bs : breakStates)
            (DERIVED).joinState(exitState, bs);

        breakStates = std::move(oldBreakStates);
        setState(std::move(exitState));
    }

    void visitNoJoin(const Expression& expr) {
        // Visit the expression without joining states afterward.
        auto prevInCondition = std::exchange(inCondition, true);
        visit(expr);
        inCondition = prevInCondition;
    }

    ConstantValue visitCondition(const Expression& expr) {
        visitNoJoin(expr);
        return adjustConditionalState(expr);
    }

#undef DERIVED
};

} // namespace slang::analysis
