//------------------------------------------------------------------------------
//! @file AbstractFlowAnalysis.h
//! @brief Base class for flow analysis passes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/EvalContext.h"
#include "slang/util/FlatMap.h"

namespace slang::analysis {

using namespace ast;

template<typename T, typename... U>
concept IsAnyOf = (std::same_as<T, U> || ...);

/// A base class for flow analysis passes.
///
/// Formally, this is a fairly conventional lattice flow analysis
/// (<see href="https://en.wikipedia.org/wiki/Data-flow_analysis"/>).
template<typename TDerived, typename TState>
class AbstractFlowAnalysis {
#define DERIVED *static_cast<TDerived*>(this)
public:
    /// The symbol being analyzed (procedure, function, etc).
    const Symbol& rootSymbol;

    /// Set to true if the analysis detected an error.
    bool bad = false;

    /// Run the analysis.
    void run(const Statement& stmt) {
        state = (DERIVED).topState();
        visit(stmt);
    }

protected:
    /// Constructs a new flow analysis pass and runs the analysis.
    AbstractFlowAnalysis(const Symbol& symbol) :
        rootSymbol(symbol),
        evalContext(ASTContext(*symbol.getParentScope(), LookupLocation::after(symbol))) {}

    /// Gets the current state.
    TState& getState() { return state; }
    const TState& getState() const { return state; }

    EvalContext& getEvalContext() { return evalContext; }

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

    /// Splits the current state into two separate states.
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

    // **** Statement Visitors ****

    void visitStmt(const InvalidStatement&) { bad = true; }

    void visitStmt(const ExpressionStatement& stmt) { visit(stmt.expr); }
    void visitStmt(const TimedStatement& stmt) { visit(stmt.stmt); }
    void visitStmt(const EventTriggerStatement& stmt) { visit(stmt.target); }

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
        // TODO: pending branch
        if (stmt.expr)
            visit(*stmt.expr);
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
        }
    }

    void visitStmt(const ConditionalStatement& stmt) {
        auto falseState = (DERIVED).unreachableState();
        for (auto& cond : stmt.conditions) {
            visitCondition(*cond.expr);

            if (cond.pattern)
                visitPattern(*cond.pattern);

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
        // TODO: we could be smarter for constant case conditions
        visit(stmt.expr);

        auto initialState = (DERIVED).copyState(state);
        auto finalState = std::move(state);

        for (auto& item : stmt.items) {
            setState((DERIVED).copyState(initialState));
            for (auto itemExpr : item.expressions)
                visit(*itemExpr);

            visit(*item.stmt);
            (DERIVED).joinState(finalState, state);
        }

        if (stmt.defaultCase) {
            setState((DERIVED).copyState(initialState));
            visit(*stmt.defaultCase);
            (DERIVED).joinState(finalState, state);
        }

        setState(std::move(finalState));
    }

    void visitStmt(const PatternCaseStatement& stmt) {
        visit(stmt.expr);

        auto initialState = (DERIVED).copyState(state);
        auto finalState = std::move(state);

        for (auto& item : stmt.items) {
            setState((DERIVED).copyState(initialState));

            visitPattern(*item.pattern);

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

        setState(std::move(finalState));
    }

    void visitStmt(const RandCaseStatement& stmt) {
        auto initialState = (DERIVED).copyState(state);
        auto finalState = std::move(state);
        for (auto& item : stmt.items) {
            setState((DERIVED).copyState(initialState));
            visit(*item.expr);
            visit(*item.stmt);
            (DERIVED).joinState(finalState, state);
        }

        setState(std::move(finalState));
    }

    void visitStmt(const ForLoopStatement& stmt) {
        for (auto init : stmt.initializers)
            visit(*init);

        for (auto var : stmt.loopVars) {
            if (auto init = var->getInitializer())
                visit(*init);
        }

        TState bodyState, exitState;
        if (stmt.stopExpr) {
            visitCondition(*stmt.stopExpr);
            bodyState = std::move(stateWhenTrue);
            exitState = std::move(stateWhenFalse);
        }
        else {
            // If there's no stop expression, the loop is infinite.
            bodyState = std::move(state);
            exitState = (DERIVED).unreachableState();
        }

        auto oldBreakStates = std::move(breakStates);
        breakStates.clear();
        setState(std::move(bodyState));
        visit(stmt.body);

        for (auto step : stmt.steps)
            visit(*step);

        loopTail(std::move(exitState), std::move(oldBreakStates));
    }

    void visitStmt(const RepeatLoopStatement& stmt) {
        // TODO: we could infer more information from the repeat count
        // when it's a constant.
        visit(stmt.count);

        auto currState = (DERIVED).copyState(state);
        auto oldBreakStates = std::move(breakStates);
        breakStates.clear();
        visit(stmt.body);

        loopTail(std::move(currState), std::move(oldBreakStates));
    }

    void visitStmt(const ForeachLoopStatement& stmt) {
        visit(stmt.arrayRef);

        auto currState = (DERIVED).copyState(state);
        auto oldBreakStates = std::move(breakStates);
        breakStates.clear();
        visit(stmt.body);

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

                            auto caseInitial = (DERIVED).copyState(state);
                            auto caseFinal = std::move(state);

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

                            setState(std::move(caseFinal));
                            break;
                        }
                        default:
                            SLANG_UNREACHABLE;
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

    // Nothing to do for these statements.
    void visitStmt(const EmptyStatement&) {}
    void visitStmt(const WaitForkStatement&) {}
    void visitStmt(const DisableForkStatement&) {}

    void visitStmt(const ProceduralAssignStatement&) { SLANG_UNREACHABLE; }
    void visitStmt(const ProceduralDeassignStatement&) { SLANG_UNREACHABLE; }
    void visitStmt(const ProceduralCheckerStatement&) { SLANG_UNREACHABLE; }

    // **** Expression Visitors ****

    void visitExpr(const InvalidExpression&) { bad = true; }

    void visitExpr(const UnaryExpression& expr) {
        // For logical not, give a chance to evaluate the operand
        // to allow for warning on incorrect logic operators.
        if (expr.op == UnaryOperator::LogicalNot)
            tryEvalBool(expr.operand());
        visit(expr.operand());
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
                visitPattern(*cond.pattern);

            (DERIVED).joinState(falseState, stateWhenFalse);
            setState(std::move(stateWhenTrue));
        }

        auto visitSide = [this](const Expression& expr, TState&& newState) {
            setState(std::move(newState));
            visit(expr);
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
        if (!expr.isLValueArg()) {
            // If this is a compound assignment we should skip the
            // generated lvalue reference expression.
            if (expr.isCompound()) {
                auto& binExpr = expr.right().as<BinaryExpression>();
                SLANG_ASSERT(binExpr.left().kind == ExpressionKind::LValueReference);
                visit(binExpr.right());
            }
            else {
                visit(expr.right());
            }
        }
    }

    void visitExpr(const CallExpression& expr) {
        if (expr.thisClass())
            visit(*expr.thisClass());

        // TODO: consider default values
        // TODO: randomize calls, iterator calls
        // TODO: omit arguments if they are for a system function
        //       that doesn't actually evaluate them.
        for (auto arg : expr.arguments())
            visit(*arg);
    }

    void visitExpr(const MinTypMaxExpression& expr) {
        // Only the selected expression is actually evaluated.
        visit(expr.selected());
    }

    // TODO: add support
    void visitExpr(const AssertionInstanceExpression&) { SLANG_UNREACHABLE; }

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
                         RangeSelectExpression, MemberAccessExpression, ConversionExpression,
                         SimpleAssignmentPatternExpression, StructuredAssignmentPatternExpression,
                         ReplicatedAssignmentPatternExpression, ValueRangeExpression,
                         DistExpression, NewArrayExpression, NewClassExpression,
                         NewCovergroupExpression, CopyClassExpression, TaggedUnionExpression>)
    void visitExpr(const T& expr) {
        expr.visitExprs(DERIVED);
    }

private:
    friend class ast::Expression;
    friend class ast::Statement;

    TState state;
    TState stateWhenTrue;
    TState stateWhenFalse;
    bool isStateSplit = false;
    EvalContext evalContext;

    SmallVector<TState> breakStates;
    flat_hash_map<const Symbol*, SmallVector<TState>> disableBranches;

    template<typename T>
    struct always_false : std::false_type {};

    // This is the primary visitor function; if provided a base type
    // (expression or statement) it will dispatch to the concrete type
    // using the AST visitor system. Otherwise if our derived analysis
    // class provides a handler we will call that, and if not we will
    // dispatch to our own handler for that concrete type.
    template<typename T>
        requires(std::is_base_of_v<Statement, T> || std::is_base_of_v<Expression, T>)
    void visit(const T& t) {
        if constexpr (std::is_same_v<T, Statement> || std::is_same_v<T, Expression>) {
            // We don't have a concrete type, we need to dispatch.
            t.visit(DERIVED);
        }
        else {
            // If the derived type provides a handler then dispatch to it.
            // Otherwise dispatch to our own handler for whatever this is.
            if constexpr (requires { (DERIVED).handle(t); }) {
                (DERIVED).handle(t);
            }
            else if constexpr (std::is_base_of_v<Statement, T>) {
                visitStmt(t);
                SLANG_ASSERT(!isStateSplit);
            }
            else if constexpr (std::is_base_of_v<Expression, T>) {
                visitExpr(t);
            }
            else {
                static_assert(always_false<T>::value);
            }

            if constexpr (std::is_base_of_v<Statement, T>) {
                // Sanity check that we finished all split state at
                // the end of the statement.
                SLANG_ASSERT(!isStateSplit);
            }
        }
    }

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

    ConstantValue visitCondition(const Expression& expr) {
        visit(expr);
        return adjustConditionalState(expr);
    }

    void visitPattern(const Pattern&) {
        // For now this does nothing, but we may want to change
        // that in the future if we want to do analysis on the
        // variables introduced by patterns.
    }

    ConstantValue tryEvalBool(const Expression& expr) { return expr.eval(evalContext); }

#undef DERIVED
};

} // namespace slang::analysis
