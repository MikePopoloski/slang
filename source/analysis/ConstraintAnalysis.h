//------------------------------------------------------------------------------
// ConstraintAnalysis.h
// Analysis of rand variable ordering in constraint blocks
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Constraints.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/diagnostics/AnalysisDiags.h"
#include "slang/util/FlatMap.h"
#include "slang/util/SmallVector.h"

namespace slang::analysis {

using namespace ast;

namespace {

// Walks a constraint expression to collect rand variable references, tracking
// whether each appears in a function argument position (which gives it higher
// implicit priority) or a non-argument position.
struct FuncArgVarCollector {
    // Rand vars that appear as arguments to user-defined function calls,
    // paired with the source range of the argument expression.
    SmallVector<std::pair<const Symbol*, SourceRange>> argVars;

    // Rand vars that appear outside of user-defined function call arguments.
    SmallVector<const Symbol*> nonArgVars;

    bool inFuncArg = false;

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_base_of_v<ValueExpressionBase, T>) {
            if (auto sym = expr.getSymbolReference()) {
                if (sym->getRandMode() != RandMode::None) {
                    if (inFuncArg)
                        argVars.push_back({sym, expr.sourceRange});
                    else
                        nonArgVars.push_back(sym);
                }
            }
            return;
        }

        if constexpr (std::is_same_v<T, CallExpression>) {
            if (!expr.isSystemCall()) {
                // Arguments to user-defined functions are in func-arg position,
                // giving those rand vars higher implicit priority.
                bool saved = std::exchange(inFuncArg, true);
                for (auto arg : expr.arguments())
                    arg->visit(*this);
                inFuncArg = saved;
                return;
            }
        }

        if constexpr (HasVisitExprs<T, FuncArgVarCollector>)
            expr.visitExprs(*this);
    }
};

struct ConstraintGraph {
    ConstraintGraph(AnalysisContext& context, const Symbol& rootSym) :
        context(context), rootSym(rootSym) {}

    void add(const Constraint& c) {
        switch (c.kind) {
            case ConstraintKind::List:
                for (auto item : c.as<ConstraintList>().list)
                    add(*item);
                return;
            case ConstraintKind::Expression: {
                FuncArgVarCollector collector;
                c.as<ExpressionConstraint>().expr.visit(collector);

                // For each (arg_var, non_arg_var) pair, arg_var must be solved first.
                for (auto& [argSym, argRange] : collector.argVars) {
                    for (auto nonArgSym : collector.nonArgVars) {
                        if (argSym != nonArgSym) {
                            funcArgEdges[argSym].emplace_back(nonArgSym, argRange);
                            funcArgNodes.insert(argSym);
                            funcArgNodes.insert(nonArgSym);
                        }
                    }
                }
                return;
            }
            case ConstraintKind::Implication:
                add(c.as<ImplicationConstraint>().body);
                return;
            case ConstraintKind::Conditional: {
                auto& cond = c.as<ConditionalConstraint>();
                add(cond.ifBody);
                if (cond.elseBody)
                    add(*cond.elseBody);
                return;
            }
            case ConstraintKind::Foreach:
                add(c.as<ForeachConstraint>().body);
                return;
            case ConstraintKind::SolveBefore: {
                auto& sb = c.as<SolveBeforeConstraint>();
                for (auto solveExpr : sb.solve) {
                    auto solveSym = solveExpr->getSymbolReference();
                    if (!solveSym)
                        continue;

                    for (auto afterExpr : sb.after) {
                        auto afterSym = afterExpr->getSymbolReference();
                        if (!afterSym || afterSym == solveSym)
                            continue;

                        solveBeforeEdges[solveSym].emplace_back(afterSym, solveExpr->sourceRange);
                        solveBeforeNodes.insert(solveSym);
                        solveBeforeNodes.insert(afterSym);
                    }
                }
                return;
            }
            case ConstraintKind::Invalid:
            case ConstraintKind::Uniqueness:
            case ConstraintKind::DisableSoft:
                return;
        }
        SLANG_UNREACHABLE;
    }

    // Runs cycle detection for both edge sets in sequence.
    void findAllCycles() {
        findCycles(funcArgEdges, funcArgNodes, diag::ConstraintFuncArgCycle,
                   diag::NoteConstraintFuncArgOrder);
        visited.clear();
        onStack.clear();
        path.clear();
        findCycles(solveBeforeEdges, solveBeforeNodes, diag::ConstraintSolveCycle,
                   diag::NoteConstraintSolveBeforeEdge);
    }

private:
    using EdgeMap =
        flat_hash_map<const Symbol*, SmallVector<std::pair<const Symbol*, SourceRange>>>;

    void findCycles(const EdgeMap& edges, const flat_hash_set<const Symbol*>& nodes,
                    DiagCode cycleDiag, DiagCode edgeDiag) {
        for (auto node : nodes) {
            if (!visited.count(node)) {
                if (!dfs(node, edges, cycleDiag, edgeDiag))
                    return;
            }
        }
    }

    bool dfs(const Symbol* v, const EdgeMap& edges, DiagCode cycleDiag, DiagCode edgeDiag) {
        visited.insert(v);
        onStack.insert(v);
        path.push_back({v, {}});

        if (auto it = edges.find(v); it != edges.end()) {
            for (auto& [neighbor, srcRange] : it->second) {
                // Record the outgoing edge range for the current node in the path.
                path.back().second = srcRange;

                if (onStack.count(neighbor)) {
                    reportCycle(neighbor, cycleDiag, edgeDiag);
                    return false;
                }

                if (!visited.count(neighbor)) {
                    if (!dfs(neighbor, edges, cycleDiag, edgeDiag))
                        return false;
                }
            }
        }

        path.pop_back();
        onStack.erase(v);
        return true;
    }

    void reportCycle(const Symbol* neighbor, DiagCode cycleDiag, DiagCode edgeDiag) {
        // Found a back edge: extract the cycle from the current path.
        SmallVector<std::pair<const Symbol*, SourceRange>> cycle;
        bool inCycle = false;
        for (auto& entry : path) {
            if (entry.first == neighbor)
                inCycle = true;
            if (inCycle)
                cycle.push_back(entry);
        }
        // cycle[i].second is the edge range from cycle[i].first to
        // cycle[(i+1) % N].first.

        auto& diag = context.addDiag(rootSym, cycleDiag, cycle[0].first->location);
        diag << cycle[0].first->name;

        for (size_t i = 0; i < cycle.size(); i++) {
            auto nextVar = cycle[(i + 1) % cycle.size()].first;
            diag.addNote(edgeDiag, cycle[i].second) << cycle[i].first->name << nextVar->name;
        }
    }

    EdgeMap funcArgEdges;
    flat_hash_set<const Symbol*> funcArgNodes;
    EdgeMap solveBeforeEdges;
    flat_hash_set<const Symbol*> solveBeforeNodes;

    flat_hash_set<const Symbol*> visited;
    flat_hash_set<const Symbol*> onStack;
    SmallVector<std::pair<const Symbol*, SourceRange>> path;

    AnalysisContext& context;
    const Symbol& rootSym;
};

} // namespace

// Checks all constraint blocks directly declared in the given scope for:
//   - circular dependencies in the implicit variable ordering created by
//     function call arguments (LRM 18.5.11)
//   - circular dependencies created by explicit 'solve...before' directives
//     (LRM 18.5.9)
void analyzeConstraints(AnalysisContext& context, const Scope& scope) {
    ConstraintGraph graph(context, scope.asSymbol());
    for (auto& member : scope.members()) {
        const Symbol* sym = &member;
        while (sym->kind == SymbolKind::TransparentMember)
            sym = &sym->as<TransparentMemberSymbol>().wrapped;

        if (sym->kind == SymbolKind::ConstraintBlock) {
            auto& constraints = sym->as<ConstraintBlockSymbol>().getConstraints();
            if (!constraints.bad())
                graph.add(constraints);
        }
    }

    graph.findAllCycles();
}

} // namespace slang::analysis
