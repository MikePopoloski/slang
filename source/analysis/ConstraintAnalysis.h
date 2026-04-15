//------------------------------------------------------------------------------
// ConstraintAnalysis.h
// Analysis of rand variable ordering in constraint blocks
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <ranges>

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Constraints.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/ValuePath.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/diagnostics/AnalysisDiags.h"
#include "slang/util/FlatMap.h"
#include "slang/util/SmallVector.h"

namespace slang::analysis {

using namespace ast;

namespace {

class PathEdgeMap {
public:
    // Outer key: root ValueSymbol* of the "from" path.
    // Outer value: one EdgeList per distinct path rooted at that symbol.
    // Each EdgeList holds the path node for that "from" node plus its outgoing edges.
    using EdgeList = std::pair<ValuePath, SmallVector<ValuePath>>;
    using MapType = flat_hash_map<const ValueSymbol*, SmallVector<EdgeList>>;

    void addEdge(const ValuePath& from, const ValuePath& to) {
        // Ensure the 'to' node has an entry (so DFS can start from it even
        // if it has no outgoing edges of its own).
        insert(to);

        // Add the edge under the 'from' node, creating it if needed.
        insert(from).emplace_back(to);
    }

    const EdgeList& findEdgeList(const ValuePath& node) const {
        if (auto it = map.find(node.rootSymbol()); it != map.end()) {
            for (auto& edgeList : it->second) {
                if (edgeList.first.overlaps(node))
                    return edgeList;
            }
        }
        SLANG_UNREACHABLE;
    }

    auto allEdgeLists() const { return map | std::views::values | std::views::join; }

private:
    MapType map;

    SmallVector<ValuePath>& insert(const ValuePath& node) {
        auto sym = node.rootSymbol();
        SLANG_ASSERT(sym);

        auto& bucket = map[sym];
        for (auto& entry : bucket) {
            if (entry.first.overlaps(node))
                return entry.second;
        }

        return bucket.emplace_back(node, SmallVector<ValuePath>{}).second;
    }
};

class PathNodeSet {
public:
    bool insert(const ValuePath& path) {
        auto& entries = map[path.rootSymbol()];
        if (std::ranges::any_of(entries, [&](auto& p) { return p.overlaps(path); }))
            return false;

        entries.push_back(path);
        return true;
    }

    void erase(const ValuePath& path) {
        auto it = map.find(path.rootSymbol());
        if (it == map.end())
            return;

        auto& vec = it->second;
        for (auto eit = vec.begin(); eit != vec.end(); ++eit) {
            if (eit->overlaps(path)) {
                vec.erase(eit);
                return;
            }
        }
    }

    bool contains(const ValuePath& path) const {
        auto it = map.find(path.rootSymbol());
        if (it == map.end())
            return false;

        return std::ranges::any_of(it->second, [&](auto& p) { return p.overlaps(path); });
    }

    void clear() { map.clear(); }

private:
    flat_hash_map<const ValueSymbol*, SmallVector<ValuePath>> map;
};

// Walks a constraint expression to collect rand variable references, tracking
// whether each appears in a function argument position (which gives it higher
// implicit priority) or a non-argument position.
struct FuncArgVarCollector {
    EvalContext& evalContext;

    // Rand var paths appearing as arguments to user-defined function calls,
    // paired with the source range of the argument expression.
    SmallVector<ValuePath> argPaths;

    // Rand var paths appearing outside of user-defined function call arguments,
    // paired with their source ranges.
    SmallVector<ValuePath> nonArgPaths;

    bool inFuncArg = false;

    explicit FuncArgVarCollector(EvalContext& evalContext) : evalContext(evalContext) {}

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_base_of_v<ValueExpressionBase, T>) {
            if (auto sym = expr.getSymbolReference()) {
                if (sym->getRandMode() != RandMode::None) {
                    if (inFuncArg)
                        argPaths.emplace_back(ValuePath(expr, evalContext));
                    else
                        nonArgPaths.emplace_back(ValuePath(expr, evalContext));
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
        context(context), rootSym(rootSym), evalContext(rootSym) {}

    void add(const Constraint& c) {
        switch (c.kind) {
            case ConstraintKind::List:
                for (auto item : c.as<ConstraintList>().list)
                    add(*item);
                return;
            case ConstraintKind::Expression: {
                FuncArgVarCollector collector(evalContext);
                c.as<ExpressionConstraint>().expr.visit(collector);

                // For each (arg_path, non_arg_path) pair, arg_path must be solved first.
                for (auto& argPath : collector.argPaths) {
                    for (auto& nonArgPath : collector.nonArgPaths) {
                        if (!argPath.overlaps(nonArgPath))
                            funcArgMap.addEdge(argPath, nonArgPath);
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
                    ValuePath solvePath(*solveExpr, evalContext);
                    if (!solvePath.rootSymbol())
                        continue;

                    for (auto afterExpr : sb.after) {
                        ValuePath afterPath(*afterExpr, evalContext);
                        if (!afterPath.rootSymbol() || solvePath.overlaps(afterPath))
                            continue;

                        solveBeforeMap.addEdge(solvePath, afterPath);
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
        findCycles(funcArgMap, diag::ConstraintFuncArgCycle, diag::NoteConstraintFuncArgOrder);
        visited.clear();
        onStack.clear();
        dfsPath.clear();
        findCycles(solveBeforeMap, diag::ConstraintSolveCycle, diag::NoteConstraintSolveBeforeEdge);
    }

private:
    void findCycles(const PathEdgeMap& map, DiagCode cycleDiag, DiagCode edgeDiag) {
        for (auto& edgeList : map.allEdgeLists()) {
            if (visited.insert(edgeList.first)) {
                if (!dfs(edgeList, map, cycleDiag, edgeDiag))
                    return;
            }
        }
    }

    bool dfs(const PathEdgeMap::EdgeList& edgeList, const PathEdgeMap& map, DiagCode cycleDiag,
             DiagCode edgeDiag) {
        auto& [node, edges] = edgeList;
        onStack.insert(node);
        dfsPath.push_back({node, {}});

        for (auto& neighbor : edges) {
            // Record the outgoing edge range for the current node in the path.
            dfsPath.back().second = neighbor.fullExpr->sourceRange;

            if (onStack.contains(neighbor)) {
                reportCycle(neighbor, cycleDiag, edgeDiag);
                return false;
            }

            if (visited.insert(neighbor)) {
                if (!dfs(map.findEdgeList(neighbor), map, cycleDiag, edgeDiag))
                    return false;
            }
        }

        dfsPath.pop_back();
        onStack.erase(node);
        return true;
    }

    void reportCycle(const ValuePath& node, DiagCode cycleDiag, DiagCode edgeDiag) {
        // Extract the portion of the DFS path that forms the cycle.
        SmallVector<std::pair<ValuePath, SourceRange>> cycle;
        bool inCycle = false;
        for (auto& entry : dfsPath) {
            if (entry.first.overlaps(node))
                inCycle = true;
            if (inCycle)
                cycle.push_back(entry);
        }

        auto& diag = context.addDiag(rootSym, cycleDiag, cycle[0].first.fullExpr->sourceRange);
        diag << cycle[0].first.toString(evalContext);

        for (size_t i = 0; i < cycle.size(); i++) {
            auto& nextVar = cycle[(i + 1) % cycle.size()].first;
            diag.addNote(edgeDiag, cycle[i].second)
                << cycle[i].first.toString(evalContext) << nextVar.toString(evalContext);
        }
    }

    PathEdgeMap funcArgMap;
    PathEdgeMap solveBeforeMap;
    PathNodeSet visited;
    PathNodeSet onStack;
    SmallVector<std::pair<ValuePath, SourceRange>> dfsPath;

    AnalysisContext& context;
    const Symbol& rootSym;
    EvalContext evalContext;
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
