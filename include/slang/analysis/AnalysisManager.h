//------------------------------------------------------------------------------
//! @file AnalysisManager.h
//! @brief Central manager for analyzing ASTs
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#if defined(SLANG_USE_THREADS)
#    include <BS_thread_pool.hpp>
#endif
#include <functional>
#include <mutex>
#include <optional>

#include "slang/analysis/AnalysisOptions.h"
#include "slang/analysis/AnalyzedAssertion.h"
#include "slang/analysis/AnalyzedProcedure.h"
#include "slang/analysis/DriverTracker.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/ConcurrentMap.h"
#include "slang/util/SmallMap.h"

namespace slang::ast {

class CheckerInstanceSymbol;
class Compilation;
class Scope;
class SubroutineSymbol;
class Symbol;

} // namespace slang::ast

namespace slang::analysis {

class AnalysisManager;
class DFAResults;

template<typename T, typename TVisitor>
concept HasVisitExprs = requires(const T& t, TVisitor&& visitor) { t.visitExprs(visitor); };

/// Represents an analyzed AST scope.
class SLANG_EXPORT AnalyzedScope {
public:
    /// The scope that was analyzed.
    const ast::Scope& scope;

    /// The procedures in the scope.
    std::vector<AnalyzedProcedure> procedures;

    /// Constructs a new AnalyzedScope object.
    explicit AnalyzedScope(const ast::Scope& scope) : scope(scope) {}
};

/// Holds various bits of state needed to perform analysis.
class SLANG_EXPORT AnalysisContext {
public:
    /// The analysis manager that owns this context.
    not_null<AnalysisManager*> manager;

    /// An allocator used for analysis-specific data structures.
    BumpAllocator alloc;

    /// Diagnostics collected during analysis.
    Diagnostics diagnostics;

    /// Constructs a new AnalysisContext object.
    explicit AnalysisContext(AnalysisManager& manager) : manager(&manager) {}

    /// Issues a new diagnostic.
    Diagnostic& addDiag(const ast::Symbol& symbol, DiagCode code, SourceLocation location);

    /// Issues a new diagnostic.
    Diagnostic& addDiag(const ast::Symbol& symbol, DiagCode code, SourceRange sourceRange);
};

/// The analysis manager coordinates running various analyses on AST symbols.
///
/// Analysis is done downstream from one or more Compilation objects.
/// Once a design has an AST successfully built, analysis passes can
/// be run to check for various issues or extract information.
class SLANG_EXPORT AnalysisManager {
public:
    /// Default constructor for the analysis manager.
    explicit AnalysisManager(AnalysisOptions options = {});

    /// Gets the set of options used to construct the analysis manager.
    const AnalysisOptions& getOptions() const { return options; }

    /// Returns true if the given flag(s) are enabled for this analysis.
    bool hasFlag(bitmask<AnalysisFlags> flags) const { return options.flags.has(flags); }

    /// Adds a listener that will be invoked when a procedure is analyzed.
    ///
    /// @note The listener may be invoked on multiple threads simultaneously.
    void addListener(std::function<void(const AnalyzedProcedure&)> listener) {
        procListeners.push_back(std::move(listener));
    }

    /// Adds a listener that will be invoked when a scope is analyzed.
    ///
    /// @note The listener may be invoked on multiple threads simultaneously.
    /// Also note that child scopes are not guaranteed to be completely analyzed
    /// when the listener is invoked.
    void addListener(std::function<void(const AnalyzedScope&)> listener) {
        scopeListeners.push_back(std::move(listener));
    }

    /// Adds a listener that will be invoked when an assertion is analyzed.
    ///
    /// @note The listener may be invoked on multiple threads simultaneously.
    void addListener(std::function<void(const AnalyzedAssertion&)> listener) {
        assertListeners.push_back(std::move(listener));
    }

    using CustomDFAProvider = std::function<AnalyzedProcedure(AnalysisContext&, const ast::Symbol&,
                                                              const AnalyzedProcedure*)>;

    /// Sets a callback that will be invoked whenever a procedure needs to be analyzed.
    ///
    /// The callback should perform whatever custom data flow analysis is desired and
    /// then return a properly constructed AnalyzedProcedure object.
    void setCustomDFAProvider(CustomDFAProvider provider) {
        SLANG_ASSERT(!customDFAProvider);
        customDFAProvider = provider;
    }

    /// Analyzes the given compilation and returns a representation of the design.
    ///
    /// @note The provided compilation must be finalized and frozen
    ///       before it can be analyzed.
    void analyze(const ast::Compilation& compilation);

    /// Returns all of the known drivers for the given symbol.
    DriverList getDrivers(const ast::ValueSymbol& symbol) const;

    /// Return the driver state tracked per canonical instance.
    std::optional<InstanceDriverState> getInstanceDriverState(
        const ast::InstanceBodySymbol& symbol) const;

    /// Collects and returns all issued analysis diagnostics.
    Diagnostics getDiagnostics();

    /// Returns the results of a previous analysis of a scope, if available.
    const AnalyzedScope* getAnalyzedScope(const ast::Scope& scope) const;

    /// Gets the result of analyzing a subroutine, if available.
    /// Otherwise returns nullptr.
    const AnalyzedProcedure* getAnalyzedSubroutine(const ast::SubroutineSymbol& symbol) const;

    /// Returns all analyzed assertions for the given symbol.
    std::vector<const AnalyzedAssertion*> getAnalyzedAssertions(const ast::Symbol& symbol) const;

    /// Analyzes the non-procedural expressions in the given symbol.
    template<std::derived_from<ast::Symbol> TSymbol>
    void analyzeNonProceduralExprs(const TSymbol& symbol) {
        if constexpr (HasVisitExprs<TSymbol, NonProceduralExprVisitor>) {
            NonProceduralExprVisitor visitor(*this, symbol);
            symbol.visitExprs(visitor);
        }
    }

    /// Analyzes the non-procedural expressions in the given timing control.
    void analyzeNonProceduralExprs(const ast::TimingControl& timing,
                                   const ast::Symbol& containingSymbol);

    /// Analyzes the given non-procedural expression.
    void analyzeNonProceduralExprs(const ast::Expression& expr, const ast::Symbol& containingSymbol,
                                   bool isDisableCondition = false);

private:
    friend struct AnalysisScopeVisitor;
    friend class AnalyzedProcedure;

    // Per-thread state.
    struct WorkerState {
        AnalysisContext context;
        TypedBumpAllocator<AnalyzedScope> scopeAlloc;
        DriverTracker::SymbolDriverMap::allocator_type driverAlloc;

        WorkerState(AnalysisManager& manager) : context(manager), driverAlloc(context.alloc) {}
    };

    const AnalyzedScope& analyzeScopeBlocking(const ast::Scope& scope,
                                              const AnalyzedProcedure* parentProcedure = nullptr);
    void analyzeSymbolAsync(const ast::Symbol& symbol);
    void analyzeScopeAsync(const ast::Scope& scope);
    void analyzeAssertion(const AnalyzedProcedure& procedure,
                          const ast::ConcurrentAssertionStatement& stmt);
    void analyzeAssertion(const AnalyzedProcedure& procedure,
                          const ast::AssertionInstanceExpression& expr);
    void analyzeAssertion(const ast::TimingControl* contextualClock,
                          const ast::Symbol& parentSymbol,
                          const ast::AssertionInstanceExpression& expr);
    void analyzeCheckerInstance(const ast::CheckerInstanceSymbol& symbol,
                                const AnalyzedProcedure& parentProcedure);

    AnalyzedProcedure analyzeProcedure(AnalysisContext& context, const ast::Symbol& symbol,
                                       const AnalyzedProcedure* parentProcedure = nullptr);
    const AnalyzedProcedure& analyzeSubroutine(AnalysisContext& context,
                                               const ast::SubroutineSymbol& symbol,
                                               const AnalyzedProcedure* parentProcedure = nullptr);

    void getFunctionDrivers(const ast::CallExpression& expr, const ast::Symbol& containingSymbol,
                            SmallSet<const ast::SubroutineSymbol*, 2>& visited,
                            std::vector<SymbolDriverListPair>& drivers);

    void getTaskTimingControls(const ast::CallExpression& expr,
                               SmallSet<const ast::SubroutineSymbol*, 2>& visited,
                               std::vector<const ast::Statement*>& controls);

    void handleAssertion(std::unique_ptr<AnalyzedAssertion>&& assertion);
    void wait();
    WorkerState& getState();

    const AnalysisOptions options;
    std::vector<WorkerState> workerStates;

    concurrent_map<const ast::Scope*, std::optional<const AnalyzedScope*>> analyzedScopes;
    concurrent_map<const ast::SubroutineSymbol*, std::unique_ptr<AnalyzedProcedure>>
        analyzedSubroutines;
    concurrent_map<const ast::Symbol*, std::vector<std::unique_ptr<AnalyzedAssertion>>>
        analyzedAssertions;

    DriverTracker driverTracker;

    CustomDFAProvider customDFAProvider;
    std::vector<std::function<void(const AnalyzedProcedure&)>> procListeners;
    std::vector<std::function<void(const AnalyzedScope&)>> scopeListeners;
    std::vector<std::function<void(const AnalyzedAssertion&)>> assertListeners;

    const SourceManager* sourceManager = nullptr;

#if defined(SLANG_USE_THREADS)
    BS::thread_pool<> threadPool;

    // A mutex for shared state; anything protected by it is declared below.
    std::mutex mutex;
    std::exception_ptr pendingException;
#endif

    struct NonProceduralExprVisitor {
        NonProceduralExprVisitor(AnalysisManager& manager, const ast::Symbol& containingSymbol,
                                 bool isDisableCondition = false) :
            manager(manager), containingSymbol(containingSymbol),
            isDisableCondition(isDisableCondition) {}

        template<typename T>
        void visit(const T& expr) {
            if constexpr (std::is_same_v<T, ast::CallExpression>) {
                visitCall(expr);
            }
            else if constexpr (std::is_same_v<T, ast::AssertionInstanceExpression>) {
                manager.analyzeAssertion(getDefaultClocking(), containingSymbol, expr);
            }

            if constexpr (HasVisitExprs<T, NonProceduralExprVisitor>) {
                expr.visitExprs(*this);
            }
        }

    private:
        AnalysisManager& manager;
        const ast::Symbol& containingSymbol;
        SmallSet<const ast::SubroutineSymbol*, 2> visitedSubroutines;
        bool isDisableCondition;

        const ast::TimingControl* getDefaultClocking() const;
        void visitCall(const ast::CallExpression& expr);
    };
};

} // namespace slang::analysis
