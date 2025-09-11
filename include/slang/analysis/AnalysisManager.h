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
#include <mutex>
#include <optional>

#include "slang/analysis/AnalysisOptions.h"
#include "slang/analysis/AnalyzedProcedure.h"
#include "slang/analysis/DriverTracker.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/ConcurrentMap.h"
#include "slang/util/SmallMap.h"

namespace slang::ast {

class Compilation;
class Scope;
class SubroutineSymbol;
class Symbol;

} // namespace slang::ast

namespace slang::analysis {

class AnalysisManager;
class AnalyzedScope;

/// Represents a pending analysis for a particular AST symbol,
/// such as a module or interface instance, a class type, etc.
class SLANG_EXPORT PendingAnalysis {
public:
    /// The symbol that was analyzed.
    not_null<const ast::Symbol*> symbol;

    /// Constructs a new AnalyzedInstance object.
    PendingAnalysis(AnalysisManager& analysisManager, const ast::Symbol& symbol) :
        symbol(&symbol), analysisManager(&analysisManager) {}

    /// Returns the analyzed body of the symbol if available,
    /// or nullptr if the symbol has not been analyzed yet.
    const AnalyzedScope* tryGet() const;

private:
    not_null<AnalysisManager*> analysisManager;
};

/// Represents an analyzed AST scope.
class SLANG_EXPORT AnalyzedScope {
public:
    /// The scope that was analyzed.
    const ast::Scope& scope;

    /// The analyzed child scopes in the scope. This includes things
    /// like class types and checker instances.
    std::vector<PendingAnalysis> childScopes;

    /// The procedures in the scope.
    std::vector<AnalyzedProcedure> procedures;

    /// Constructs a new AnalyzedScope object.
    explicit AnalyzedScope(const ast::Scope& scope) : scope(scope) {}
};

/// Represents the result of analyzing a full design.
class SLANG_EXPORT AnalyzedDesign {
public:
    /// The compilation that was analyzed.
    const ast::Compilation* compilation = nullptr;

    /// The analyzed compilation units in the design.
    std::vector<const AnalyzedScope*> compilationUnits;

    /// The analyzed packages in the design.
    std::vector<const AnalyzedScope*> packages;

    /// The analyzed top-level instances in the design.
    std::vector<PendingAnalysis> topInstances;

    /// Default constructor.
    AnalyzedDesign() = default;

    /// Constructs a new AnalyzedDesign object.
    explicit AnalyzedDesign(const ast::Compilation& compilation) : compilation(&compilation) {}
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

    /// Analyzes the given compilation and returns a representation of the design.
    ///
    /// @note The provided compilation must be finalized and frozen
    ///       before it can be analyzed.
    AnalyzedDesign analyze(const ast::Compilation& compilation);

    /// Returns all of the known drivers for the given symbol.
    DriverList getDrivers(const ast::ValueSymbol& symbol) const;

    /// Return the driver state tracked per canonical instance.
    std::optional<InstanceDriverState> getInstanceDriverState(
        const ast::InstanceBodySymbol& symbol) const;

    /// Collects and returns all issued analysis diagnostics.
    /// If @a sourceManager is provided it will be used to sort the diagnostics.
    Diagnostics getDiagnostics(const SourceManager* sourceManager);

    /// Analyzes the given scope, in blocking fashion.
    ///
    /// @note The result is not stored in the manager and so
    /// won't be visible via calls to @a getAnalyzedScope.
    const AnalyzedScope& analyzeScopeBlocking(const ast::Scope& scope,
                                              const AnalyzedProcedure* parentProcedure = nullptr);

    /// Returns the results of a previous analysis of a scope, if available.
    const AnalyzedScope* getAnalyzedScope(const ast::Scope& scope) const;

    /// Gets the result of analyzing a subroutine, if available.
    /// Otherwise returns nullptr.
    const AnalyzedProcedure* getAnalyzedSubroutine(const ast::SubroutineSymbol& symbol) const;

    /// Adds a new analyzed subroutine to the manager's cache for later lookup.
    const AnalyzedProcedure* addAnalyzedSubroutine(const ast::SubroutineSymbol& symbol,
                                                   std::unique_ptr<AnalyzedProcedure> procedure);

    /// Notes that the given expression is a driver and should be added to the driver tracker.
    void noteDriver(const ast::Expression& expr, const ast::Symbol& containingSymbol);

    /// Notes the existence of the given symbol value drivers.
    void noteDrivers(std::span<const SymbolDriverListPair> drivers);

    /// Helper method to get the indirect drivers from a call to a function.
    void getFunctionDrivers(const ast::CallExpression& expr, const ast::Symbol& containingSymbol,
                            SmallSet<const ast::SubroutineSymbol*, 2>& visited,
                            std::vector<SymbolDriverListPair>& drivers);

    /// Helper method to get all timing controls from a call to a task.
    void getTaskTimingControls(const ast::CallExpression& expr,
                               SmallSet<const ast::SubroutineSymbol*, 2>& visited,
                               std::vector<const ast::Statement*>& controls);

private:
    friend struct AnalysisScopeVisitor;

    // Per-thread state.
    struct WorkerState {
        AnalysisContext context;
        TypedBumpAllocator<AnalyzedScope> scopeAlloc;
        DriverTracker::SymbolDriverMap::allocator_type driverAlloc;

        WorkerState(AnalysisManager& manager) : context(manager), driverAlloc(context.alloc) {}
    };

    PendingAnalysis analyzeSymbol(const ast::Symbol& symbol);
    void analyzeScopeAsync(const ast::Scope& scope);
    void wait();
    WorkerState& getState();

    const AnalysisOptions options;
    std::vector<WorkerState> workerStates;

    concurrent_map<const ast::Scope*, std::optional<const AnalyzedScope*>> analyzedScopes;
    concurrent_map<const ast::SubroutineSymbol*, std::unique_ptr<AnalyzedProcedure>>
        analyzedSubroutines;

    DriverTracker driverTracker;

#if defined(SLANG_USE_THREADS)
    BS::thread_pool<> threadPool;

    // A mutex for shared state; anything protected by it is declared below.
    std::mutex mutex;
    std::exception_ptr pendingException;
#endif
};

} // namespace slang::analysis
