//------------------------------------------------------------------------------
//! @file AnalysisManager.h
//! @brief Central manager for analyzing ASTs
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <BS_thread_pool.hpp>
#include <mutex>
#include <optional>

#include "slang/analysis/AnalyzedProcedure.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/ConcurrentMap.h"

namespace slang::ast {

class Compilation;
class Scope;
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
    /// An allocator used for analysis-specific data structures.
    BumpAllocator alloc;

    /// Diagnostics collected during analysis.
    Diagnostics diagnostics;
};

/// The analysis manager coordinates running various analyses on AST symbols.
///
/// Analysis is done downstream from one or more Compilation objects.
/// Once a design has an AST successfully built, analysis passes can
/// be run to check for various issues or extract information.
class SLANG_EXPORT AnalysisManager {
public:
    /// Default constructor for the analysis manager.
    explicit AnalysisManager(uint32_t numThreads = 0);

    /// Analyzes the given compilation and returns a representation of the design.
    ///
    /// @note The provided compilation must be finalized and frozen
    ///       before it can be analyzed.
    AnalyzedDesign analyze(const ast::Compilation& compilation);

    /// Returns the results of a previous analysis of a scope, if available.
    const AnalyzedScope* getAnalyzedScope(const ast::Scope& scope);

    /// Collects and returns all issued analysis diagnostics.
    Diagnostics getDiagnostics();

private:
    friend struct ScopeVisitor;

    PendingAnalysis analyzeSymbol(const ast::Symbol& symbol);
    const AnalyzedScope& analyzeScope(const ast::Scope& scope);
    void analyzeScopeAsync(const ast::Scope& scope);
    void wait();

    struct WorkerState {
        AnalysisContext context;
        TypedBumpAllocator<AnalyzedScope> scopeAlloc;
    };
    WorkerState& state();

    BS::thread_pool<> threadPool;
    std::vector<WorkerState> workerStates;
    concurrent_map<const ast::Scope*, std::optional<const AnalyzedScope*>> analyzedScopes;

    // A mutex for shared state; anything protected by it is declared below.
    std::mutex mutex;
    std::exception_ptr pendingException;
};

} // namespace slang::analysis
