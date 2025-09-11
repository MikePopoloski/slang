//------------------------------------------------------------------------------
// AnalysisManager.cpp
// Central manager for analyzing ASTs
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AnalysisManager.h"

#include "AnalysisScopeVisitor.h"

#include "slang/ast/ASTDiagMap.h"
#include "slang/ast/Compilation.h"

namespace slang::analysis {

using namespace ast;

static const Scope& getAsScope(const Symbol& symbol) {
    switch (symbol.kind) {
        case SymbolKind::Instance: {
            auto& inst = symbol.as<InstanceSymbol>();
            if (auto body = inst.getCanonicalBody())
                return *body;
            return inst.body;
        }
        case SymbolKind::CheckerInstance:
            return symbol.as<CheckerInstanceSymbol>().body;
        default:
            return symbol.as<Scope>();
    }
}

const AnalyzedScope* PendingAnalysis::tryGet() const {
    return analysisManager->getAnalyzedScope(getAsScope(*symbol));
}

Diagnostic& AnalysisContext::addDiag(const Symbol& symbol, DiagCode code, SourceLocation location) {
    return diagnostics.add(symbol, code, location);
}

Diagnostic& AnalysisContext::addDiag(const Symbol& symbol, DiagCode code, SourceRange sourceRange) {
    return diagnostics.add(symbol, code, sourceRange);
}

AnalysisManager::AnalysisManager(AnalysisOptions options) :
#if defined(SLANG_USE_THREADS)
    options(options), threadPool(options.numThreads) {
#else
    options(options) {
#endif

#if defined(SLANG_USE_THREADS)
    workerStates.reserve(threadPool.get_thread_count() + 1);
    for (size_t i = 0; i < threadPool.get_thread_count() + 1; i++)
        workerStates.emplace_back(*this);
#else
    workerStates.emplace_back(*this);
#endif
}

AnalyzedDesign AnalysisManager::analyze(const Compilation& compilation) {
    if (!compilation.isElaborated())
        SLANG_THROW(std::runtime_error("Compilation must be elaborated before analysis"));

    SLANG_ASSERT(compilation.isFrozen());
    if (compilation.hasFatalErrors())
        return {};

    // Analyze all compilation units first.
    auto& root = compilation.getRootNoFinalize();
    for (auto unit : root.compilationUnits)
        analyzeScopeAsync(*unit);
    wait();

    // Go back through and collect all of the units that were analyzed.
    AnalyzedDesign result(compilation);
    for (auto unit : root.compilationUnits) {
        auto scope = getAnalyzedScope(*unit);
        SLANG_ASSERT(scope);
        result.compilationUnits.push_back(scope);
    }

    // Collect all packages into our result object.
    for (auto package : compilation.getPackages()) {
        // Skip the built-in "std" package.
        if (package->name == "std")
            continue;

        auto scope = getAnalyzedScope(*package);
        SLANG_ASSERT(scope);
        result.packages.push_back(scope);
    }

    for (auto instance : root.topInstances)
        result.topInstances.emplace_back(analyzeSymbol(*instance));
    wait();

    // Finalize all drivers that are applied through modport ports.
    auto& state = getState();
    driverTracker.propagateModportDrivers(state.context, state.driverAlloc);

    // Report on unused definitions.
    if (hasFlag(AnalysisFlags::CheckUnused)) {
        for (auto def : compilation.getUnreferencedDefinitions()) {
            if (!def->name.empty() && def->name != "_"sv && !hasUnusedAttrib(compilation, *def)) {
                state.context.addDiag(*def, diag::UnusedDefinition, def->location)
                    << def->getKindString();
            }
        }
    }

    return result;
}

const AnalyzedScope& AnalysisManager::analyzeScopeBlocking(
    const Scope& scope, const AnalyzedProcedure* parentProcedure) {

    auto& state = getState();
    auto& result = *state.scopeAlloc.emplace(scope);

    AnalysisScopeVisitor visitor(state, result, parentProcedure);
    for (auto& member : scope.members())
        member.visit(visitor);

    return result;
}

const AnalyzedScope* AnalysisManager::getAnalyzedScope(const Scope& scope) const {
    const AnalyzedScope* result = nullptr;
    analyzedScopes.cvisit(&scope, [&result](auto& item) {
        if (item.second)
            result = *item.second;
    });
    return result;
}

const AnalyzedProcedure* AnalysisManager::getAnalyzedSubroutine(
    const SubroutineSymbol& symbol) const {

    const AnalyzedProcedure* result = nullptr;
    analyzedSubroutines.cvisit(&symbol, [&result](auto& item) { result = item.second.get(); });
    return result;
}

const AnalyzedProcedure* AnalysisManager::addAnalyzedSubroutine(
    const SubroutineSymbol& symbol, std::unique_ptr<AnalyzedProcedure> procedure) {

    const AnalyzedProcedure* result = nullptr;
    auto updater = [&result](auto& item) { result = item.second.get(); };

    if (analyzedSubroutines.try_emplace_and_cvisit(&symbol, std::move(procedure), updater,
                                                   updater)) {
        // If we successfully inserted a new procedure, we need to
        // add it to the driver tracker. If not, someone else already
        // did it for us.
        SLANG_ASSERT(result);

        auto& state = getState();
        driverTracker.add(state.context, state.driverAlloc, *result);
    }

    return result;
}

void AnalysisManager::noteDriver(const Expression& expr, const Symbol& containingSymbol) {
    auto& state = getState();
    driverTracker.add(state.context, state.driverAlloc, expr, containingSymbol);
}

void AnalysisManager::noteDrivers(std::span<const SymbolDriverListPair> drivers) {
    auto& state = getState();
    driverTracker.add(state.context, state.driverAlloc, drivers);
}

void AnalysisManager::getFunctionDrivers(const CallExpression& expr, const Symbol& containingSymbol,
                                         SmallSet<const SubroutineSymbol*, 2>& visited,
                                         std::vector<SymbolDriverListPair>& drivers) {
    if (expr.isSystemCall() || expr.thisClass() ||
        expr.getSubroutineKind() != SubroutineKind::Function) {
        return;
    }

    auto& subroutine = *std::get<const SubroutineSymbol*>(expr.subroutine);
    if (subroutine.flags.has(MethodFlags::Pure | MethodFlags::InterfaceExtern |
                             MethodFlags::DPIImport | MethodFlags::Randomize |
                             MethodFlags::BuiltIn)) {
        return;
    }

    // The contents of non-static class methods don't get propagated up
    // to the caller.
    auto subroutineParent = subroutine.getParentScope();
    SLANG_ASSERT(subroutineParent);
    if (subroutineParent->asSymbol().kind == SymbolKind::ClassType) {
        if (!subroutine.flags.has(MethodFlags::Static))
            return;
    }

    // If we've already visited this function then we don't need to
    // analyze it again.
    if (!visited.insert(&subroutine).second)
        return;

    // Get analysis for the function.
    auto& context = getState().context;
    auto analysis = getAnalyzedSubroutine(subroutine);
    if (!analysis) {
        auto proc = std::make_unique<AnalyzedProcedure>(context, subroutine);
        analysis = addAnalyzedSubroutine(subroutine, std::move(proc));
    }

    // For each driver in the function, create a new driver that points to the
    // original driver but has the current procedure as the containing symbol.
    auto funcDrivers = analysis->getDrivers();
    drivers.reserve(drivers.size() + funcDrivers.size());

    for (auto& [valueSym, driverList] : funcDrivers) {
        // The user can disable this inlining of drivers for function locals via a flag.
        if (hasFlag(AnalysisFlags::AllowMultiDrivenLocals)) {
            auto scope = valueSym->getParentScope();
            while (scope && scope->asSymbol().kind == SymbolKind::StatementBlock)
                scope = scope->asSymbol().getParentScope();

            if (scope == &subroutine)
                continue;
        }

        DriverList perSymbol;
        for (auto& [driver, bounds] : driverList) {
            auto newDriver = context.alloc.emplace<ValueDriver>(
                driver->kind, *driver->prefixExpression, containingSymbol, DriverFlags::None);
            newDriver->procCallExpression = &expr;

            perSymbol.emplace_back(newDriver, bounds);
        }

        drivers.emplace_back(valueSym, std::move(perSymbol));
    }

    // If this function has any calls, we need to recursively add drivers
    // from those calls as well.
    for (auto call : analysis->getCallExpressions())
        getFunctionDrivers(*call, containingSymbol, visited, drivers);
}

void AnalysisManager::getTaskTimingControls(const CallExpression& expr,
                                            SmallSet<const SubroutineSymbol*, 2>& visited,
                                            std::vector<const ast::Statement*>& controls) {
    if (expr.getSubroutineKind() != SubroutineKind::Task || expr.isSystemCall()) {
        return;
    }

    auto& subroutine = *std::get<const SubroutineSymbol*>(expr.subroutine);
    if (subroutine.flags.has(MethodFlags::Pure | MethodFlags::InterfaceExtern |
                             MethodFlags::DPIImport | MethodFlags::Randomize |
                             MethodFlags::BuiltIn)) {
        return;
    }

    // If we've already visited this task then we don't need to
    // analyze it again.
    if (!visited.insert(&subroutine).second)
        return;

    // Get analysis for the task.
    auto analysis = getAnalyzedSubroutine(subroutine);
    if (!analysis) {
        auto proc = std::make_unique<AnalyzedProcedure>(getState().context, subroutine);
        analysis = addAnalyzedSubroutine(subroutine, std::move(proc));
    }

    // Add timing controls from the task to our list.
    auto taskTimingControls = analysis->getTimingControls();
    controls.insert(controls.end(), taskTimingControls.begin(), taskTimingControls.end());

    // If this task has any calls, we need to recursively add timing controls
    // from those calls as well.
    for (auto call : analysis->getCallExpressions())
        getTaskTimingControls(*call, visited, controls);
}

DriverList AnalysisManager::getDrivers(const ValueSymbol& symbol) const {
    return driverTracker.getDrivers(symbol);
}

std::optional<InstanceDriverState> AnalysisManager::getInstanceDriverState(
    const ast::InstanceBodySymbol& symbol) const {
    return driverTracker.getInstanceState(symbol);
}

Diagnostics AnalysisManager::getDiagnostics(const SourceManager* sourceManager) {
    wait();

    ASTDiagMap diagMap;
    for (auto& state : workerStates) {
        for (auto& diag : state.context.diagnostics) {
            bool _;
            diagMap.add(diag, _);
        }
    }

    return diagMap.coalesce(sourceManager);
}

PendingAnalysis AnalysisManager::analyzeSymbol(const Symbol& symbol) {
    analyzeScopeAsync(getAsScope(symbol));

    // If this is an instance with a canonical body, record that
    // relationship in our map.
    if (symbol.kind == SymbolKind::Instance) {
        auto& inst = symbol.as<InstanceSymbol>();
        if (inst.getCanonicalBody()) {
            auto& state = getState();
            driverTracker.noteNonCanonicalInstance(state.context, state.driverAlloc, inst);
        }
    }

    return PendingAnalysis(*this, symbol);
}

void AnalysisManager::analyzeScopeAsync(const Scope& scope) {
    // Kick off a new analysis task if we haven't already seen
    // this scope before.
    if (analyzedScopes.try_emplace(&scope, std::nullopt)) {
#if defined(SLANG_USE_THREADS)
        threadPool.detach_task([this, &scope] {
            SLANG_TRY {
                auto& result = analyzeScopeBlocking(scope);
                analyzedScopes.visit(&scope, [&result](auto& item) { item.second = &result; });
            }
            SLANG_CATCH(...) {
                std::unique_lock<std::mutex> lock(mutex);
                pendingException = std::current_exception();
            }
        });
#else
        auto& result = analyzeScopeBlocking(scope);
        analyzedScopes.visit(&scope, [&result](auto& item) { item.second = &result; });
#endif
    }
}

AnalysisManager::WorkerState& AnalysisManager::getState() {
#if defined(SLANG_USE_THREADS)
    return workerStates[BS::this_thread::get_index().value_or(workerStates.size() - 1)];
#else
    return workerStates[0];
#endif
}

void AnalysisManager::wait() {
#if defined(SLANG_USE_THREADS)
    threadPool.wait();
    if (pendingException)
        std::rethrow_exception(pendingException);
#endif
}

} // namespace slang::analysis
