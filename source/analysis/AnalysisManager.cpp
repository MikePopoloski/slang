//------------------------------------------------------------------------------
// AnalysisManager.cpp
// Central manager for analyzing ASTs
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AnalysisManager.h"

#include "AnalysisScopeVisitor.h"

#include "slang/analysis/ClockInference.h"
#include "slang/analysis/DataFlowAnalysis.h"
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

void AnalysisManager::analyze(const Compilation& compilation) {
    if (!compilation.isElaborated())
        SLANG_THROW(std::runtime_error("Compilation must be elaborated before analysis"));

    SLANG_ASSERT(compilation.isFrozen());
    if (compilation.hasFatalErrors())
        return;

    if (sourceManager && sourceManager != compilation.getSourceManager()) {
        SLANG_THROW(
            std::runtime_error("AnalysisManager cannot be reused with different source managers"));
    }
    sourceManager = compilation.getSourceManager();

    // Analyze all compilation units first.
    auto& root = compilation.getRootNoFinalize();
    for (auto unit : root.compilationUnits)
        analyzeScopeAsync(*unit);

    for (auto instance : root.topInstances)
        analyzeSymbolAsync(*instance);
    wait();

    // Finalize all drivers that are applied through indirect drivers.
    auto& state = getState();
    driverTracker.propagateIndirectDrivers(state.context, state.driverAlloc);

    // Report on unused definitions.
    if (hasFlag(AnalysisFlags::CheckUnused)) {
        for (auto def : compilation.getUnreferencedDefinitions()) {
            if (!def->name.empty() && def->name != "_"sv && !hasUnusedAttrib(compilation, *def)) {
                state.context.addDiag(*def, diag::UnusedDefinition, def->location)
                    << def->getKindString();
            }
        }
    }
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

std::vector<const AnalyzedAssertion*> AnalysisManager::getAnalyzedAssertions(
    const Symbol& symbol) const {

    std::vector<const AnalyzedAssertion*> results;
    analyzedAssertions.cvisit(&symbol, [&results](auto& item) {
        for (auto& elem : item.second)
            results.push_back(elem.get());
    });
    return results;
}

void AnalysisManager::analyzeAssertion(const AnalyzedProcedure& procedure,
                                       const ConcurrentAssertionStatement& stmt) {
    handleAssertion(std::make_unique<AnalyzedAssertion>(getState().context, procedure, stmt));
}

void AnalysisManager::analyzeAssertion(const AnalyzedProcedure& procedure,
                                       const AssertionInstanceExpression& expr) {
    handleAssertion(std::make_unique<AnalyzedAssertion>(getState().context, procedure, expr));
}

void AnalysisManager::analyzeAssertion(const TimingControl* contextualClock,
                                       const Symbol& parentSymbol,
                                       const AssertionInstanceExpression& expr) {
    handleAssertion(std::make_unique<AnalyzedAssertion>(getState().context, contextualClock,
                                                        parentSymbol, expr));
}

void AnalysisManager::analyzeCheckerInstance(const CheckerInstanceSymbol& inst,
                                             const AnalyzedProcedure& parentProcedure) {
    analyzeScopeBlocking(inst.body, &parentProcedure);
    analyzeNonProceduralExprs(inst);

    auto& state = getState();
    for (auto& conn : inst.getPortConnections()) {
        if (conn.formal.kind == SymbolKind::FormalArgument && conn.actual.index() == 0)
            driverTracker.add(state.context, state.driverAlloc, *std::get<0>(conn.actual), inst);
    }
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
    auto& analysis = analyzeSubroutine(context, subroutine);

    // For each driver in the function, create a new driver that points to the
    // original driver but has the current procedure as the containing symbol.
    auto funcDrivers = analysis.getDrivers();
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
            auto newDriver = ValueDriver::create(context.alloc, driver->kind, *driver->lsp,
                                                 containingSymbol, DriverFlags::None,
                                                 &expr.sourceRange);
            perSymbol.emplace_back(newDriver, bounds);
        }

        drivers.emplace_back(valueSym, std::move(perSymbol));
    }

    // If this function has any calls, we need to recursively add drivers
    // from those calls as well.
    for (auto call : analysis.getCallExpressions())
        getFunctionDrivers(*call, containingSymbol, visited, drivers);
}

void AnalysisManager::getTaskTimingControls(const CallExpression& expr,
                                            SmallSet<const SubroutineSymbol*, 2>& visited,
                                            std::vector<const Statement*>& controls) {
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

    // Add timing controls from the task to our list.
    auto& analysis = analyzeSubroutine(getState().context, subroutine);
    auto taskTimingControls = analysis.getTimingControls();
    controls.insert(controls.end(), taskTimingControls.begin(), taskTimingControls.end());

    // If this task has any calls, we need to recursively add timing controls
    // from those calls as well.
    for (auto call : analysis.getCallExpressions())
        getTaskTimingControls(*call, visited, controls);
}

void AnalysisManager::analyzeNonProceduralExprs(const TimingControl& timing,
                                                const Symbol& containingSymbol) {
    NonProceduralExprVisitor visitor(*this, containingSymbol);
    timing.visit(visitor);
}

void AnalysisManager::analyzeNonProceduralExprs(const Expression& expr,
                                                const Symbol& containingSymbol,
                                                bool isDisableCondition) {
    NonProceduralExprVisitor visitor(*this, containingSymbol, isDisableCondition);
    expr.visit(visitor);
}

DriverList AnalysisManager::getDrivers(const ValueSymbol& symbol) const {
    return driverTracker.getDrivers(symbol);
}

std::optional<InstanceDriverState> AnalysisManager::getInstanceDriverState(
    const InstanceBodySymbol& symbol) const {
    return driverTracker.getInstanceState(symbol);
}

Diagnostics AnalysisManager::getDiagnostics() {
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

const AnalyzedScope& AnalysisManager::analyzeScopeBlocking(
    const Scope& scope, const AnalyzedProcedure* parentProcedure) {

    auto& state = getState();
    auto& result = *state.scopeAlloc.emplace(scope);

    AnalysisScopeVisitor visitor(state, result, parentProcedure);
    for (auto& member : scope.members())
        member.visit(visitor);

    return result;
}

void AnalysisManager::analyzeSymbolAsync(const Symbol& symbol) {
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
                for (auto& listener : scopeListeners)
                    listener(result);
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

AnalyzedProcedure AnalysisManager::analyzeProcedure(AnalysisContext& context, const Symbol& symbol,
                                                    const AnalyzedProcedure* parentProcedure) {
    if (customDFAProvider)
        return customDFAProvider(context, symbol, parentProcedure);

    DefaultDFA dfa(context, symbol, true);
    dfa.run();

    if (dfa.bad)
        return AnalyzedProcedure(symbol, parentProcedure);
    else
        return AnalyzedProcedure(context, symbol, parentProcedure, dfa);
}

const AnalyzedProcedure& AnalysisManager::analyzeSubroutine(
    AnalysisContext& context, const SubroutineSymbol& symbol,
    const AnalyzedProcedure* parentProcedure) {

    if (auto result = getAnalyzedSubroutine(symbol))
        return *result;

    auto proc = std::make_unique<AnalyzedProcedure>(
        analyzeProcedure(context, symbol, parentProcedure));

    const AnalyzedProcedure* result = nullptr;
    auto updater = [&result](auto& item) { result = item.second.get(); };

    if (analyzedSubroutines.try_emplace_and_cvisit(&symbol, std::move(proc), updater, updater)) {
        // If we successfully inserted a new procedure, we need to
        // add it to the driver tracker. If not, someone else already
        // did it for us.
        SLANG_ASSERT(result);

        auto& state = getState();
        driverTracker.add(state.context, state.driverAlloc, *result);

        for (auto& listener : procListeners)
            listener(*result);
    }

    return *result;
}

void AnalysisManager::handleAssertion(std::unique_ptr<AnalyzedAssertion>&& assertion) {
    if (!assertion->bad) {
        for (auto& listener : assertListeners)
            listener(*assertion);

        auto updater = [&](auto& item) { item.second.emplace_back(std::move(assertion)); };
        analyzedAssertions.try_emplace_and_visit(assertion->containingSymbol, updater, updater);
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

const TimingControl* AnalysisManager::NonProceduralExprVisitor::getDefaultClocking() const {
    if (isDisableCondition)
        return nullptr;

    auto scope = containingSymbol.getParentScope();
    SLANG_ASSERT(scope);

    if (auto defClk = scope->getCompilation().getDefaultClocking(*scope))
        return &defClk->as<ClockingBlockSymbol>().getEvent();

    return nullptr;
}

void AnalysisManager::NonProceduralExprVisitor::visitCall(const CallExpression& expr) {
    auto& state = manager.getState();
    if (ClockInference::isSampledValueFuncCall(expr)) {
        // If we don't have a default clocking active in this scope then
        // we should check the call to be sure it has an explicit clock provided.
        if (getDefaultClocking() == nullptr)
            ClockInference::checkSampledValueFuncs(state.context, containingSymbol, expr);
    }

    std::vector<SymbolDriverListPair> drivers;
    manager.getFunctionDrivers(expr, containingSymbol, visitedSubroutines, drivers);
    if (!drivers.empty())
        manager.driverTracker.add(state.context, state.driverAlloc, drivers);
}

} // namespace slang::analysis
