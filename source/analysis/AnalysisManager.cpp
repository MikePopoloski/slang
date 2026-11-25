//------------------------------------------------------------------------------
// AnalysisManager.cpp
// Central manager for analyzing ASTs
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AnalysisManager.h"

#include "AnalysisScopeVisitor.h"
#include "ConstraintAnalysis.h"
#include <fmt/format.h>

#include "slang/analysis/ClockInference.h"
#include "slang/analysis/DataFlowAnalysis.h"
#include "slang/ast/ASTDiagMap.h"
#include "slang/ast/Compilation.h"
#include "slang/text/SourceManager.h"

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

Diagnostic& AnalysisContext::addDiag(const Symbol& symbol, DiagCode code) {
    if (manager->sourceManager->isMacroLoc(symbol.location)) {
        return diagnostics.add(symbol, code, symbol.location);
    }
    else {
        return diagnostics.add(
            symbol, code, SourceRange{symbol.location, symbol.location + symbol.name.length()});
    }
}

bool AnalysisContext::isFromMacroBody(SourceLocation location) const {
    auto sm = manager->sourceManager;
    return sm && sm->isMacroLoc(location) && !sm->isMacroArgLoc(location);
}

AnalysisManager::AnalysisManager(AnalysisOptions options, std::shared_ptr<ThreadPool> threadPool) :
    options(options), threadPool(std::move(threadPool)) {

    if (this->threadPool) {
        const size_t count = this->threadPool->get_thread_count() + 1;
        workerStates.reserve(count);
        for (size_t i = 0; i < count; i++)
            workerStates.emplace_back(*this);
    }
    else {
        workerStates.emplace_back(*this);
    }
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

    if (hasFlag(AnalysisFlags::CheckInstanceDrivers))
        checkInstanceDrivers();

    // Report on unused definitions.
    if (hasFlag(AnalysisFlags::CheckUnused)) {
        for (auto def : compilation.getUnreferencedDefinitions()) {
            if (!def->name.empty() && def->name != "_"sv && !hasUnusedAttrib(compilation, *def)) {
                state.context.addDiag(*def, diag::UnusedDefinition) << def->getKindString();
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
        if (conn.formal.kind == SymbolKind::FormalArgument && conn.actual.index() == 0) {
            if (auto expr = std::get<0>(conn.actual))
                driverTracker.add(state.context, state.driverAlloc, *expr, inst);
        }
    }
}

void AnalysisManager::getFunctionValUses(const CallExpression& expr, const Symbol& containingSymbol,
                                         function_ref<bool(const SubroutineSymbol&)> visitPredicate,
                                         SmallVectorBase<const ValueDriver*>& drivers,
                                         SmallVectorBase<ReadRange>* reads) {
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
    if (!visitPredicate(subroutine))
        return;

    // Get analysis for the function.
    auto& context = getState().context;
    auto& analysis = analyzeSubroutine(context, subroutine);

    // For each driver in the function, create a new driver that points to the
    // original driver but has the current procedure as the containing symbol.
    auto funcDrivers = analysis.getDrivers();
    drivers.reserve(drivers.size() + funcDrivers.size());

    auto isLocal = [&](const Symbol& symbol) {
        auto scope = symbol.getParentScope();
        while (scope && scope->asSymbol().kind == SymbolKind::StatementBlock)
            scope = scope->asSymbol().getParentScope();

        return scope == &subroutine;
    };

    for (auto driver : funcDrivers) {
        // The user can disable this inlining of drivers for function locals via a flag.
        if (hasFlag(AnalysisFlags::AllowMultiDrivenLocals) && isLocal(driver->getSymbol()))
            continue;

        auto newDriver = ValueDriver::create(context.alloc, driver->kind, driver->path,
                                             containingSymbol, DriverFlags::None,
                                             &expr.sourceRange);

        drivers.push_back(newDriver);
    }

    // Optionally collect reads from the function body.
    // Note: this excludes locally declared variables.
    if (reads) {
        for (auto& read : analysis.getReadSet()) {
            if (!isLocal(*read.symbol))
                reads->push_back(read);
        }
    }

    // Recurse into functions called by this function.
    for (auto call : analysis.getCallExpressions())
        getFunctionValUses(*call, containingSymbol, visitPredicate, drivers, reads);
}

void AnalysisManager::getTaskTimingControls(const CallExpression& expr,
                                            SmallSet<const SubroutineSymbol*, 2>& visited,
                                            SmallVectorBase<const Statement*>& controls) {
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

std::vector<const ValueDriver*> AnalysisManager::getDrivers(const ValueSymbol& symbol) const {
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

AnalysisManager::Stats AnalysisManager::getStats() const {
    Stats stats;
    for (auto& state : workerStates) {
        stats.memoryUsage += state.context.alloc.getTotalBytesAllocated();
        stats.memoryUsage += state.scopeAlloc.getTotalBytesAllocated();
    }

    auto mapBytes = [](const auto& m) {
        return m.size() * sizeof(typename std::remove_reference_t<decltype(m)>::value_type);
    };
    stats.memoryUsage += mapBytes(analyzedScopes);
    stats.memoryUsage += mapBytes(analyzedSubroutines);
    stats.memoryUsage += mapBytes(analyzedAssertions);
    stats.memoryUsage += mapBytes(visitedNonProcCalls);

    stats.numScopes = analyzedScopes.size();
    stats.numProcedures = analyzedSubroutines.size();

    analyzedAssertions.visit_all([&](const auto& e) {
        stats.numAssertions += e.second.size();
        stats.memoryUsage += e.second.capacity() * sizeof(AnalyzedAssertion);
    });

    analyzedSubroutines.visit_all(
        [&](auto& item) { stats.memoryUsage += item.second->getMemoryUsage(); });

    analyzedScopes.visit_all([&](auto& item) {
        if (item.second) {
            auto& scope = *item.second.value();
            stats.numProcedures += scope.procedures.size();
            for (auto& proc : scope.procedures)
                stats.memoryUsage += proc.getMemoryUsage();
        }
    });

    return stats;
}

const AnalyzedScope& AnalysisManager::analyzeScopeBlocking(
    const Scope& scope, const AnalyzedProcedure* parentProcedure) {

    auto& state = getState();
    auto& result = *state.scopeAlloc.emplace(scope);

    AnalysisScopeVisitor visitor(state, result, parentProcedure);
    for (auto& member : scope.members())
        member.visit(visitor);

    // Check for constraint ordering cycles (func-arg implicit ordering and
    // explicit solve...before directives, LRM 18.5.11).
    if (visitor.hasConstraints)
        analyzeConstraints(state.context, scope);

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
        if (threadPool) {
            threadPool->detach_task([this, &scope] {
                SLANG_TRY {
                    auto& result = analyzeScopeBlocking(scope);
                    addScopeResult(scope, result);
                }
                SLANG_CATCH(...) {
                    std::unique_lock<std::mutex> lock(mutex);
                    pendingException = std::current_exception();
                }
            });
        }
        else {
            auto& result = analyzeScopeBlocking(scope);
            addScopeResult(scope, result);
        }
    }
}

void AnalysisManager::addScopeResult(const Scope& scope, const AnalyzedScope& result) {
    analyzedScopes.visit(&scope, [&result](auto& item) { item.second = &result; });
    for (auto& listener : scopeListeners)
        listener(result);
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

using BitRange = std::pair<uint64_t, uint64_t>;

// Formats a select of the inclusive index range [a, b] (in either order),
// written in the same direction as the declared range.
static std::string formatSelect(std::string_view prefix, int32_t a, int32_t b, bool descending) {
    if (a == b)
        return fmt::format("{}[{}]", prefix, a);

    auto [min, max] = std::minmax(a, b);
    if (descending)
        return fmt::format("{}[{}:{}]", prefix, max, min);
    return fmt::format("{}[{}:{}]", prefix, min, max);
}

// The maximum number of undriven paths to list in a single diagnostic.
static constexpr size_t MaxUndrivenPaths = 8;

// Produces human-readable path strings describing the given bit ranges within
// the given type, appending them to the results list. The ranges are relative to
// the start of the type, must be sorted, and must not overlap or be adjacent.
// Results are ordered by struct field declaration order and by ascending array index.
//
// No more than @a limit results will be produced; no work is done to produce
// strings beyond that point. Returns true if all of the ranges were described,
// or false if the description was truncated due to the limit.
static bool describeBits(const Type& type, std::span<const BitRange> ranges,
                         const std::string& prefix, SmallVectorBase<std::string>& results,
                         size_t limit) {
    SLANG_ASSERT(!ranges.empty());
    if (results.size() >= limit)
        return false;

    auto& ct = type.getCanonicalType();
    const uint64_t width = ct.getSelectableWidth();
    if (ranges.size() == 1 && ranges[0].first == 0 && ranges[0].second >= width - 1) {
        results.push_back(prefix);
        return true;
    }

    if (ct.isStruct()) {
        SmallVector<BitRange> sub;
        for (auto& field : ct.as<Scope>().membersOfType<FieldSymbol>()) {
            auto& fieldType = field.getType();
            const uint64_t fieldLo = field.bitOffset;
            const uint64_t fieldWidth = fieldType.getSelectableWidth();
            SLANG_ASSERT(fieldWidth > 0);
            const uint64_t fieldHi = fieldLo + fieldWidth - 1;

            sub.clear();
            for (auto [lo, hi] : ranges) {
                if (hi >= fieldLo && lo <= fieldHi)
                    sub.emplace_back(std::max(lo, fieldLo) - fieldLo,
                                     std::min(hi, fieldHi) - fieldLo);
            }

            if (sub.empty())
                continue;

            if (results.size() >= limit ||
                !describeBits(fieldType, sub, fmt::format("{}.{}", prefix, field.name), results,
                              limit)) {
                return false;
            }
        }
        return true;
    }

    if (ct.kind == SymbolKind::PackedArrayType ||
        ct.kind == SymbolKind::FixedSizeUnpackedArrayType) {
        auto& elemType = *ct.getArrayElementType();
        const uint64_t elemWidth = elemType.getSelectableWidth();
        SLANG_ASSERT(elemWidth > 0);
        const auto range = ct.getFixedRange();

        // Packed arrays store their elements starting from the right bound;
        // unpacked arrays start from the left bound. Work out whether the
        // declared index increases along with the storage offset.
        const bool fromLower = range.isDescending() == ct.isPackedArray();
        auto toIndex = [&](uint64_t elem) {
            auto k = int32_t(elem);
            return fromLower ? range.lower() + k : range.upper() - k;
        };

        // Break the ranges into runs of fully covered elements
        // and individual partially covered elements. Since the ranges
        // are sorted and never adjacent, no two full runs will be adjacent.
        struct Piece {
            uint64_t first;
            uint64_t last;
            SmallVector<BitRange, 2> partial; // empty if the elements are fully covered
        };
        SmallVector<Piece> pieces;

        auto addPartial = [&](uint64_t elem, uint64_t lo, uint64_t hi) {
            if (!pieces.empty() && !pieces.back().partial.empty() && pieces.back().first == elem)
                pieces.back().partial.emplace_back(lo, hi);
            else
                pieces.push_back({elem, elem, {{lo, hi}}});
        };

        for (auto [lo, hi] : ranges) {
            uint64_t first = lo / elemWidth;
            uint64_t last = hi / elemWidth;
            const uint64_t loOffset = lo % elemWidth;
            const uint64_t hiOffset = hi % elemWidth;

            if (first == last) {
                if (loOffset == 0 && hiOffset == elemWidth - 1)
                    pieces.push_back({first, first, {}});
                else
                    addPartial(first, loOffset, hiOffset);
                continue;
            }

            if (loOffset != 0)
                addPartial(first++, loOffset, elemWidth - 1);

            const bool lastPartial = hiOffset != elemWidth - 1;
            const uint64_t lastFull = lastPartial ? last - 1 : last;
            if (first <= lastFull)
                pieces.push_back({first, lastFull, {}});

            if (lastPartial)
                addPartial(last, 0, hiOffset);
        }

        if (!fromLower)
            std::ranges::reverse(pieces);

        for (auto& piece : pieces) {
            if (results.size() >= limit)
                return false;

            if (piece.partial.empty()) {
                results.push_back(formatSelect(prefix, toIndex(piece.first), toIndex(piece.last),
                                               range.isDescending()));
            }
            else if (!describeBits(elemType, piece.partial,
                                   fmt::format("{}[{}]", prefix, toIndex(piece.first)), results,
                                   limit)) {
                return false;
            }
        }
        return true;
    }

    if (ct.isIntegral()) {
        // Some other integral type, like a predefined integer, enum, or
        // packed union; just describe the bits as range selects.
        const auto range = ct.as<IntegralType>().getBitVectorRange();
        auto toIndex = [&](uint64_t bit) {
            auto k = int32_t(bit);
            return range.isDescending() ? range.lower() + k : range.upper() - k;
        };

        // For descending ranges the index increases along with the bit offset;
        // otherwise walk the ranges backward to produce ascending indices.
        for (size_t i = 0; i < ranges.size(); i++) {
            if (results.size() >= limit)
                return false;

            auto [lo, hi] = ranges[range.isDescending() ? i : ranges.size() - 1 - i];
            results.push_back(formatSelect(prefix, toIndex(lo), toIndex(hi), range.isDescending()));
        }
        return true;
    }

    // Otherwise we can't break this down any further.
    results.push_back(prefix);
    return true;
}

void AnalysisManager::checkInstanceDrivers() {
    flat_hash_set<const ValueSymbol*> unknownPortConns;
    for (auto& ws : workerStates)
        unknownPortConns.insert(ws.unknownPortConns.begin(), ws.unknownPortConns.end());

    auto& state = getState();
    for (auto& ws : workerStates) {
        for (auto port : ws.outputPorts) {
            // If something else that we can't see might be driving this
            // symbol then we can't say anything about it.
            auto& symbol = port->internalSymbol->as<ValueSymbol>();
            if (unknownPortConns.contains(&symbol))
                continue;

            auto& type = symbol.getType();
            const uint64_t width = type.getSelectableWidth();

            SmallVector<BitRange> bounds;
            for (auto driver : driverTracker.getDrivers(symbol))
                bounds.push_back(driver->getBounds());

            if (bounds.empty()) {
                state.context.addDiag(*port, diag::UndrivenPortInstance, port->location)
                    << port->name;
                continue;
            }

            // Find any gaps in coverage of the port's bits.
            std::ranges::sort(bounds);
            SmallVector<BitRange> gaps;
            uint64_t next = 0;
            for (auto [lo, hi] : bounds) {
                if (lo > next)
                    gaps.emplace_back(next, lo - 1);
                next = std::max(next, hi + 1);
            }

            if (next < width)
                gaps.emplace_back(next, width - 1);

            if (!gaps.empty()) {
                SmallVector<std::string> undriven;
                const bool complete = describeBits(type, gaps, std::string(port->name), undriven,
                                                   MaxUndrivenPaths);

                std::string str;
                for (auto& u : undriven) {
                    if (!str.empty())
                        str += ", ";
                    str += u;
                }

                if (!complete)
                    str += ", ...";

                auto& diag = state.context.addDiag(*port, diag::PartiallyUndrivenPort,
                                                   port->location);
                diag << port->name << str;
            }
        }
    }
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
    if (threadPool)
        return workerStates[BS::this_thread::get_index().value_or(workerStates.size() - 1)];
#endif
    return workerStates[0];
}

void AnalysisManager::wait() {
    if (threadPool) {
        threadPool->wait();
        if (pendingException)
            std::rethrow_exception(pendingException);
    }
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

    SmallVector<const ValueDriver*, 2> drivers;
    manager.getFunctionValUses(
        expr, containingSymbol,
        [&](const SubroutineSymbol& sub) { return manager.visitedNonProcCalls.insert(&sub); },
        drivers, nullptr);

    if (!drivers.empty())
        manager.driverTracker.add(state.context, state.driverAlloc, drivers);
}

void AnalysisManager::NonProceduralExprVisitor::visitBinary(const BinaryExpression& expr) {
    TautologicalCompare::check(manager.getState().context, containingSymbol, expr);
}

} // namespace slang::analysis
