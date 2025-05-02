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
    options(options), threadPool(options.numThreads) {

    workerStates.reserve(threadPool.get_thread_count() + 1);
    for (size_t i = 0; i < threadPool.get_thread_count() + 1; i++)
        workerStates.emplace_back(*this);
}

AnalyzedDesign AnalysisManager::analyze(const Compilation& compilation) {
    SLANG_ASSERT(compilation.isFinalized());
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

    // Report on unused definitions.
    if (hasFlag(AnalysisFlags::CheckUnused)) {
        auto& context = getState().context;
        for (auto def : compilation.getUnreferencedDefinitions()) {
            if (!def->name.empty() && def->name != "_"sv && !hasUnusedAttrib(compilation, *def)) {
                context.addDiag(*def, diag::UnusedDefinition, def->location)
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

const AnalyzedScope* AnalysisManager::getAnalyzedScope(const Scope& scope) {
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

void AnalysisManager::addAnalyzedSubroutine(const SubroutineSymbol& symbol,
                                            std::unique_ptr<AnalyzedProcedure> procedure) {
    addDriversFor(*procedure);
    analyzedSubroutines.try_emplace(&symbol, std::move(procedure));
}

std::vector<const ValueDriver*> AnalysisManager::getDrivers(const ValueSymbol& symbol) const {
    std::vector<const ValueDriver*> drivers;
    symbolDrivers.cvisit(&symbol, [&drivers](auto& item) {
        for (auto it = item.second.begin(); it != item.second.end(); ++it)
            drivers.push_back(*it);
    });
    return drivers;
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
    return PendingAnalysis(*this, symbol);
}

void AnalysisManager::analyzeScopeAsync(const Scope& scope) {
    // Kick off a new analysis task if we haven't already seen
    // this scope before.
    if (analyzedScopes.try_emplace(&scope, std::nullopt)) {
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
    }
}

AnalysisManager::WorkerState& AnalysisManager::getState() {
    return workerStates[BS::this_thread::get_index().value_or(workerStates.size() - 1)];
}

void AnalysisManager::wait() {
    threadPool.wait();
    if (pendingException)
        std::rethrow_exception(pendingException);
}

void AnalysisManager::addDriversFor(const AnalyzedProcedure& procedure) {
    auto& state = getState();
    for (auto& [valueSym, drivers] : procedure.getDrivers()) {
        auto updateFunc = [&](auto& elem) {
            for (auto& [driver, bounds] : drivers)
                addDriver(state, *elem.first, elem.second, *driver, bounds);
        };
        symbolDrivers.try_emplace_and_visit(valueSym, updateFunc, updateFunc);
    }
}

static std::string getLSPName(const ValueSymbol& symbol, const ValueDriver& driver) {
    auto scope = symbol.getParentScope();
    SLANG_ASSERT(scope);

    FormatBuffer buf;
    EvalContext evalContext(ASTContext(*scope, LookupLocation::after(symbol)));
    stringifyLSP(*driver.prefixExpression, evalContext, buf);

    return buf.str();
}

static bool handleOverlap(AnalysisContext& context, const ValueSymbol& symbol,
                          const ValueDriver& curr, const ValueDriver& driver, bool isNet,
                          bool isUWire, bool isSingleDriverUDNT, const NetType* netType) {
    auto currRange = curr.getSourceRange();
    auto driverRange = driver.getSourceRange();

    // The default handling case for mixed vs multiple assignments is below.
    // First check for more specialized cases here:
    // 1. If this is a non-uwire net for an input or output port
    // 2. If this is a variable for an input port
    const bool isUnidirectionNetPort = isNet && (curr.isUnidirectionalPort() ||
                                                 driver.isUnidirectionalPort());

    if ((isUnidirectionNetPort && !isUWire && !isSingleDriverUDNT) ||
        (!isNet && (curr.isInputPort() || driver.isInputPort()))) {
        auto code = diag::InputPortAssign;
        if (isNet) {
            if (curr.flags.has(AssignFlags::InputPort))
                code = diag::InputPortCoercion;
            else
                code = diag::OutputPortCoercion;
        }

        // This is a little messy; basically we want to report the correct
        // range for the port vs the assignment. We only want to do this
        // for input ports though, as output ports show up at the instantiation
        // site and we'd rather that be considered the "port declaration".
        auto portRange = currRange;
        auto assignRange = driverRange;
        if (driver.isInputPort() || curr.flags.has(AssignFlags::OutputPort))
            std::swap(portRange, assignRange);

        auto& diag = context.addDiag(symbol, code, assignRange);
        diag << symbol.name;

        auto note = code == diag::OutputPortCoercion ? diag::NoteDrivenHere
                                                     : diag::NoteDeclarationHere;
        diag.addNote(note, portRange);

        // For variable ports this is an error, for nets it's a warning.
        return isNet;
    }

    if (curr.isClockVar() || driver.isClockVar()) {
        // Both drivers being clockvars is allowed.
        if (curr.isClockVar() && driver.isClockVar())
            return true;

        // Procedural drivers are allowed to clockvars.
        if (curr.kind == DriverKind::Procedural || driver.kind == DriverKind::Procedural)
            return true;

        // Otherwise we have an error.
        if (driver.isClockVar())
            std::swap(driverRange, currRange);

        auto& diag = context.addDiag(symbol, diag::ClockVarTargetAssign, driverRange);
        diag << symbol.name;
        diag.addNote(diag::NoteReferencedHere, currRange);
        return false;
    }

    if (curr.isLocalVarFormalArg() && driver.isLocalVarFormalArg()) {
        auto& diag = context.addDiag(symbol, diag::LocalFormalVarMultiAssign, driverRange);
        diag << symbol.name;
        diag.addNote(diag::NoteAssignedHere, currRange);
        return false;
    }

    auto addAssignedHereNote = [&](Diagnostic& d) {
        // If the two locations are the same, the symbol is driven by
        // the same source location but two different parts of the hierarchy.
        // In those cases we want a different note about what's going on.
        if (currRange.start() != driverRange.start()) {
            d.addNote(diag::NoteAssignedHere, currRange);
        }
        else {
            auto& note = d.addNote(diag::NoteFromHere2, SourceLocation::NoLocation);
            note << driver.containingSymbol->getHierarchicalPath();
            note << curr.containingSymbol->getHierarchicalPath();
        }
    };

    if (curr.kind == DriverKind::Procedural && driver.kind == DriverKind::Procedural) {
        // Multiple procedural drivers where one of them is an
        // always_comb / always_ff block.
        ProceduralBlockKind procKind;
        const ValueDriver* sourceForName = &driver;
        if (driver.isInSingleDriverProcedure()) {
            procKind = static_cast<ProceduralBlockKind>(driver.source);
        }
        else {
            procKind = static_cast<ProceduralBlockKind>(curr.source);
            std::swap(driverRange, currRange);
            sourceForName = &curr;
        }

        auto& diag = context.addDiag(symbol, diag::MultipleAlwaysAssigns, driverRange);
        diag << getLSPName(symbol, *sourceForName) << SemanticFacts::getProcedureKindStr(procKind);
        addAssignedHereNote(diag);

        if (driver.procCallExpression || curr.procCallExpression) {
            SourceRange extraRange = driver.procCallExpression
                                         ? driver.prefixExpression->sourceRange
                                         : curr.prefixExpression->sourceRange;

            diag.addNote(diag::NoteOriginalAssign, extraRange);
        }

        return false;
    }

    DiagCode code;
    if (isUWire)
        code = diag::MultipleUWireDrivers;
    else if (isSingleDriverUDNT)
        code = diag::MultipleUDNTDrivers;
    else if (driver.kind == DriverKind::Continuous && curr.kind == DriverKind::Continuous)
        code = diag::MultipleContAssigns;
    else
        code = diag::MixedVarAssigns;

    auto& diag = context.addDiag(symbol, code, driverRange);
    diag << getLSPName(symbol, driver);
    if (isSingleDriverUDNT) {
        SLANG_ASSERT(netType);
        diag << netType->name;
    }

    addAssignedHereNote(diag);
    return false;
}

void AnalysisManager::addDriver(WorkerState& state, const ValueSymbol& symbol,
                                SymbolDriverMap& driverMap, const ValueDriver& driver,
                                DriverBitRange bounds) {
    auto& context = state.context;
    auto scope = symbol.getParentScope();
    SLANG_ASSERT(scope);

    // If this driver is made via an interface port connection we want to
    // note that fact as it represents a side effect for the instance that
    // is not captured in the port connections.
    // bool isIfacePortDriver = false;
    // if (!driver.isFromSideEffect) {
    //     visitPrefixExpressions(*driver.prefixExpression, /* includeRoot */ true,
    //                            [&](const Expression& expr) {
    //                                if (expr.kind == ExpressionKind::HierarchicalValue) {
    //                                    auto& hve = expr.as<HierarchicalValueExpression>();
    //                                    if (hve.ref.isViaIfacePort()) {
    //                                        isIfacePortDriver = true;
    //                                        comp.noteInterfacePortDriver(hve.ref, driver);
    //                                    }
    //                                }
    //                            });
    // }

    if (driverMap.empty()) {
        // The first time we add a driver, check whether there is also an
        // initializer expression that should count as a driver as well.
        auto addInitializer = [&](DriverKind driverKind) {
            auto& valExpr = *context.alloc.emplace<NamedValueExpression>(
                symbol, SourceRange{symbol.location, symbol.location + symbol.name.length()});

            DriverBitRange initBounds{0, symbol.getType().getSelectableWidth() - 1};
            auto initDriver = context.alloc.emplace<ValueDriver>(driverKind, valExpr,
                                                                 scope->asSymbol(),
                                                                 AssignFlags::None);

            driverMap.insert(initBounds, initDriver, state.driverAlloc);
        };

        switch (symbol.kind) {
            case SymbolKind::Net:
                if (symbol.getInitializer())
                    addInitializer(DriverKind::Continuous);
                break;
            case SymbolKind::Variable:
            case SymbolKind::ClassProperty:
            case SymbolKind::Field:
                if (symbol.getInitializer())
                    addInitializer(DriverKind::Procedural);
                break;
            default:
                break;
        }

        if (driverMap.empty()) {
            driverMap.insert(bounds, &driver, state.driverAlloc);
            return;
        }
    }

    // We need to check for overlap in the following cases:
    // - static variables (automatic variables can't ever be driven continuously)
    // - uwire nets
    // - user-defined nets with no resolution function
    const bool isNet = symbol.kind == SymbolKind::Net;
    bool isUWire = false;
    bool isSingleDriverUDNT = false;
    const NetType* netType = nullptr;

    if (isNet) {
        netType = &symbol.as<NetSymbol>().netType;
        isUWire = netType->netKind == NetType::UWire;
        isSingleDriverUDNT = netType->netKind == NetType::UserDefined &&
                             netType->getResolutionFunction() == nullptr;
    }

    const bool checkOverlap = (VariableSymbol::isKind(symbol.kind) &&
                               symbol.as<VariableSymbol>().lifetime == VariableLifetime::Static) ||
                              isUWire || isSingleDriverUDNT ||
                              symbol.kind == SymbolKind::LocalAssertionVar;

    // TODO: try to clean these conditions up a bit more
    auto end = driverMap.end();
    for (auto it = driverMap.find(bounds); it != end; ++it) {
        // Check whether this pair of drivers overlapping constitutes a problem.
        // The conditions for reporting a problem are:
        // - If this is for a mix of input/output and inout ports, always report.
        // - Don't report for "Other" drivers (procedural force / release, etc)
        // - Otherwise, if is this a static var or uwire net:
        //      - Report if a mix of continuous and procedural assignments
        //      - Don't report if both drivers are sliced ports from an array
        //        of instances. We already sliced these up correctly when the
        //        connections were made and the overlap logic here won't work correctly.
        //      - Report if multiple continuous assignments
        //      - If both procedural, report if there aren multiple
        //        always_comb / always_ff procedures.
        //          - If the allowDupInitialDrivers option is set, allow an initial
        //            block to overlap even if the other block is an always_comb/ff.
        // - Assertion local variable formal arguments can't drive more than
        //   one output to the same local variable.
        bool isProblem = false;
        auto curr = *it;

        if (curr->isUnidirectionalPort() != driver.isUnidirectionalPort()) {
            isProblem = true;
        }
        else if (checkOverlap && driver.kind != DriverKind::Other &&
                 curr->kind != DriverKind::Other) {
            if (driver.kind == DriverKind::Continuous || curr->kind == DriverKind::Continuous) {
                if (!driver.flags.has(AssignFlags::SlicedPort) ||
                    !curr->flags.has(AssignFlags::SlicedPort)) {
                    isProblem = true;
                }
            }
            else if (curr->containingSymbol != driver.containingSymbol && curr->isInProcedure() &&
                     driver.isInProcedure() &&
                     (curr->isInSingleDriverProcedure() || driver.isInSingleDriverProcedure()) &&
                     (!hasFlag(AnalysisFlags::AllowDupInitialDrivers) ||
                      (curr->source != DriverSource::Initial &&
                       driver.source != DriverSource::Initial))) {
                isProblem = true;
            }
            else if (curr->isLocalVarFormalArg() && driver.isLocalVarFormalArg()) {
                isProblem = true;
            }
        }

        if (isProblem) {
            if (!handleOverlap(context, symbol, *curr, driver, isNet, isUWire, isSingleDriverUDNT,
                               netType)) {
                break;
            }
        }
    }

    driverMap.insert(bounds, &driver, state.driverAlloc);
}

} // namespace slang::analysis
