//------------------------------------------------------------------------------
// DriverTracker.cpp
// Centralized tracking of assigned / driven symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/DriverTracker.h"

#include "slang/analysis/AnalysisManager.h"
#include "slang/analysis/AnalyzedProcedure.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/LSPUtilities.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/diagnostics/AnalysisDiags.h"

namespace slang::analysis {

using namespace ast;

void DriverTracker::add(AnalysisContext& context, DriverAlloc& driverAlloc,
                        const AnalyzedProcedure& procedure) {
    add(context, driverAlloc, procedure.getDrivers());
}

void DriverTracker::add(AnalysisContext& context, DriverAlloc& driverAlloc,
                        const PortConnection& connection, const Symbol& containingSymbol) {
    auto& port = connection.port;
    auto expr = connection.getExpression();
    if (!expr || expr->bad() || port.kind == SymbolKind::InterfacePort)
        return;

    ArgumentDirection direction;
    if (port.kind == SymbolKind::Port) {
        direction = port.as<PortSymbol>().direction;
        checkNetCollapsing(context, connection);
    }
    else {
        direction = port.as<MultiPortSymbol>().direction;
    }

    // Input and ref ports are not drivers.
    if (direction == ArgumentDirection::In || direction == ArgumentDirection::Ref)
        return;

    bitmask<DriverFlags> flags;
    if (direction == ArgumentDirection::Out)
        flags = DriverFlags::OutputPort;

    if (expr->kind == ExpressionKind::Assignment)
        expr = &expr->as<AssignmentExpression>().left();

    addDrivers(context, driverAlloc, *expr, DriverKind::Continuous, flags, containingSymbol);
}

void DriverTracker::add(AnalysisContext& context, DriverAlloc& driverAlloc,
                        const PortSymbol& symbol) {
    // This method adds a driver *from* the port to the *internal*
    // symbol (or expression) that it connects to.
    auto dir = symbol.direction;
    if (dir != ArgumentDirection::In && dir != ArgumentDirection::InOut)
        return;

    auto flags = dir == ArgumentDirection::In ? DriverFlags::InputPort : DriverFlags::None;
    auto scope = symbol.getParentScope();
    SLANG_ASSERT(scope);

    if (auto expr = symbol.getInternalExpr()) {
        addDrivers(context, driverAlloc, *expr, DriverKind::Continuous, flags, scope->asSymbol());
    }
    else if (auto is = symbol.internalSymbol) {
        auto nve = context.alloc.emplace<NamedValueExpression>(
            is->as<ValueSymbol>(), SourceRange{is->location, is->location + is->name.length()});
        addDrivers(context, driverAlloc, *nve, DriverKind::Continuous, flags, scope->asSymbol());
    }
}

void DriverTracker::add(AnalysisContext& context, DriverAlloc& driverAlloc,
                        const ClockVarSymbol& symbol) {
    // Input clock vars don't have drivers.
    if (symbol.direction == ArgumentDirection::In)
        return;

    auto scope = symbol.getParentScope();
    SLANG_ASSERT(scope);

    if (auto expr = symbol.getInitializer()) {
        addDrivers(context, driverAlloc, *expr, DriverKind::Continuous, DriverFlags::ClockVar,
                   scope->asSymbol());
    }
}

void DriverTracker::add(AnalysisContext& context, DriverAlloc& driverAlloc, const Expression& expr,
                        const Symbol& containingSymbol) {
    addDrivers(context, driverAlloc, expr, DriverKind::Continuous, DriverFlags::None,
               containingSymbol);
}

void DriverTracker::add(AnalysisContext& context, DriverAlloc& driverAlloc,
                        std::span<const SymbolDriverListPair> symbolDriverList) {
    SmallVector<HierPortDriver> hierPortDrivers;
    for (auto& [valueSym, drivers] : symbolDriverList) {
        auto updateFunc = [&](auto& elem) {
            for (auto& [driver, bounds] : drivers) {
                addDriver(context, driverAlloc, *elem.first, elem.second, *driver, bounds,
                          hierPortDrivers);
            }
        };
        symbolDrivers.try_emplace_and_visit(valueSym, updateFunc, updateFunc);
    }

    for (auto& hpd : hierPortDrivers)
        noteHierPortDriver(context, driverAlloc, hpd);
}

void DriverTracker::noteNonCanonicalInstance(AnalysisContext& context, DriverAlloc& driverAlloc,
                                             const InstanceSymbol& instance) {
    auto canonical = instance.getCanonicalBody();
    SLANG_ASSERT(canonical);

    std::vector<HierPortDriver> hierPortDrivers;
    auto updater = [&](auto& item) {
        auto& state = item.second;
        state.nonCanonicalInstances.push_back(&instance);

        // Copy these out so we can act on them outside of the concurrent visitor.
        hierPortDrivers = state.hierPortDrivers;
    };
    instanceMap.try_emplace_and_visit(canonical, updater, updater);

    for (auto& hierPortDriver : hierPortDrivers)
        applyInstanceSideEffect(context, driverAlloc, hierPortDriver, instance);
}

void DriverTracker::propagateIndirectDrivers(AnalysisContext& context, DriverAlloc& driverAlloc) {
    while (true) {
        concurrent_map<const ValueSymbol*, DriverList> localCopy;
        std::swap(indirectDrivers, localCopy);
        if (localCopy.empty())
            break;

        localCopy.cvisit_all([&](auto& item) {
            SmallVector<HierPortDriver> hierPortDrivers;
            for (auto& [original, _] : item.second) {
                EvalContext evalCtx(*original->containingSymbol);
                LSPUtilities::expandIndirectLSPs(
                    context.alloc, *original->lsp, evalCtx,
                    [&](const ValueSymbol& symbol, const Expression& lsp, bool isLValue) {
                        // If this is not an lvalue, we don't care about it.
                        if (!isLValue)
                            return;

                        // If the LSP maps to the same symbol as the original driver,
                        // skip it to avoid infinite recursion. This can happen only if
                        // this is a ref port and `expandIndirectLSPs` determined that
                        // the driver doesn't actually apply to the port due to a
                        // non-overlapping internal connection expression.
                        if (&symbol == item.first) {
                            SLANG_ASSERT(symbol.isConnectedToRefPort());
                            return;
                        }

                        auto ogRange = original->getSourceRange();
                        auto newDriver = ValueDriver::create(
                            context.alloc, original->kind, lsp, *original->containingSymbol,
                            original->flags | DriverFlags::ViaIndirectPort, &ogRange);

                        addFromLSP(context, driverAlloc, *newDriver, symbol, evalCtx,
                                   hierPortDrivers);
                    });
            }

            for (auto& hpd : hierPortDrivers)
                noteHierPortDriver(context, driverAlloc, hpd);
        });
    }
}

void DriverTracker::addDrivers(AnalysisContext& context, DriverAlloc& driverAlloc,
                               const Expression& expr, DriverKind driverKind,
                               bitmask<DriverFlags> driverFlags, const Symbol& containingSymbol) {
    EvalContext evalCtx(containingSymbol);
    SmallVector<HierPortDriver> hierPortDrivers;
    LSPUtilities::visitLSPs(
        expr, evalCtx, [&](const ValueSymbol& symbol, const Expression& lsp, bool isLValue) {
            // If this is not an lvalue, we don't care about it.
            if (!isLValue)
                return;

            auto driver = ValueDriver::create(context.alloc, driverKind, lsp, containingSymbol,
                                              driverFlags);

            addFromLSP(context, driverAlloc, *driver, symbol, evalCtx, hierPortDrivers);
        });

    for (auto& hpd : hierPortDrivers)
        noteHierPortDriver(context, driverAlloc, hpd);
}

void DriverTracker::addFromLSP(AnalysisContext& context, DriverAlloc& driverAlloc,
                               const ValueDriver& driver, const ValueSymbol& symbol,
                               EvalContext& evalCtx, SmallVector<HierPortDriver>& hierPortDrivers) {
    auto bounds = LSPUtilities::getBounds(*driver.lsp, evalCtx, symbol.getType());
    if (!bounds)
        return;

    auto updateFunc = [&](auto& elem) {
        addDriver(context, driverAlloc, *elem.first, elem.second, driver, *bounds, hierPortDrivers);
    };
    symbolDrivers.try_emplace_and_visit(&symbol, updateFunc, updateFunc);
}

DriverList DriverTracker::getDrivers(const ValueSymbol& symbol) const {
    DriverList drivers;
    symbolDrivers.cvisit(&symbol, [&drivers](auto& item) {
        for (auto it = item.second.begin(); it != item.second.end(); ++it)
            drivers.emplace_back(*it, it.bounds());
    });
    return drivers;
}

std::optional<InstanceDriverState> DriverTracker::getInstanceState(
    const InstanceBodySymbol& symbol) const {

    std::optional<InstanceDriverState> state;
    instanceMap.cvisit(&symbol, [&state](auto& item) { state = item.second; });
    return state;
}

static std::string getLSPName(const ValueSymbol& symbol, const ValueDriver& driver) {
    FormatBuffer buf;
    EvalContext evalContext(symbol);
    LSPUtilities::stringifyLSP(*driver.lsp, evalContext, buf);
    return buf.str();
}

static bool handleOverlap(AnalysisContext& context, const ValueSymbol& symbol,
                          const ValueDriver* first, const ValueDriver* second, bool isNet,
                          bool isUWire, bool isSingleDriverUDNT, const NetType* netType) {
    // The default handling case for mixed vs multiple assignments is below.
    // First check for more specialized cases here:
    // 1. If this is a non-uwire net for an input or output port
    // 2. If this is a variable for an input port
    const bool isUnidirectionNetPort = isNet && (first->isUnidirectionalPort() ||
                                                 second->isUnidirectionalPort());

    if ((isUnidirectionNetPort && !isUWire && !isSingleDriverUDNT) ||
        (!isNet && (first->isInputPort() || second->isInputPort()))) {
        auto code = diag::InputPortAssign;
        if (isNet) {
            if (first->flags.has(DriverFlags::InputPort))
                code = diag::InputPortCoercion;
            else
                code = diag::OutputPortCoercion;
        }

        // This is a little messy; basically we want to report the correct
        // range for the port vs the assignment. We only want to do this
        // for input ports though, as output ports show up at the instantiation
        // site and we'd rather that be considered the "port declaration".
        if (second->isInputPort() || first->flags.has(DriverFlags::OutputPort))
            std::swap(first, second);

        auto& diag = context.addDiag(symbol, code, second->getSourceRange());
        diag << symbol.name;

        auto note = code == diag::OutputPortCoercion ? diag::NoteDrivenHere
                                                     : diag::NoteDeclarationHere;
        diag.addNote(note, first->getSourceRange());

        // For variable ports this is an error, for nets it's a warning.
        return isNet;
    }

    if (first->isClockVar() || second->isClockVar()) {
        // Both drivers being clockvars is allowed.
        if (first->isClockVar() && second->isClockVar())
            return true;

        // Procedural drivers are allowed to clockvars.
        if (first->kind == DriverKind::Procedural || second->kind == DriverKind::Procedural)
            return true;

        // Otherwise we have an error.
        if (second->isClockVar())
            std::swap(first, second);

        auto& diag = context.addDiag(symbol, diag::ClockVarTargetAssign, second->getSourceRange());
        diag << symbol.name;
        diag.addNote(diag::NoteReferencedHere, first->getSourceRange());
        return false;
    }

    const bool bothProcedural = first->kind == DriverKind::Procedural &&
                                second->kind == DriverKind::Procedural;

    DiagCode code;
    if (bothProcedural)
        code = diag::MultipleAlwaysAssigns;
    else if (isUWire)
        code = diag::MultipleUWireDrivers;
    else if (isSingleDriverUDNT)
        code = diag::MultipleUDNTDrivers;
    else if (second->kind == DriverKind::Continuous && first->kind == DriverKind::Continuous)
        code = diag::MultipleContAssigns;
    else
        code = diag::MixedVarAssigns;

    // If we're reporting a message about single driver procedures, make sure
    // the "primary" location is inside a single driver procedure.
    if (bothProcedural && !second->isInSingleDriverProcedure())
        std::swap(first, second);

    auto secondRange = second->getSourceRange();
    auto& diag = context.addDiag(symbol, code, secondRange);
    diag << getLSPName(symbol, *second);

    if (bothProcedural) {
        auto pbk = static_cast<ProceduralBlockKind>(second->source);
        diag << SemanticFacts::getProcedureKindStr(pbk);
    }
    else if (isSingleDriverUDNT) {
        SLANG_ASSERT(netType);
        diag << netType->name;
    }

    SourceLocation overrideLoc;
    auto addOriginalNote = [&](const ValueDriver& driver) {
        auto startLoc = driver.lsp->sourceRange.start();
        if (driver.flags.has(DriverFlags::HasOverrideRange) && startLoc != overrideLoc) {
            auto code = driver.flags.has(DriverFlags::ViaIndirectPort) ? diag::NotePortConnHere
                                                                       : diag::NoteOriginalAssign;
            diag.addNote(code, driver.lsp->sourceRange);
            overrideLoc = startLoc;
        }
    };
    addOriginalNote(*second);

    // If the two locations are the same, the symbol is driven by
    // the same source location but two different parts of the hierarchy.
    // In those cases we want a different note about what's going on.
    auto firstRange = first->getSourceRange();
    if (firstRange.start() != secondRange.start()) {
        diag.addNote(diag::NoteAssignedHere, firstRange);
    }
    else {
        auto& note = diag.addNote(diag::NoteFromHere2, SourceLocation::NoLocation);
        note << second->containingSymbol->getHierarchicalPath();
        note << first->containingSymbol->getHierarchicalPath();
    }

    addOriginalNote(*first);

    return false;
}

void DriverTracker::addDriver(AnalysisContext& context, DriverAlloc& driverAlloc,
                              const ValueSymbol& symbol, SymbolDriverMap& driverMap,
                              const ValueDriver& driver, DriverBitRange bounds,
                              SmallVector<HierPortDriver>& hierPortDrivers) {
    auto scope = symbol.getParentScope();
    SLANG_ASSERT(scope);

    // If this driver is made via an interface port connection we want to
    // note that fact as it represents a side effect for the instance that
    // is not captured in the port connections.
    if (!driver.flags.has(DriverFlags::FromSideEffect)) {
        LSPUtilities::visitComponents(
            *driver.lsp, /* includeRoot */ true, [&](const Expression& expr) {
                if (expr.kind == ExpressionKind::HierarchicalValue) {
                    auto& ref = expr.as<HierarchicalValueExpression>().ref;
                    if (ref.isViaIfacePort())
                        hierPortDrivers.push_back({&driver, &symbol, &ref});
                }
            });
    }

    // Keep track of "indirect" drivers separately so we can revisit them at the end of analysis.
    auto indirectUpdater = [&](auto& item) { item.second.emplace_back(&driver, bounds); };
    if (symbol.kind == SymbolKind::ModportPort) {
        indirectDrivers.try_emplace_and_visit(&symbol, indirectUpdater, indirectUpdater);

        // We don't do overlap detection for modports but we will still track them for downstream
        // users to query later.
        driverMap.insert(bounds, &driver, driverAlloc);
        return;
    }

    if (symbol.isConnectedToRefPort()) {
        indirectDrivers.try_emplace_and_visit(&symbol, indirectUpdater, indirectUpdater);

        if (!driver.flags.has(DriverFlags::FromSideEffect)) {
            // Ref port drivers are side effects that need to be applied to
            // non-canonical instances.
            hierPortDrivers.push_back({&driver, &symbol, nullptr});
        }

        // For ref ports we will continue on and do normal overlap checking,
        // since the ref port might not actually apply if it has an internal
        // connection expression that points somewhere else.
    }

    if (driverMap.empty()) {
        // The first time we add a driver, check whether there is also an
        // initializer expression that should count as a driver as well.
        auto addInitializer = [&](DriverKind driverKind) {
            auto& valExpr = *context.alloc.emplace<NamedValueExpression>(
                symbol, SourceRange{symbol.location, symbol.location + symbol.name.length()});

            DriverBitRange initBounds{0, symbol.getType().getSelectableWidth() - 1};
            auto initDriver = ValueDriver::create(context.alloc, driverKind, valExpr,
                                                  scope->asSymbol(), DriverFlags::Initializer);

            driverMap.insert(initBounds, initDriver, driverAlloc);
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
            driverMap.insert(bounds, &driver, driverAlloc);
            return;
        }
    }

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

    // We need to check for overlap in the following cases:
    // - static variables (automatic variables can't ever be driven continuously)
    // - uwire nets
    // - user-defined nets (UDNTs) with no resolution function
    const bool checkOverlap = (VariableSymbol::isKind(symbol.kind) &&
                               symbol.as<VariableSymbol>().lifetime == VariableLifetime::Static) ||
                              isUWire || isSingleDriverUDNT;

    const bool allowDupInitialDrivers = context.manager->hasFlag(
        AnalysisFlags::AllowDupInitialDrivers);

    auto shouldIgnore = [&](const ValueDriver& vd) {
        // We ignore drivers from subroutines and from initializers.
        // We also ignore initial blocks if the user has set a flag.
        return vd.source == DriverSource::Subroutine || vd.flags.has(DriverFlags::Initializer) ||
               (vd.source == DriverSource::Initial && allowDupInitialDrivers);
    };

    auto end = driverMap.end();
    for (auto it = driverMap.find(bounds); it != end; ++it) {
        // Check whether this pair of drivers overlapping constitutes a problem.
        // The conditions for reporting a problem are:
        // - If this is for a mix of input/output and inout ports, always report.
        // - Don't report for "Other" drivers (procedural force / release, etc)
        // - Otherwise, if is this a static var or uwire net:
        //      - Report if a mix of continuous and procedural assignments
        //      - Report if multiple continuous assignments
        bool isProblem = false;
        auto curr = *it;

        if (curr->isUnidirectionalPort() != driver.isUnidirectionalPort()) {
            isProblem = true;
        }
        else if (checkOverlap) {
            if (driver.kind == DriverKind::Continuous || curr->kind == DriverKind::Continuous) {
                isProblem = true;
            }
            else if (curr->containingSymbol != driver.containingSymbol && !shouldIgnore(*curr) &&
                     !shouldIgnore(driver) &&
                     (curr->isInSingleDriverProcedure() || driver.isInSingleDriverProcedure())) {
                isProblem = true;
            }
        }

        if (isProblem) {
            if (!handleOverlap(context, symbol, curr, &driver, isNet, isUWire, isSingleDriverUDNT,
                               netType)) {
                break;
            }
        }
    }

    driverMap.insert(bounds, &driver, driverAlloc);
}

void DriverTracker::noteHierPortDriver(AnalysisContext& context, DriverAlloc& driverAlloc,
                                       const HierPortDriver& hierPortDriver) {
    // Common logic to register this hier port driver with the containing instance
    // and to apply it to any non-canonical instances.
    auto updateAndApply = [&](const InstanceBodySymbol& instBody) {
        std::vector<const InstanceSymbol*> nonCanonicalInstances;
        auto updater = [&](auto& item) {
            auto& state = item.second;
            state.hierPortDrivers.push_back(hierPortDriver);

            // Copy these out so we can act on them outside of the concurrent visitor.
            nonCanonicalInstances = state.nonCanonicalInstances;
        };
        instanceMap.try_emplace_and_visit(&instBody, updater, updater);

        for (auto inst : nonCanonicalInstances)
            applyInstanceSideEffect(context, driverAlloc, hierPortDriver, *inst);
    };

    if (hierPortDriver.ref) {
        auto& ref = *hierPortDriver.ref;
        SLANG_ASSERT(ref.isViaIfacePort());
        SLANG_ASSERT(ref.target);
        SLANG_ASSERT(ref.expr);

        auto& port = ref.path[0].symbol->as<InterfacePortSymbol>();
        auto scope = port.getParentScope();
        SLANG_ASSERT(scope);

        auto& symbol = scope->asSymbol();
        updateAndApply(symbol.as<InstanceBodySymbol>());

        // If this driver's target is through another interface port we should
        // recursively follow it to the parent connection.
        auto [_, expr] = port.getConnectionAndExpr();
        if (expr && expr->kind == ExpressionKind::ArbitrarySymbol) {
            auto& connRef = expr->as<ArbitrarySymbolExpression>().hierRef;
            if (connRef.isViaIfacePort()) {
                HierPortDriver nextHPD = hierPortDriver;
                nextHPD.ref = &connRef.join(context.alloc, ref);
                noteHierPortDriver(context, driverAlloc, nextHPD);
            }
        }
    }
    else {
        // Must be a ref port target. Note that we don't have to go recursively up
        // the hierarchy here because we register these as "indirect drivers" which
        // will be applied recursively at the end of analysis.
        auto scope = hierPortDriver.target->getParentScope();
        SLANG_ASSERT(scope);

        auto& symbol = scope->asSymbol();
        updateAndApply(symbol.as<InstanceBodySymbol>());
    }
}

static const Symbol* retargetIfacePort(const HierarchicalReference& ref,
                                       const InstanceSymbol& base) {
    // This function retargets a hierarchical reference that begins with
    // an interface port access to a different instance that has the same port,
    // i.e. performing the same lookup for a different but identical instance.
    if (!ref.isViaIfacePort() || !ref.target)
        return nullptr;

    // Should always find the port here unless some other error occurred.
    auto& path = ref.path;
    auto port = base.body.findPort(path[0].symbol->name);
    if (!port)
        return nullptr;

    const Symbol* symbol = port;
    const ModportSymbol* modport = nullptr;
    std::optional<std::span<const Symbol* const>> instanceArrayElems;

    // Walk the path to find the target symbol.
    for (size_t i = 1; i < path.size(); i++) {
        while (symbol && symbol->kind == SymbolKind::InterfacePort)
            std::tie(symbol, modport) = symbol->as<InterfacePortSymbol>().getConnection();

        if (!symbol)
            return nullptr;

        // instanceArrayElems is valid when the prior entry in the path
        // did a range select of an interface instance array. We don't
        // have a way to represent that range as a symbol, so we track this
        // as a separate optional span of selected instances.
        if (!instanceArrayElems) {
            if (symbol->kind == SymbolKind::Instance) {
                auto& body = symbol->as<InstanceSymbol>().body;
                symbol = &body;

                // We should never see a module instance on this path
                // unless there is an error, because modules can't be
                // instantiated in interfaces,
                if (body.getDefinition().definitionKind == DefinitionKind::Module)
                    return nullptr;

                // See lookupDownward in Lookup.cpp for the logic here.
                if (modport) {
                    symbol = body.find(modport->name);
                    modport = nullptr;
                    SLANG_ASSERT(symbol);
                }
            }
            else if (symbol->kind == SymbolKind::InstanceArray) {
                instanceArrayElems = symbol->as<InstanceArraySymbol>().elements;
            }
            else if (!symbol->isScope()) {
                return nullptr;
            }
        }

        auto& elem = path[i];
        if (auto index = std::get_if<int32_t>(&elem.selector)) {
            // We're doing an element select here.
            if (instanceArrayElems) {
                // Prior entry was a range select, so select further within it.
                if (*index < 0 || size_t(*index) >= instanceArrayElems->size())
                    return nullptr;

                symbol = (*instanceArrayElems)[size_t(*index)];
            }
            else if (symbol->kind == SymbolKind::GenerateBlockArray) {
                auto& arr = symbol->as<GenerateBlockArraySymbol>();
                if (!arr.valid || *index < 0 || size_t(*index) >= arr.entries.size())
                    return nullptr;

                symbol = arr.entries[size_t(*index)];
            }
            else {
                return nullptr;
            }
        }
        else if (auto range = std::get_if<std::pair<int32_t, int32_t>>(&elem.selector)) {
            // We're doing a range select here.
            if (!instanceArrayElems)
                return nullptr;

            auto size = instanceArrayElems->size();
            if (range->first < 0 || size_t(range->second) >= size)
                return nullptr;

            if (size_t(range->first) >= size || size_t(range->second) >= size)
                return nullptr;

            // We `continue` here so that we don't reset the instanceArrayElems.
            instanceArrayElems = instanceArrayElems->subspan(
                size_t(range->first), size_t(range->second - range->first) + 1);
            continue;
        }
        else {
            auto name = std::get<std::string_view>(elem.selector);
            auto next = symbol->as<Scope>().find(name);
            if (!next && symbol->kind == SymbolKind::Modport) {
                // See lookupDownward in Lookup.cpp for the logic here.
                next = symbol->getParentScope()->find(name);
                if (!next || SemanticFacts::isAllowedInModport(next->kind) ||
                    next->kind == SymbolKind::Modport) {
                    return nullptr;
                }
            }
            symbol = next;
        }

        // Otherwise we're done with the range select if we had one.
        instanceArrayElems.reset();
    }

    return symbol;
}

void DriverTracker::applyInstanceSideEffect(AnalysisContext& context, DriverAlloc& driverAlloc,
                                            const HierPortDriver& hierPortDriver,
                                            const InstanceSymbol& instance) {
    auto newDriverAndBounds = [&](const ValueSymbol& newTarget)
        -> std::pair<ValueDriver*, std::optional<DriverBitRange>> {
        auto driver = ValueDriver::create(context.alloc, *hierPortDriver.driver, newTarget);
        driver->containingSymbol = &instance;
        driver->flags |= DriverFlags::FromSideEffect;

        EvalContext evalCtx(instance);
        auto bounds = LSPUtilities::getBounds(*driver->lsp, evalCtx, newTarget.getType());
        return {driver, bounds};
    };

    if (hierPortDriver.ref) {
        auto& ref = *hierPortDriver.ref;
        if (auto target = retargetIfacePort(ref, instance)) {
            auto& valueSym = target->as<ValueSymbol>();
            auto [driver, bounds] = newDriverAndBounds(valueSym);
            if (!bounds)
                return;

            auto updateFunc = [&](auto& elem) {
                SmallVector<HierPortDriver> unused;
                addDriver(context, driverAlloc, *elem.first, elem.second, *driver, *bounds, unused);
            };
            symbolDrivers.try_emplace_and_visit(&valueSym, updateFunc, updateFunc);
        }
    }
    else {
        // Not an interface port, so must be a ref port. Find ourselves in the new
        // instance body and assign an indirect driver, which we'll propagate later.
        if (auto newTarget = instance.body.find(hierPortDriver.target->name)) {
            auto& valueSym = newTarget->as<ValueSymbol>();
            auto [driver, bounds] = newDriverAndBounds(valueSym);
            if (!bounds)
                return;

            auto updater = [&](auto& item) { item.second.emplace_back(driver, *bounds); };
            indirectDrivers.try_emplace_and_visit(&valueSym, updater, updater);
        }
    }
}

static const Symbol* findAnyVars(const Expression& expr) {
    if (auto sym = expr.getSymbolReference(); sym && sym->kind != SymbolKind::Net)
        return sym;

    if (expr.kind == ExpressionKind::Concatenation) {
        for (auto op : expr.as<ConcatenationExpression>().operands()) {
            if (auto sym = findAnyVars(*op))
                return sym;
        }
    }

    return nullptr;
}

void DriverTracker::checkNetCollapsing(AnalysisContext& context, const PortConnection& conn) {
    auto expr = conn.getExpression();
    SLANG_ASSERT(expr && !expr->bad() && conn.port.kind == SymbolKind::Port);

    // If there are nets on either side of the connection we may need
    // to do dissimilar net type collapsing. All such checks happen
    // on bit ranges, as different bits may have different net types.
    SmallVector<PortSymbol::NetTypeRange, 4> internal;
    auto& port = conn.port.as<PortSymbol>();
    port.getNetTypes(internal);

    SmallVector<PortSymbol::NetTypeRange, 4> external;
    PortSymbol::getNetRanges(*expr, external);

    // There might not be any nets, in which case we should just leave.
    if (internal.empty() && external.empty())
        return;

    // Do additional checking on the expression for interconnect port connections.
    if (internal.size() == 1 && internal[0].netType->netKind == NetType::Interconnect) {
        if (auto sym = findAnyVars(*expr)) {
            context.addDiag(port, diag::InterconnectPortVar, expr->sourceRange) << sym->name;
            return;
        }
    }

    auto requireMatching = [&](const NetType& udnt) {
        // Types are more restricted; they must match instead of just being
        // assignment compatible. Also direction must be input or output.
        // We need to do this dance to get at the type of the connection prior
        // to it being converted to match the type of the port.
        auto exprType = expr->type.get();
        if (expr->kind == ExpressionKind::Conversion) {
            auto& conv = expr->as<ConversionExpression>();
            if (conv.isImplicit())
                exprType = conv.operand().type;
        }
        else if (expr->kind == ExpressionKind::Assignment) {
            auto& assign = expr->as<AssignmentExpression>();
            if (assign.isLValueArg())
                exprType = assign.left().type;
        }

        auto& type = port.getType();
        if (!type.isMatching(*exprType)) {
            // If this is from an interconnect connection, don't require matching types.
            auto isInterconnect = [](const Type& t) {
                auto curr = &t;
                while (curr->isArray())
                    curr = curr->getArrayElementType();

                return curr->isUntypedType();
            };

            if (isInterconnect(type) || isInterconnect(*exprType))
                return;

            auto& diag = context.addDiag(port, diag::MismatchedUserDefPortConn, expr->sourceRange);
            diag << udnt.name;
            diag << type;
            diag << *exprType;
        }
        else if (port.direction != ArgumentDirection::In &&
                 port.direction != ArgumentDirection::Out) {
            auto& diag = context.addDiag(port, diag::MismatchedUserDefPortDir, expr->sourceRange);
            diag << udnt.name;
        }
    };

    // If only one side has net types, check for user-defined nettypes,
    // which impose additional restrictions on the connection.
    if (internal.empty() || external.empty()) {
        const NetType* udnt = nullptr;
        auto checker = [&](auto& list) {
            for (auto& ntr : list) {
                if (!ntr.netType->isBuiltIn()) {
                    udnt = ntr.netType;
                    break;
                }
            }
        };

        checker(internal);
        checker(external);
        if (udnt)
            requireMatching(*udnt);

        return;
    }

    // Simple case is one net connected on each side.
    if (internal.size() == 1 && external.size() == 1) {
        auto& inNt = *internal[0].netType;
        auto& exNt = *external[0].netType;
        if (&inNt == &exNt)
            return;

        if (!inNt.isBuiltIn() || !exNt.isBuiltIn()) {
            // If both sides are user-defined nettypes they need to match.
            if (!inNt.isBuiltIn() && !exNt.isBuiltIn()) {
                auto& diag = context.addDiag(port, diag::UserDefPortTwoSided, expr->sourceRange);
                diag << inNt.name << exNt.name;
            }
            else if (!inNt.isBuiltIn()) {
                requireMatching(inNt);
            }
            else {
                requireMatching(exNt);
            }
        }
        else {
            // Otherwise both sides are built-in nettypes.
            bool shouldWarn;
            NetType::getSimulatedNetType(inNt, exNt, shouldWarn);
            if (shouldWarn) {
                auto diagCode = conn.isImplicit ? diag::ImplicitConnNetInconsistent
                                                : diag::NetInconsistent;
                auto& diag = context.addDiag(port, diagCode, expr->sourceRange);
                diag << exNt.name;
                diag << inNt.name;
                diag.addNote(diag::NoteDeclarationHere, port.location);
            }
        }

        return;
    }

    // Otherwise we need to compare ranges of net types for differences.
    auto in = internal.begin();
    auto ex = external.begin();
    bitwidth_t currBit = 0;
    bitwidth_t exprWidth = expr->type->getBitWidth();
    bool shownDeclaredHere = false;

    while (true) {
        bool shouldWarn;
        auto& inNt = *in->netType;
        auto& exNt = *ex->netType;

        if (!inNt.isBuiltIn() || !exNt.isBuiltIn()) {
            if (&inNt != &exNt) {
                context.addDiag(port, diag::UserDefPortMixedConcat, expr->sourceRange)
                    << inNt.name << exNt.name;
                return;
            }
            shouldWarn = false;
        }
        else {
            NetType::getSimulatedNetType(inNt, exNt, shouldWarn);
        }

        bitwidth_t width;
        if (in->width < ex->width) {
            width = in->width;
            ex->width -= width;
            in++;
        }
        else {
            width = ex->width;
            ex++;

            if (in->width == width)
                in++;
            else
                in->width -= width;
        }

        if (shouldWarn) {
            SLANG_ASSERT(exprWidth >= currBit + width);
            bitwidth_t left = exprWidth - currBit - 1;
            bitwidth_t right = left - (width - 1);

            auto& diag = context.addDiag(port, diag::NetRangeInconsistent, expr->sourceRange);
            diag << exNt.name;
            diag << left << right;
            diag << inNt.name;

            if (!shownDeclaredHere) {
                diag.addNote(diag::NoteDeclarationHere, port.location);
                shownDeclaredHere = true;
            }
        }

        if (in == internal.end() || ex == external.end())
            break;

        currBit += width;
    }
}

} // namespace slang::analysis
