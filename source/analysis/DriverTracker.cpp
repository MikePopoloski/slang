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
    if (port.kind == SymbolKind::Port)
        direction = port.as<PortSymbol>().direction;
    else
        direction = port.as<MultiPortSymbol>().direction;

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
            for (auto& [originalDriver, _] : item.second) {
                EvalContext evalCtx(*originalDriver->containingSymbol);
                LSPUtilities::expandIndirectLSPs(
                    context.alloc, *originalDriver->prefixExpression, evalCtx,
                    [&](const ValueSymbol& symbol, const Expression& lsp, bool isLValue) {
                        // If the LSP maps to the same symbol as the original driver,
                        // skip it to avoid infinite recursion. This can happen only if
                        // this is a ref port and `expandIndirectLSPs` determined that
                        // the driver doesn't actually apply to the port due to a
                        // non-overlapping internal connection expression.
                        if (&symbol == item.first) {
                            SLANG_ASSERT(symbol.isConnectedToRefPort());
                            return;
                        }

                        addFromLSP(context, driverAlloc, originalDriver->kind,
                                   originalDriver->flags, *originalDriver->containingSymbol, symbol,
                                   lsp, isLValue, evalCtx, hierPortDrivers);
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
    LSPUtilities::visitLSPs(expr, evalCtx,
                            [&](const ValueSymbol& symbol, const Expression& lsp, bool isLValue) {
                                addFromLSP(context, driverAlloc, driverKind, driverFlags,
                                           containingSymbol, symbol, lsp, isLValue, evalCtx,
                                           hierPortDrivers);
                            });

    for (auto& hpd : hierPortDrivers)
        noteHierPortDriver(context, driverAlloc, hpd);
}

void DriverTracker::addFromLSP(AnalysisContext& context, DriverAlloc& driverAlloc,
                               DriverKind driverKind, bitmask<DriverFlags> driverFlags,
                               const ast::Symbol& containingSymbol, const ValueSymbol& symbol,
                               const Expression& lsp, bool isLValue, EvalContext& evalCtx,
                               SmallVector<HierPortDriver>& hierPortDrivers) {
    // If this is not an lvalue, we don't care about it.
    if (!isLValue)
        return;

    auto bounds = LSPUtilities::getBounds(lsp, evalCtx, symbol.getType());
    if (!bounds)
        return;

    auto driver = context.alloc.emplace<ValueDriver>(driverKind, lsp, containingSymbol,
                                                     driverFlags);

    auto updateFunc = [&](auto& elem) {
        addDriver(context, driverAlloc, *elem.first, elem.second, *driver, *bounds,
                  hierPortDrivers);
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
    LSPUtilities::stringifyLSP(*driver.prefixExpression, evalContext, buf);
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
            if (curr.flags.has(DriverFlags::InputPort))
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
        if (driver.isInputPort() || curr.flags.has(DriverFlags::OutputPort))
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

void DriverTracker::addDriver(AnalysisContext& context, DriverAlloc& driverAlloc,
                              const ValueSymbol& symbol, SymbolDriverMap& driverMap,
                              const ValueDriver& driver, DriverBitRange bounds,
                              SmallVector<HierPortDriver>& hierPortDrivers) {
    auto scope = symbol.getParentScope();
    SLANG_ASSERT(scope);

    // If this driver is made via an interface port connection we want to
    // note that fact as it represents a side effect for the instance that
    // is not captured in the port connections.
    if (!driver.isFromSideEffect) {
        LSPUtilities::visitComponents(
            *driver.prefixExpression, /* includeRoot */ true, [&](const Expression& expr) {
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

        if (!driver.isFromSideEffect) {
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
            auto initDriver = context.alloc.emplace<ValueDriver>(driverKind, valExpr,
                                                                 scope->asSymbol(),
                                                                 DriverFlags::Initializer);

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
                              isUWire || isSingleDriverUDNT;

    const bool allowDupInitialDrivers = context.manager->hasFlag(
        AnalysisFlags::AllowDupInitialDrivers);

    auto shouldIgnore = [&](const ValueDriver& vd) {
        // We ignore drivers from subroutines and from initializers.
        // We also ignore initial blocks if the user has set a flag.
        return vd.source == DriverSource::Subroutine || vd.flags.has(DriverFlags::Initializer) ||
               (vd.source == DriverSource::Initial && allowDupInitialDrivers);
    };

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
            if (!handleOverlap(context, symbol, *curr, driver, isNet, isUWire, isSingleDriverUDNT,
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
        auto driver = context.alloc.emplace<ValueDriver>(*hierPortDriver.driver);
        driver->containingSymbol = &instance;
        driver->isFromSideEffect = true;

        EvalContext evalCtx(instance);
        auto bounds = LSPUtilities::getBounds(*driver->prefixExpression, evalCtx,
                                              newTarget.getType());
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
        // TODO: add test for explicit port expression that connects hierarchically
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

} // namespace slang::analysis
