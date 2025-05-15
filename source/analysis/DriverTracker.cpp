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
#include "slang/analysis/LSPUtilities.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/types/NetType.h"
#include "slang/diagnostics/AnalysisDiags.h"

namespace slang::analysis {

using namespace ast;

void DriverTracker::add(AnalysisContext& context, DriverAlloc& driverAlloc,
                        const AnalyzedProcedure& procedure) {
    SmallVector<std::pair<const HierarchicalReference*, const ValueDriver*>> ifacePortRefs;
    for (auto& [valueSym, drivers] : procedure.getDrivers()) {
        auto updateFunc = [&](auto& elem) {
            for (auto& [driver, bounds] : drivers) {
                auto ref = addDriver(context, driverAlloc, *elem.first, elem.second, *driver,
                                     bounds);
                if (ref) {
                    // This driver is via an interface port so we need to
                    // store and then apply it after we're done touching the
                    // symbolDrivers map.
                    ifacePortRefs.emplace_back(ref, driver);
                }
            }
        };
        symbolDrivers.try_emplace_and_visit(valueSym, updateFunc, updateFunc);
    }

    for (auto& [ref, driver] : ifacePortRefs)
        noteInterfacePortDriver(context, driverAlloc, *ref, *driver);
}

void DriverTracker::noteNonCanonicalInstance(AnalysisContext& context, DriverAlloc& driverAlloc,
                                             const InstanceSymbol& instance) {
    auto canonical = instance.getCanonicalBody();
    SLANG_ASSERT(canonical);

    std::vector<InstanceState::IfacePortDriver> ifacePortDrivers;
    auto updater = [&](auto& item) {
        auto& state = item.second;
        state.nonCanonicalInstances.push_back(&instance);

        // Copy these out so we can act on them outside of the concurrent visitor.
        ifacePortDrivers = state.ifacePortDrivers;
    };
    instanceMap.try_emplace_and_visit(canonical, updater, updater);

    for (auto& ifacePortDriver : ifacePortDrivers)
        applyInstanceSideEffect(context, driverAlloc, ifacePortDriver, instance);
}

std::vector<const ValueDriver*> DriverTracker::getDrivers(const ValueSymbol& symbol) const {
    std::vector<const ValueDriver*> drivers;
    symbolDrivers.cvisit(&symbol, [&drivers](auto& item) {
        for (auto it = item.second.begin(); it != item.second.end(); ++it)
            drivers.push_back(*it);
    });
    return drivers;
}

static std::string getLSPName(const ValueSymbol& symbol, const ValueDriver& driver) {
    auto scope = symbol.getParentScope();
    SLANG_ASSERT(scope);

    FormatBuffer buf;
    EvalContext evalContext(ASTContext(*scope, LookupLocation::after(symbol)));
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

const HierarchicalReference* DriverTracker::addDriver(
    AnalysisContext& context, DriverAlloc& driverAlloc, const ValueSymbol& symbol,
    SymbolDriverMap& driverMap, const ValueDriver& driver, DriverBitRange bounds) {

    auto scope = symbol.getParentScope();
    SLANG_ASSERT(scope);

    // If this driver is made via an interface port connection we want to
    // note that fact as it represents a side effect for the instance that
    // is not captured in the port connections.
    const HierarchicalReference* result = nullptr;
    if (!driver.isFromSideEffect) {
        LSPUtilities::visitLSP(*driver.prefixExpression, /* includeRoot */ true,
                               [&](const Expression& expr) {
                                   if (expr.kind == ExpressionKind::HierarchicalValue) {
                                       auto& ref = expr.as<HierarchicalValueExpression>().ref;
                                       if (ref.isViaIfacePort())
                                           result = &ref;
                                   }
                               });
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
                                                                 AssignFlags::None);

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
            return result;
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
                     (!context.manager->hasFlag(AnalysisFlags::AllowDupInitialDrivers) ||
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

    driverMap.insert(bounds, &driver, driverAlloc);
    return result;
}

void DriverTracker::noteInterfacePortDriver(AnalysisContext& context, DriverAlloc& driverAlloc,
                                            const HierarchicalReference& ref,
                                            const ValueDriver& driver) {
    SLANG_ASSERT(ref.isViaIfacePort());
    SLANG_ASSERT(ref.target);
    SLANG_ASSERT(ref.expr);

    auto& port = ref.path[0].symbol->as<InterfacePortSymbol>();
    auto scope = port.getParentScope();
    SLANG_ASSERT(scope);

    auto& symbol = scope->asSymbol();
    SLANG_ASSERT(symbol.kind == SymbolKind::InstanceBody);

    InstanceState::IfacePortDriver ifacePortDriver{&ref, &driver};
    std::vector<const ast::InstanceSymbol*> nonCanonicalInstances;
    auto updater = [&](auto& item) {
        auto& state = item.second;
        state.ifacePortDrivers.push_back(ifacePortDriver);

        // Copy these out so we can act on them outside of the concurrent visitor.
        nonCanonicalInstances = state.nonCanonicalInstances;
    };
    instanceMap.try_emplace_and_visit(&symbol.as<InstanceBodySymbol>(), updater, updater);

    for (auto inst : nonCanonicalInstances)
        applyInstanceSideEffect(context, driverAlloc, ifacePortDriver, *inst);

    // If this driver's target is through another interface port we should
    // recursively follow it to the parent connection.
    auto [_, expr] = port.getConnectionAndExpr();
    if (expr && expr->kind == ExpressionKind::ArbitrarySymbol) {
        auto& connRef = expr->as<ArbitrarySymbolExpression>().hierRef;
        if (connRef.isViaIfacePort())
            noteInterfacePortDriver(context, driverAlloc, connRef.join(context.alloc, ref), driver);
    }
}

void DriverTracker::applyInstanceSideEffect(AnalysisContext& context, DriverAlloc& driverAlloc,
                                            const InstanceState::IfacePortDriver& ifacePortDriver,
                                            const InstanceSymbol& instance) {
    auto& ref = *ifacePortDriver.ref;
    auto& alloc = context.alloc;
    auto scope = instance.getParentScope();
    SLANG_ASSERT(scope);

    EvalContext evalCtx(ASTContext(*scope, LookupLocation::after(instance)));

    // TODO: add test for invalid case of module instance in an interface
    // that is connected and driven through a cached port.

    auto addNewDriver = [&](const ValueSymbol& valueSym, const ValueDriver& driver) {
        // TODO: can we reuse the bounds instead of calculating them again?
        auto bounds = ValueDriver::getBounds(*driver.prefixExpression, evalCtx, valueSym.getType());
        if (!bounds)
            return;

        auto updateFunc = [&](auto& elem) {
            auto ref = addDriver(context, driverAlloc, *elem.first, elem.second, driver, *bounds);
            SLANG_ASSERT(!ref);
        };
        symbolDrivers.try_emplace_and_visit(&valueSym, updateFunc, updateFunc);
    };

    if (auto target = ref.retargetIfacePort(instance)) {
        // If we found a modport port we need to translate to the underlying
        // connection expression.
        if (target->kind == SymbolKind::ModportPort) {
            auto expr = target->as<ModportPortSymbol>().getConnectionExpr();
            SLANG_ASSERT(expr);

            auto lsp = ifacePortDriver.driver->prefixExpression.get();
            if (lsp == ref.expr)
                lsp = nullptr;

            // TODO: clean this up
            SmallVector<std::pair<const ValueSymbol*, const Expression*>> prefixes;
            expr->getLongestStaticPrefixes(prefixes, evalCtx, lsp);

            for (auto& [value, prefix] : prefixes) {
                auto driver = alloc.emplace<ValueDriver>(*ifacePortDriver.driver);
                driver->prefixExpression = prefix;
                driver->containingSymbol = &instance;
                driver->isFromSideEffect = true;
                addNewDriver(*value, *driver);
            }
        }
        else {
            auto driver = alloc.emplace<ValueDriver>(*ifacePortDriver.driver);
            driver->containingSymbol = &instance;
            driver->isFromSideEffect = true;
            addNewDriver(target->as<ValueSymbol>(), *driver);
        }
    }
}

} // namespace slang::analysis
