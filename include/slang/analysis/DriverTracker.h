//------------------------------------------------------------------------------
//! @file DriverTracker.h
//! @brief Centralized tracking of assigned / driven symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/analysis/ValueDriver.h"
#include "slang/util/ConcurrentMap.h"
#include "slang/util/IntervalMap.h"

namespace slang::ast {

class EvalContext;
class Expression;
class HierarchicalReference;
class InstanceBodySymbol;
class InstanceSymbol;
class PortConnection;
class PortSymbol;
class Symbol;

} // namespace slang::ast

namespace slang::analysis {

class AnalysisContext;
class AnalyzedProcedure;

/// A helper class that tracks drivers for all symbols in a thread-safe manner.
class DriverTracker {
public:
    using SymbolDriverMap = IntervalMap<uint64_t, const ValueDriver*, 5>;
    using DriverAlloc = SymbolDriverMap::allocator_type;

    /// Adds drivers for the given procedure to the tracker.
    void add(AnalysisContext& context, DriverAlloc& driverAlloc,
             const AnalyzedProcedure& procedure);

    // Adds drivers for the given port connection to the tracker.
    void add(AnalysisContext& context, DriverAlloc& driverAlloc,
             const ast::PortConnection& connection, const ast::Symbol& containingSymbol);

    // Adds drivers for the given port symbol to the tracker.
    void add(AnalysisContext& context, DriverAlloc& driverAlloc, const ast::PortSymbol& symbol);

    /// Records the existence of a non-canonical instance, which may imply that
    /// additional drivers should be applied based on the canonical instance.
    void noteNonCanonicalInstance(AnalysisContext& context, DriverAlloc& driverAlloc,
                                  const ast::InstanceSymbol& instance);

    /// Propagates drivers to modport ports down to the targets of the
    /// modport port connections.
    void propagateModportDrivers(AnalysisContext& context, DriverAlloc& driverAlloc);

    /// Returns all of the tracked drivers for the given symbol.
    std::vector<const ValueDriver*> getDrivers(const ast::ValueSymbol& symbol) const;

private:
    // State tracked per canonical instance.
    struct InstanceState {
        struct IfacePortDriver {
            not_null<const ast::HierarchicalReference*> ref;
            not_null<const ValueDriver*> driver;
        };

        // Drivers that are applied through interface ports.
        std::vector<IfacePortDriver> ifacePortDrivers;

        // A list of instances that refer to the canonical one.
        std::vector<const ast::InstanceSymbol*> nonCanonicalInstances;
    };

    const ast::HierarchicalReference* addDriver(AnalysisContext& context, DriverAlloc& driverAlloc,
                                                const ast::ValueSymbol& symbol,
                                                SymbolDriverMap& driverMap,
                                                const ValueDriver& driver, DriverBitRange bounds);
    void noteInterfacePortDriver(AnalysisContext& context, DriverAlloc& driverAlloc,
                                 const ast::HierarchicalReference& ref, const ValueDriver& driver);
    void applyInstanceSideEffect(AnalysisContext& context, DriverAlloc& driverAlloc,
                                 const InstanceState::IfacePortDriver& ifacePortDriver,
                                 const ast::InstanceSymbol& instance);
    void propagateModportDriver(AnalysisContext& context, DriverAlloc& driverAlloc,
                                const ast::Expression& connectionExpr,
                                const ValueDriver& originalDriver);
    void addDrivers(AnalysisContext& context, DriverAlloc& driverAlloc, const ast::Expression& expr,
                    ast::DriverKind driverKind, bitmask<ast::AssignFlags> assignFlags,
                    const ast::Symbol& containingSymbol,
                    const ast::Expression* initialLSP = nullptr);

    concurrent_map<const ast::ValueSymbol*, SymbolDriverMap> symbolDrivers;
    concurrent_map<const ast::InstanceBodySymbol*, InstanceState> instanceMap;
    concurrent_map<const ast::ValueSymbol*, DriverList> modportPortDrivers;
};

} // namespace slang::analysis
