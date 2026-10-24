//------------------------------------------------------------------------------
//! @file DriverTracker.h
//! @brief Centralized tracking of assigned / driven symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/ValuePath.h"
#include "slang/util/ConcurrentMap.h"
#include "slang/util/FlatMap.h"
#include "slang/util/IntervalMap.h"

namespace slang::ast {

class ClockVarSymbol;
class EvalContext;
class Expression;
class HierarchicalReference;
class InstanceBodySymbol;
class InstanceSymbol;
class PortConnection;
class PortSymbol;
class Symbol;
class ValueSymbol;

} // namespace slang::ast

namespace slang::analysis {

class AnalysisContext;
class AnalyzedProcedure;
class ValueDriver;

enum class DriverFlags : uint8_t;
enum class DriverKind : uint8_t;
enum class DriverSource : uint8_t;

/// State tracked per canonical instance.
struct SLANG_EXPORT InstanceDriverState {
    /// Information about a driver that is applied hierarchically through an
    /// interface or ref port and so needs to be reapplied for non-canonical instances.
    struct HierPortDriver {
        /// The driver that was applied to the interface or ref port.
        not_null<const ValueDriver*> driver;

        /// If this was an interface port driver, the hierarchical reference
        /// that describes how the driver was applied. Otherwise nullptr.
        const ast::HierarchicalReference* ref = nullptr;
    };

    /// Drivers that are applied through hierarchical ports.
    std::vector<HierPortDriver> hierPortDrivers;

    /// A list of instances that refer to the canonical one.
    std::vector<const ast::InstanceSymbol*> nonCanonicalInstances;
};

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

    // Adds drivers for the given clock variable to the tracker.
    void add(AnalysisContext& context, DriverAlloc& driverAlloc, const ast::ClockVarSymbol& symbol);

    // Adds drivers for the given expression to the tracker.
    void add(AnalysisContext& context, DriverAlloc& driverAlloc, const ast::Expression& expr,
             const ast::Symbol& containingSymbol);

    /// Adds the given drivers to the tracker.
    void add(AnalysisContext& context, DriverAlloc& driverAlloc,
             std::span<const ValueDriver* const> drivers);

    /// Records the existence of a non-canonical instance, which may imply that
    /// additional drivers should be applied based on the canonical instance.
    void noteNonCanonicalInstance(AnalysisContext& context, DriverAlloc& driverAlloc,
                                  const ast::InstanceSymbol& instance);

    /// Propagates drivers of modport ports and ref ports down to the targets of their
    /// actual port connections.
    void propagateIndirectDrivers(AnalysisContext& context, DriverAlloc& driverAlloc);

    /// Returns all of the tracked drivers for the given symbol.
    std::vector<const ValueDriver*> getDrivers(const ast::ValueSymbol& symbol) const;

    /// Return the state tracked per canonical instance.
    std::optional<InstanceDriverState> getInstanceState(
        const ast::InstanceBodySymbol& symbol) const;

private:
    using HierPortDriver = InstanceDriverState::HierPortDriver;

    // The drivers of one symbol. A driver into the elements of a dynamically sized
    // array, such as a["k"][0], is kept in the storage of those elements, and is also
    // noted at the bit of each array it goes through on the way (a in the symbol,
    // a["k"] in the storage of a's elements), so that a write of a whole array finds
    // it. Most symbols have drivers only in the symbol itself.
    struct SymbolDrivers {
        bool empty() const { return root.own.empty() && !root.elements; }

        void insert(const ValueDriver& driver, const ast::StoragePlace& place,
                    DriverAlloc& driverAlloc);

        // Gets the drivers whose bits overlap @a place.
        void getOverlapping(const ast::StoragePlace& place,
                            SmallVector<const ValueDriver*>& results) const;

        // Gets every driver, in the order of their bits in the symbol.
        void getAll(std::vector<const ValueDriver*>& results) const;

        struct Elements;
        struct Storage {
            SymbolDriverMap own;

            // Allocated once a driver goes on into the elements of an array held here.
            std::unique_ptr<Elements> elements;
        };
        struct Elements {
            // Drivers into the elements, at the bit of the array they go through here.
            SymbolDriverMap nested;
            flat_hash_map<ast::ElementStorage::Step, Storage> storage;
        };

        Storage root;
    };

    void addDriver(AnalysisContext& context, DriverAlloc& driverAlloc, SymbolDrivers& drivers,
                   const ValueDriver& driver, SmallVector<HierPortDriver>& hierPortDrivers);
    void noteHierPortDriver(AnalysisContext& context, DriverAlloc& driverAlloc,
                            const HierPortDriver& hierPortDriver);
    void applyInstanceSideEffect(AnalysisContext& context, DriverAlloc& driverAlloc,
                                 const HierPortDriver& hierPortDriver,
                                 const ast::InstanceSymbol& instance);
    void addDrivers(AnalysisContext& context, DriverAlloc& driverAlloc, const ast::Expression& expr,
                    DriverKind driverKind, bitmask<DriverFlags> driverFlags,
                    const ast::Symbol& containingSymbol);

    void checkNetCollapsing(AnalysisContext& context, const ast::PortConnection& conn);

    concurrent_map<const ast::ValueSymbol*, SymbolDrivers> symbolDrivers;
    concurrent_map<const ast::InstanceBodySymbol*, InstanceDriverState> instanceMap;
    concurrent_map<const ast::ValueSymbol*, std::vector<const ValueDriver*>> indirectDrivers;
};

} // namespace slang::analysis
