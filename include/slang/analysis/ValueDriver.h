//------------------------------------------------------------------------------
//! @file ValueDriver.h
//! @brief Tracking of assigned / driven symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <vector>

#include "slang/text/SourceLocation.h"
#include "slang/util/Util.h"

namespace slang {

class BumpAllocator;

}

namespace slang::ast {

class EvalContext;
class Expression;
class Symbol;
class ValueSymbol;

} // namespace slang::ast

namespace slang::analysis {

class ValueDriver;

using DriverBitRange = std::pair<uint64_t, uint64_t>;
using DriverList = std::vector<std::pair<const ValueDriver*, DriverBitRange>>;
using SymbolDriverListPair = std::pair<const ast::ValueSymbol*, DriverList>;

/// Specifies possible containing symbol kinds for value drivers.
enum class DriverSource : uint8_t {
    // Note: the first entries have to match the values
    // in the ProceduralBlocKind enum.
    Initial,
    Final,
    Always,
    AlwaysComb,
    AlwaysLatch,
    AlwaysFF,
    Subroutine,
    Other
};

#define DRIVER(x) x(Procedural) x(Continuous)
SLANG_ENUM_SIZED(DriverKind, uint8_t, DRIVER)
#undef DRIVER

/// A set of flags that control how assignments are checked.
enum class SLANG_EXPORT DriverFlags : uint8_t {
    /// No special assignment behavior specified.
    None = 0,

    /// The assignment is for an input port of a module / interface / program
    /// (the assignment to the internal symbol from the port itself).
    InputPort = 1 << 0,

    /// The assignment is for an output port of a module / interface / program
    /// (the assignment from the port connection).
    OutputPort = 1 << 1,

    /// The assignment is from a clocking block signal.
    ClockVar = 1 << 2,

    /// The driver is for a net or variable initializer.
    Initializer = 1 << 3,

    /// The driver is from a side effect of applying a cached instance body.
    FromSideEffect = 1 << 4,

    /// The ValueDriver object has an override range stored with it.
    HasOverrideRange = 1 << 5,

    /// The driver connects through an indirect port, such as a modport or ref port.
    ViaIndirectPort = 1 << 6
};
SLANG_BITMASK(DriverFlags, ViaIndirectPort)

/// Represents an expression that drives a value by assigning
/// to some range of its type.
class SLANG_EXPORT ValueDriver {
public:
    /// The longest static prefix expression that drives the value.
    not_null<const ast::Expression*> lsp;

    /// The symbol that contains the driver expression.
    not_null<const ast::Symbol*> containingSymbol;

    /// Flags that control how the driver operates.
    bitmask<DriverFlags> flags;

    /// The kind of driver (procedural or continuous).
    DriverKind kind;

    /// The source of the driver (procedural block, subroutine, etc).
    DriverSource source;

    /// Constructs a new ValueDriver instance.
    static ValueDriver* create(BumpAllocator& alloc, DriverKind kind, const ast::Expression& lsp,
                               const ast::Symbol& containingSymbol, bitmask<DriverFlags> flags,
                               const SourceRange* overrideRange = nullptr);

    /// Constructs a new ValueDriver instance.
    static ValueDriver* create(BumpAllocator& alloc, const ValueDriver& copyFrom,
                               const ast::ValueSymbol& newTarget);

    /// Indicates whether the driver is for an input port.
    bool isInputPort() const { return flags.has(DriverFlags::InputPort); }

    /// Indicates whether the driver is for a unidirectional port (i.e. not an inout or ref port).
    bool isUnidirectionalPort() const {
        return flags.has(DriverFlags::InputPort | DriverFlags::OutputPort);
    }

    /// Indicates whether the driver is for a clocking variable.
    bool isClockVar() const { return flags.has(DriverFlags::ClockVar); }

    /// Indicates whether the driver is inside a single-driver procedure (such as always_comb).
    bool isInSingleDriverProcedure() const {
        return source == DriverSource::AlwaysComb || source == DriverSource::AlwaysLatch ||
               source == DriverSource::AlwaysFF;
    }

    /// Gets the source range describing the driver as written in the source code.
    SourceRange getSourceRange() const;

    /// Gets an optional extra source range that indicates the driver actually came
    /// from some other, indirected location (like a modport port expansion).
    const SourceRange* getOverrideRange() const;

private:
    ValueDriver(DriverKind kind, const ast::Expression& lsp, const ast::Symbol& containingSymbol,
                bitmask<DriverFlags> flags);
};

} // namespace slang::analysis
