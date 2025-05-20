//------------------------------------------------------------------------------
//! @file ValueDriver.h
//! @brief Tracking of assigned / driven symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <vector>

#include "slang/ast/SemanticFacts.h"
#include "slang/util/Util.h"

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

/// Represents an expression that drives a value by assigning
/// to some range of its type.
class SLANG_EXPORT ValueDriver {
public:
    /// The expression that drives the value.
    not_null<const ast::Expression*> prefixExpression;

    /// The symbol that contains the driver expression.
    not_null<const ast::Symbol*> containingSymbol;

    /// If the driver is implied inside a procedure by a subroutine,
    /// this is the call expression for that subroutine.
    const ast::Expression* procCallExpression = nullptr;

    /// Flags that control how the driver operates.
    bitmask<ast::AssignFlags> flags;

    /// The kind of driver (procedural or continuous).
    ast::DriverKind kind;

    /// The source of the driver (procedural block, subroutine, etc).
    DriverSource source;

    /// Indicates whether the driver is from a side effect of
    /// applying a cached instance body.
    bool isFromSideEffect = false;

    /// Constructs a new ValueDriver instance.
    ValueDriver(ast::DriverKind kind, const ast::Expression& longestStaticPrefix,
                const ast::Symbol& containingSymbol, bitmask<ast::AssignFlags> flags);

    /// Indicates whether the driver is for an input port.
    bool isInputPort() const { return flags.has(ast::AssignFlags::InputPort); }

    /// Indicates whether the driver is for a unidirectional port (i.e. not an inout or ref port).
    bool isUnidirectionalPort() const {
        return flags.has(ast::AssignFlags::InputPort | ast::AssignFlags::OutputPort);
    }

    /// Indicates whether the driver is for a clocking variable.
    bool isClockVar() const { return flags.has(ast::AssignFlags::ClockVar); }

    /// Indicates whether the driver is for an assertion local variable formal argument.
    bool isLocalVarFormalArg() const {
        return flags.has(ast::AssignFlags::AssertionLocalVarFormalArg);
    }

    /// Indicates whether the driver is inside a procedural block.
    bool isInProcedure() const { return source <= DriverSource::AlwaysFF; }

    /// Indicates whether the driver is inside a single-driver procedure (such as always_comb).
    bool isInSingleDriverProcedure() const {
        return source == DriverSource::AlwaysComb || source == DriverSource::AlwaysLatch ||
               source == DriverSource::AlwaysFF;
    }

    /// Gets the source range describing the driver as written in the source code.
    SourceRange getSourceRange() const;
};

} // namespace slang::analysis
