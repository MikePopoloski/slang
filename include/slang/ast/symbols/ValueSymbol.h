//------------------------------------------------------------------------------
//! @file ValueSymbol.h
//! @brief Base class for all value symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/SemanticFacts.h"
#include "slang/ast/Symbol.h"
#include "slang/ast/types/DeclaredType.h"
#include "slang/util/IntervalMap.h"

namespace slang::ast {

class EvalContext;
class PortSymbol;
class ValueDriver;

using DriverIntervalMap = IntervalMap<uint64_t, const ValueDriver*>;
using DriverBitRange = std::pair<uint64_t, uint64_t>;

/// A base class for symbols that represent a value (for example a variable or a parameter).
/// The common functionality is that they all have a type.
class SLANG_EXPORT ValueSymbol : public Symbol {
public:
    /// Gets the type of the value.
    const Type& getType() const { return declaredType.getType(); }

    /// Sets the type of the value.
    void setType(const Type& type) { declaredType.setType(type); }

    /// Gets access to the symbol's declared type.
    not_null<const DeclaredType*> getDeclaredType() const { return &declaredType; }
    not_null<DeclaredType*> getDeclaredType() { return &declaredType; }

    /// Sets the symbol's declared type.
    void setDeclaredType(const syntax::DataTypeSyntax& newType) {
        declaredType.setTypeSyntax(newType);
    }
    void setDeclaredType(const syntax::DataTypeSyntax& newType,
                         const syntax::SyntaxList<syntax::VariableDimensionSyntax>& newDimensions) {
        declaredType.setTypeSyntax(newType);
        declaredType.setDimensionSyntax(newDimensions);
    }

    /// Gets the initializer for this value, if it has one.
    const Expression* getInitializer() const { return declaredType.getInitializer(); }

    /// Sets the initializer for this value.
    void setInitializer(const Expression& expr) { declaredType.setInitializer(expr); }

    /// Sets the expression tree used to initialize this value.
    void setInitializerSyntax(const syntax::ExpressionSyntax& syntax, SourceLocation initLocation) {
        declaredType.setInitializerSyntax(syntax, initLocation);
    }

    /// Initializes the value's dimension and initializer syntax from the given declarator.
    void setFromDeclarator(const syntax::DeclaratorSyntax& decl);

    static bool isKind(SymbolKind kind);

    void addDriver(DriverKind kind, const Expression& longestStaticPrefix,
                   const Symbol& containingSymbol, bitmask<AssignFlags> flags) const;

    void addDriver(DriverKind kind, DriverBitRange bounds, const Expression& longestStaticPrefix,
                   const Symbol& containingSymbol, const Expression& procCallExpression) const;

    void addDriver(DriverBitRange bounds, const ValueDriver& driver) const;

    std::ranges::subrange<DriverIntervalMap::const_iterator> drivers() const {
        return {driverMap.begin(), driverMap.end()};
    }

    class PortBackref {
    public:
        not_null<const PortSymbol*> port;

        PortBackref(const PortSymbol& port, const PortBackref* next) : port(&port), next(next) {}

        const PortBackref* getNextBackreference() const { return next; }

    private:
        const PortBackref* next;
    };

    void addPortBackref(const PortSymbol& port) const;
    const PortBackref* getFirstPortBackref() const { return firstPortBackref; }

protected:
    ValueSymbol(SymbolKind kind, std::string_view name, SourceLocation location,
                bitmask<DeclaredTypeFlags> flags = DeclaredTypeFlags::None);

private:
    DeclaredType declaredType;
    mutable DriverIntervalMap driverMap;
    mutable const PortBackref* firstPortBackref = nullptr;
};

/// Represents an expression that drives a value by assigning
/// to some range of its type.
class SLANG_EXPORT ValueDriver {
public:
    /// The expression that drives the value.
    not_null<const Expression*> prefixExpression;

    /// The symbol that contains the driver expression.
    not_null<const Symbol*> containingSymbol;

    /// If the driver is implied inside a procedure by a subroutine,
    /// this is the call expression for that subroutine.
    const Expression* procCallExpression = nullptr;

    /// Flags that control how the driver operates.
    bitmask<AssignFlags> flags;

    /// The kind of driver (procedural or continuous).
    DriverKind kind;

    /// Constructs a new ValueDriver instance.
    ValueDriver(DriverKind kind, const Expression& longestStaticPrefix,
                const Symbol& containingSymbol, bitmask<AssignFlags> flags) :
        prefixExpression(&longestStaticPrefix), containingSymbol(&containingSymbol), flags(flags),
        kind(kind) {}

    /// Indicates whether the driver is for an input port.
    bool isInputPort() const { return flags.has(AssignFlags::InputPort); }

    /// Indicates whether the driver is for a unidirectional port (i.e. not an inout or ref port).
    bool isUnidirectionalPort() const {
        return flags.has(AssignFlags::InputPort | AssignFlags::OutputPort);
    }

    /// Indicates whether the driver is for a clocking variable.
    bool isClockVar() const { return flags.has(AssignFlags::ClockVar); }

    /// Indicates whether the driver is for an assertion local variable formal argument.
    bool isLocalVarFormalArg() const { return flags.has(AssignFlags::AssertionLocalVarFormalArg); }

    /// Indicates whether the driver is inside a single-driver procedure (such as always_comb).
    bool isInSingleDriverProcedure() const;

    /// Indicates whether the driver is inside a subroutine.
    bool isInSubroutine() const;

    /// Indicates whether the driver is inside an initial block.
    bool isInInitialBlock() const;

    /// Indicates whether the driver is inside an always_ff block.
    bool isInAlwaysFFBlock() const;

    /// Indicates whether the driver is inside an always_latch block.
    bool isInAlwaysLatchBlock() const;

    /// Gets the source range describing the driver as written in the source code.
    SourceRange getSourceRange() const;

    /// Computes bounds for a driver given its longest static prefix expression.
    static std::optional<DriverBitRange> getBounds(const Expression& prefixExpression,
                                                   EvalContext& evalContext, const Type& rootType);
};

} // namespace slang::ast
