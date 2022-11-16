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
#include "slang/util/Iterator.h"

namespace slang::ast {

class Compilation;
class EvalContext;
class PortSymbol;
class ProceduralBlockSymbol;
class ValueDriver;

using DriverIntervalMap = IntervalMap<uint32_t, const ValueDriver*>;

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
                   const Symbol& containingSymbol, bitmask<AssignFlags> flags,
                   EvalContext* customEvalContext = nullptr) const;

    void addDriver(DriverKind kind, std::pair<uint32_t, uint32_t> bounds,
                   const Expression& longestStaticPrefix, const Symbol& containingSymbol,
                   const Expression& procCallExpression) const;

    iterator_range<DriverIntervalMap::const_iterator> drivers() const {
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
    ValueSymbol(SymbolKind kind, string_view name, SourceLocation location,
                bitmask<DeclaredTypeFlags> flags = DeclaredTypeFlags::None);

private:
    void addDriverImpl(const Scope& scope, std::pair<uint32_t, uint32_t> bounds,
                       const ValueDriver& driver) const;

    DeclaredType declaredType;
    mutable DriverIntervalMap driverMap;
    mutable const PortBackref* firstPortBackref = nullptr;
};

class SLANG_EXPORT ValueDriver {
public:
    not_null<const Expression*> prefixExpression;
    not_null<const Symbol*> containingSymbol;
    const Expression* procCallExpression = nullptr;
    bitmask<AssignFlags> flags;
    DriverKind kind;

    ValueDriver(DriverKind kind, const Expression& longestStaticPrefix,
                const Symbol& containingSymbol, bitmask<AssignFlags> flags) :
        prefixExpression(&longestStaticPrefix),
        containingSymbol(&containingSymbol), flags(flags), kind(kind) {}

    bool isInputPort() const { return flags.has(AssignFlags::InputPort); }
    bool isUnidirectionalPort() const {
        return flags.has(AssignFlags::InputPort | AssignFlags::OutputPort);
    }
    bool isClockVar() const { return flags.has(AssignFlags::ClockVar); }
    bool isLocalVarFormalArg() const { return flags.has(AssignFlags::AssertionLocalVarFormalArg); }

    bool isInSingleDriverProcedure() const;
    bool isInSubroutine() const;
    bool isInInitialBlock() const;

    SourceRange getSourceRange() const;

    static std::optional<std::pair<uint32_t, uint32_t>> getBounds(
        const Expression& prefixExpression, EvalContext& evalContext, const Type& rootType);
};

} // namespace slang::ast
