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

namespace slang::ast {

class Compilation;
class EvalContext;
class ProceduralBlockSymbol;

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

    class Driver {
    private:
        friend class ValueSymbol;
        mutable const Driver* next = nullptr;

    public:
        not_null<const Symbol*> containingSymbol;
        SourceRange sourceRange;
        uint32_t numPrefixEntries;
        DriverKind kind;
        bitmask<AssignFlags> flags;
        bool hasOriginalRange;
        bool hasError = false;

        const Driver* getNextDriver() const { return next; }
        span<const ConstantRange> getPrefix() const;
        SourceRange getOriginalRange() const;

        bool isInputPort() const { return flags.has(AssignFlags::InputPort); }
        bool isUnidirectionalPort() const {
            return flags.has(AssignFlags::InputPort | AssignFlags::OutputPort);
        }
        bool isClockVar() const { return flags.has(AssignFlags::ClockVar); }
        bool isLocalVarFormalArg() const {
            return flags.has(AssignFlags::AssertionLocalVarFormalArg);
        }

        bool isInSingleDriverProcedure() const;
        bool isInSubroutine() const;
        bool isInInitialBlock() const;

        bool overlaps(const Driver& other) const;

        static Driver& create(EvalContext& evalContext, DriverKind kind,
                              const Expression& longestStaticPrefix, const Symbol& containingSymbol,
                              bitmask<AssignFlags> flags, SourceRange range);

        static Driver& create(Compilation& compilation, DriverKind kind,
                              span<const ConstantRange> longestStaticPrefix,
                              const Symbol& containingSymbol, bitmask<AssignFlags> flags,
                              SourceRange range, SourceRange originalRange);

    private:
        Driver(DriverKind kind, const Symbol& containingSymbol, bitmask<AssignFlags> flags,
               uint32_t numPrefixEntries, bool hasOriginalRange) :
            containingSymbol(&containingSymbol),
            numPrefixEntries(numPrefixEntries), kind(kind), flags(flags),
            hasOriginalRange(hasOriginalRange) {}
    };

    void addDriver(DriverKind kind, const Expression& longestStaticPrefix,
                   const Symbol& containingSymbol, bitmask<AssignFlags> flags,
                   SourceRange rangeOverride = {}, EvalContext* customEvalContext = nullptr) const;

    void addDriver(DriverKind kind, const Driver& copyFrom, const Symbol& containingSymbol,
                   bitmask<AssignFlags> flags, SourceRange rangeOverride) const;

    const Driver* getFirstDriver() const { return firstDriver; }

protected:
    ValueSymbol(SymbolKind kind, string_view name, SourceLocation location,
                bitmask<DeclaredTypeFlags> flags = DeclaredTypeFlags::None);

private:
    void addDriverImpl(const Scope& scope, const Driver& driver) const;

    DeclaredType declaredType;
    mutable const Driver* firstDriver = nullptr;
};

} // namespace slang::ast
