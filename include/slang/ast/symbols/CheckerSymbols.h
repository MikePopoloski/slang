//------------------------------------------------------------------------------
//! @file CheckerSymbols.h
//! @brief Contains checker-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/symbols/InstanceSymbols.h"

namespace slang::ast {

class AssertionPortSymbol;
class CheckerInstanceBodySymbol;
class Expression;

/// Represents a checker declaration.
class SLANG_EXPORT CheckerSymbol final : public Symbol, public Scope {
public:
    std::span<const AssertionPortSymbol* const> ports;

    CheckerSymbol(Compilation& compilation, std::string_view name, SourceLocation loc);

    static CheckerSymbol& fromSyntax(const Scope& scope,
                                     const syntax::CheckerDeclarationSyntax& syntax);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Checker; }
};

/// Represents an instance of a checker.
class SLANG_EXPORT CheckerInstanceSymbol final : public InstanceSymbolBase {
public:
    const CheckerInstanceBodySymbol& body;

    CheckerInstanceSymbol(std::string_view name, SourceLocation loc,
                          CheckerInstanceBodySymbol& body);

    class SLANG_EXPORT Connection {
    public:
        const CheckerInstanceBodySymbol& parent;
        const Symbol& formal;
        std::variant<const Expression*, const AssertionExpr*, const TimingControl*> actual;
        std::span<const AttributeSymbol* const> attributes;

        Connection(const CheckerInstanceBodySymbol& parent, const Symbol& formal,
                   const syntax::ExpressionSyntax* outputInitialSyntax,
                   std::span<const AttributeSymbol* const> attributes) :
            parent(parent), formal(formal), attributes(attributes),
            outputInitialSyntax(outputInitialSyntax) {}

        const Expression* getOutputInitialExpr() const;

    private:
        const syntax::ExpressionSyntax* outputInitialSyntax;
        mutable std::optional<const Expression*> outputInitialExpr;
    };

    std::span<const Connection> getPortConnections() const;

    static void fromSyntax(const CheckerSymbol& checker,
                           const syntax::HierarchyInstantiationSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets,
                           bitmask<InstanceFlags> flags);

    static void fromSyntax(const syntax::CheckerInstantiationSyntax& syntax,
                           const ASTContext& context, SmallVectorBase<const Symbol*>& results,
                           SmallVectorBase<const Symbol*>& implicitNets,
                           bitmask<InstanceFlags> flags);

    /// Creates an intentionally invalid instance by forcing all port connections to
    /// null values. This allows type checking instance members as long as they don't
    /// depend on any port expansion.
    static CheckerInstanceSymbol& createInvalid(const CheckerSymbol& checker, uint32_t depth);

    static CheckerInstanceSymbol& fromSyntax(
        Compilation& compilation, const ASTContext& context, const CheckerSymbol& checker,
        const syntax::HierarchicalInstanceSyntax& syntax,
        std::span<const syntax::AttributeInstanceSyntax* const> attributes,
        SmallVectorBase<uint32_t>& path, bool isProcedural, bitmask<InstanceFlags> flags);

    void verifyMembers() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CheckerInstance; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const; // implementation is in ASTVisitor.h

private:
    std::span<Connection> connections;
    mutable bool connectionsResolved = false;
};

/// The body of a checker instance, which acts as the scope for its members.
class SLANG_EXPORT CheckerInstanceBodySymbol final : public Symbol, public Scope {
public:
    /// The parent instance for which this is the body.
    const CheckerInstanceSymbol* parentInstance = nullptr;

    const CheckerSymbol& checker;
    const AssertionInstanceDetails& assertionDetails;
    uint32_t instanceDepth;
    bool isProcedural;
    bitmask<InstanceFlags> flags;

    CheckerInstanceBodySymbol(Compilation& compilation, const CheckerSymbol& checker,
                              AssertionInstanceDetails& assertionDetails,
                              const ASTContext& originalContext, uint32_t instanceDepth,
                              bool isProcedural, bitmask<InstanceFlags> flags);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CheckerInstanceBody; }

private:
    ASTContext originalContext;
};

} // namespace slang::ast
