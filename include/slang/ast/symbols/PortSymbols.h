//------------------------------------------------------------------------------
//! @file PortSymbols.h
//! @brief Contains port-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Expression.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/numeric/ConstantValue.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

class AttributeSymbol;
class DefinitionSymbol;
class InstanceSymbol;
class ModportSymbol;

/// Represents the public-facing side of a module / program / interface port.
/// The port symbol itself is not directly referenceable from within the instance;
/// it can however connect directly to a symbol that is.
class SLANG_EXPORT PortSymbol : public Symbol {
public:
    /// An instance-internal symbol that this port connects to, if any.
    /// Ports that do not connect directly to an internal symbol will have
    /// this set to nullptr.
    const Symbol* internalSymbol = nullptr;

    /// The source location where the external name for the port is declared.
    SourceLocation externalLoc;

    /// The direction of data flowing across the port.
    ArgumentDirection direction = ArgumentDirection::InOut;

    /// Set to true for null ports, i.e. ports that don't connect to
    /// anything internal to the instance.
    bool isNullPort = false;

    /// True if this port was declared using the ansi syntax, and
    /// false if it was declared using the non-ansi syntax.
    bool isAnsiPort = false;

    PortSymbol(std::string_view name, SourceLocation loc, bool isAnsiPort);

    const Type& getType() const;
    void setType(const Type& newType) { type = &newType; }

    bool hasInitializer() const { return initializer || initializerSyntax; }
    const Expression* getInitializer() const;

    void setInitializerSyntax(const syntax::ExpressionSyntax& syntax, SourceLocation loc) {
        initializerSyntax = &syntax;
        initializerLoc = loc;
    }

    const Expression* getInternalExpr() const;

    struct NetTypeRange {
        const NetType* netType = nullptr;
        bitwidth_t width = 0;
    };
    void getNetTypes(SmallVectorBase<NetTypeRange>& ranges) const;

    bool isNetPort() const;

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(
        const syntax::PortListSyntax& syntax, const Scope& scope,
        SmallVectorBase<const Symbol*>& results,
        SmallVectorBase<std::pair<Symbol*, const Symbol*>>& implicitMembers,
        std::span<std::pair<const syntax::SyntaxNode*, const Symbol*> const> portDeclarations);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Port; }

    using Symbol::setParent;

private:
    mutable const Type* type = nullptr;
    mutable const Expression* initializer = nullptr;
    mutable const Expression* internalExpr = nullptr;
    const syntax::ExpressionSyntax* initializerSyntax = nullptr;
    SourceLocation initializerLoc;
};

/// Represents a multi-port, which is a port symbol that externally appears as
/// a single connection but internally connects to multiple names, potentially
/// with varying directions.
class SLANG_EXPORT MultiPortSymbol : public Symbol {
public:
    std::span<const PortSymbol* const> ports;

    /// The direction of data flowing across the various ports. This is the most
    /// restrictive aggregated direction out of all the ports. You need to check
    /// each individual port to know how the data actually flows.
    ArgumentDirection direction;

    /// Always set to false on multi-ports; included for parity for PortSymbols
    /// so that generic code can work on both types.
    bool isNullPort = false;

    MultiPortSymbol(std::string_view name, SourceLocation loc,
                    std::span<const PortSymbol* const> ports, ArgumentDirection direction);

    const Type& getType() const;

    /// Placeholder functions to enable generic code. Multi-ports never have initializers.
    bool hasInitializer() const { return false; }
    const Expression* getInitializer() const { return nullptr; }

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::MultiPort; }

private:
    mutable const Type* type = nullptr;
};

/// Represents the public-facing side of a module / program / interface port
/// that is also a connection to an interface instance (optionally with a modport restriction).
class SLANG_EXPORT InterfacePortSymbol : public Symbol {
public:
    using IfaceConn = std::pair<const Symbol*, const ModportSymbol*>;

    /// A pointer to the definition for the interface.
    const DefinitionSymbol* interfaceDef = nullptr;

    /// If non-empty, the name of the modport that restricts which interface signals are accessible.
    std::string_view modport;

    /// Set to true if this is a generic interface port, which allows connections
    /// to any interface type. If true, @a interfaceDef will be nullptr.
    bool isGeneric = false;

    InterfacePortSymbol(std::string_view name, SourceLocation loc) :
        Symbol(SymbolKind::InterfacePort, name, loc) {}

    bool isInvalid() const { return !interfaceDef && !isGeneric; }

    /// Gets the set of dimensions for specifying interface arrays.
    /// Returns nullopt if an error occurs evaluating the dimensions.
    std::optional<std::span<const ConstantRange>> getDeclaredRange() const;

    /// Gets the interface instance that this port connects to.
    IfaceConn getConnection() const;

    const ModportSymbol* getModport(const ASTContext& context, const InstanceSymbol& instance,
                                    syntax::DeferredSourceRange sourceRange) const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InterfacePort; }

private:
    mutable std::optional<std::span<const ConstantRange>> range;
};

class SLANG_EXPORT PortConnection {
public:
    using IfaceConn = InterfacePortSymbol::IfaceConn;

    const Symbol& port;

    PortConnection(const Symbol& port);
    PortConnection(const Symbol& port, const syntax::ExpressionSyntax& expr);
    PortConnection(const Symbol& port, bool useDefault);
    PortConnection(const InterfacePortSymbol& port, const Symbol* connectedSymbol,
                   const ModportSymbol* modport);
    PortConnection(const Symbol& port, const Symbol* connectedSymbol,
                   SourceRange implicitNameRange);

    IfaceConn getIfaceConn() const;
    const Expression* getExpression() const;
    void checkSimulatedNetTypes() const;

    void serializeTo(ASTSerializer& serializer) const;

    struct ConnMap {
        using NamedConnMap = SmallMap<std::string_view,
                                      std::pair<const syntax::NamedPortConnectionSyntax*, bool>, 8>;

        SmallVector<const syntax::PortConnectionSyntax*> orderedConns;
        NamedConnMap namedConns;
        std::span<const AttributeSymbol* const> wildcardAttrs;
        SourceRange wildcardRange;
        bool usingOrdered = true;
        bool hasWildcard = false;

        ConnMap(const syntax::SeparatedSyntaxList<syntax::PortConnectionSyntax>& portConnections,
                const Scope& scope, LookupLocation lookupLocation);
    };

    static void makeConnections(
        const InstanceSymbol& instance, std::span<const Symbol* const> ports,
        const syntax::SeparatedSyntaxList<syntax::PortConnectionSyntax>& portConnections,
        SmallVector<const PortConnection*>& results);

private:
    const InstanceSymbol& getParentInstance() const;

    const Symbol* connectedSymbol = nullptr;
    union {
        mutable const Expression* expr = nullptr;
        const ModportSymbol* modport;
    };
    union {
        const syntax::ExpressionSyntax* exprSyntax = nullptr;
        SourceRange implicitNameRange;
    };
    bool useDefault = false;
    bool isImplicit = false;
};

} // namespace slang::ast
