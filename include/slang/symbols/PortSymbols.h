//------------------------------------------------------------------------------
//! @file PortSymbols.h
//! @brief Contains port-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/ConstantValue.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/Symbol.h"

namespace slang {

class AttributeSymbol;
class DefinitionSymbol;
class ModportSymbol;

struct PortConnectionSyntax;
struct PortDeclarationSyntax;
struct PortListSyntax;

/// Represents the public-facing side of a module / program / interface port.
/// The port symbol itself is not directly referenceable from within the instance;
/// it can however connect directly to a symbol that is.
class PortSymbol : public ValueSymbol {
public:
    /// The direction of data flowing across the port.
    PortDirection direction = PortDirection::InOut;

    /// An instance-internal symbol that this port connects to, if any.
    /// Ports that do not connect directly to an internal symbol will have
    /// this set to nullptr.
    const Symbol* internalSymbol = nullptr;

    /// An optional default value that is used for the port when no connection is provided.
    const Expression* defaultValue = nullptr;

    PortSymbol(string_view name, SourceLocation loc,
               bitmask<DeclaredTypeFlags> flags = DeclaredTypeFlags::None);

    /// If the port is connected during instantiation, gets the expression that
    /// indicates how it connects to the outside world. Otherwise returns nullptr.
    const Expression* getConnection() const;

    void setConnection(const Expression* expr, span<const AttributeSymbol* const> attributes);
    void setConnection(const ExpressionSyntax& syntax,
                       span<const AttributeSymbol* const> attributes);

    span<const AttributeSymbol* const> getConnectionAttributes() const { return connAttrs; }

    void toJson(json& j) const;
    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(
        const PortListSyntax& syntax, const Scope& scope, SmallVector<Symbol*>& results,
        SmallVector<std::pair<Symbol*, const Symbol*>>& implicitMembers,
        span<std::pair<const PortDeclarationSyntax*, const Symbol*> const> portDeclarations);

    static void makeConnections(const Scope& scope, span<Symbol* const> ports,
                                const SeparatedSyntaxList<PortConnectionSyntax>& portConnections);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Port; }

private:
    mutable optional<const Expression*> conn;
    const ExpressionSyntax* connSyntax = nullptr;
    span<const AttributeSymbol* const> connAttrs;
};

/// Represents the public-facing side of a module / program / interface port
/// that is also a connection to an interface instance (optionally with a modport restriction).
class InterfacePortSymbol : public Symbol {
public:
    /// A pointer to the definition for the interface.
    const DefinitionSymbol* interfaceDef = nullptr;

    /// A pointer to an optional modport that restricts which interface signals are accessible.
    const ModportSymbol* modport = nullptr;

    /// If the port is connected during instantiation, this is the external instance to which it
    /// connects.
    const Symbol* connection = nullptr;

    /// Attributes attached to the connection, if any.
    span<const AttributeSymbol* const> connectionAttributes;

    /// Gets the set of dimensions for specifying interface arrays.
    /// Returns nullopt if an error occurs evaluating the dimensions.
    optional<span<const ConstantRange>> getDeclaredRange() const;

    InterfacePortSymbol(string_view name, SourceLocation loc) :
        Symbol(SymbolKind::InterfacePort, name, loc) {}

    void toJson(json& j) const;
    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InterfacePort; }

private:
    mutable optional<span<const ConstantRange>> range;
};

} // namespace slang