//------------------------------------------------------------------------------
//! @file PortSymbols.h
//! @brief Contains port-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/ConstantValue.h"
#include "slang/binding/Expression.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/Symbol.h"

namespace slang {

class AttributeSymbol;
class Definition;
class InstanceBodySymbol;

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

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(
        const PortListSyntax& syntax, const Scope& scope, SmallVector<Symbol*>& results,
        SmallVector<std::pair<Symbol*, const Symbol*>>& implicitMembers,
        span<std::pair<const PortDeclarationSyntax*, const Symbol*> const> portDeclarations);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Port; }
};

/// Represents the public-facing side of a module / program / interface port
/// that is also a connection to an interface instance (optionally with a modport restriction).
class InterfacePortSymbol : public Symbol {
public:
    /// A pointer to the definition for the interface.
    const Definition* interfaceDef = nullptr;

    /// If non-empty, the name of the modport that restricts which interface signals are accessible.
    string_view modport;

    /// Gets the set of dimensions for specifying interface arrays.
    /// Returns nullopt if an error occurs evaluating the dimensions.
    optional<span<const ConstantRange>> getDeclaredRange() const;

    /// Gets the interface instance that this port connects to. Note that there may be
    /// more than one actual instance that has connected this port; this will return
    /// only the first such connection.
    const Symbol* getConnection() const;

    InterfacePortSymbol(string_view name, SourceLocation loc) :
        Symbol(SymbolKind::InterfacePort, name, loc) {}

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::InterfacePort; }

private:
    mutable optional<span<const ConstantRange>> range;
};

class PortConnection {
public:
    union {
        const PortSymbol* port;
        const InterfacePortSymbol* ifacePort;
    };

    union {
        const Expression* expr;
        const Symbol* ifaceInstance;
    };

    bool isInterfacePort;
    span<const AttributeSymbol* const> attributes;

    PortConnection(const PortSymbol& port, const Expression* expr,
                   span<const AttributeSymbol* const> attributes);
    PortConnection(const InterfacePortSymbol& port, const Symbol* instance,
                   span<const AttributeSymbol* const> attributes);

    static void makeConnections(const InstanceSymbol& instance, span<const Symbol* const> ports,
                                const SeparatedSyntaxList<PortConnectionSyntax>& portConnections,
                                PointerMap& results);
};

} // namespace slang