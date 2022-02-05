//------------------------------------------------------------------------------
//! @file PortSymbols.h
//! @brief Contains port-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"
#include "slang/numeric/ConstantValue.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/ValueSymbol.h"

namespace slang {

class AttributeSymbol;
class Definition;
class InstanceBodySymbol;
class InstanceSymbol;
class InstanceCacheKey;

struct ImplicitTypeSyntax;
struct PortDeclarationSyntax;
struct PortListSyntax;

/// Represents the public-facing side of a module / program / interface port.
/// The port symbol itself is not directly referenceable from within the instance;
/// it can however connect directly to a symbol that is.
class PortSymbol : public ValueSymbol {
public:
    /// The direction of data flowing across the port.
    ArgumentDirection direction = ArgumentDirection::InOut;

    /// An instance-internal symbol that this port connects to, if any.
    /// Ports that do not connect directly to an internal symbol will have
    /// this set to nullptr.
    const Symbol* internalSymbol = nullptr;

    /// An optional default value that is used for the port when no connection is provided.
    const Expression* defaultValue = nullptr;

    /// The source location where the external name for the port is declared.
    SourceLocation externalLoc;

    PortSymbol(string_view name, SourceLocation loc,
               bitmask<DeclaredTypeFlags> flags = DeclaredTypeFlags::None);

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(
        const PortListSyntax& syntax, const Scope& scope, SmallVector<const Symbol*>& results,
        SmallVector<std::pair<Symbol*, const Symbol*>>& implicitMembers,
        span<std::pair<const PortDeclarationSyntax*, const Symbol*> const> portDeclarations);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Port; }

    using ValueSymbol::setParent;
};

/// Represents a multi-port, which is a port symbol that externally appears as
/// a single connection but internally connects to multiple names, potentially
/// with varying directions.
class MultiPortSymbol : public Symbol {
public:
    span<const PortSymbol* const> ports;

    /// The direction of data flowing across the various ports. This is the most
    /// restrictive aggregated direction out of all the ports. You need to check
    /// each individual port to know how the data actually flows.
    ArgumentDirection direction;

    MultiPortSymbol(string_view name, SourceLocation loc, span<const PortSymbol* const> ports,
                    ArgumentDirection direction);

    const Type& getType() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::MultiPort; }

    /// A placeholder value to make templating between PortSymbol and MultiPortSymbol easier.
    static inline const Expression* const defaultValue = nullptr;

private:
    mutable const Type* type = nullptr;
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

    /// Set to true if this was declared as a non-ansi port and no
    /// I/O declaration was ever found for it.
    bool isMissingIO = false;

    /// The source location of the port name, if this port was declared
    /// inside of a multi-port concatenation expression. This is only set
    /// if isMissingIO is also set to true; it indicates an error should be
    /// reported when the I/O declaration is finally found.
    SourceLocation multiPortLoc;

    /// Gets the interface instance that this port connects to.
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
        const Symbol* port;
        const InterfacePortSymbol* ifacePort;
    };

    union {
        const Expression* expr;
        const Symbol* ifaceInstance;
    };

    bool isInterfacePort;
    span<const AttributeSymbol* const> attributes;

    PortConnection(const Symbol& port, const Expression* expr,
                   span<const AttributeSymbol* const> attributes);
    PortConnection(const InterfacePortSymbol& port, const Symbol* instance,
                   span<const AttributeSymbol* const> attributes);

    static void makeConnections(const InstanceSymbol& instance, span<const Symbol* const> ports,
                                const SeparatedSyntaxList<PortConnectionSyntax>& portConnections,
                                PointerMap& results);

    void serializeTo(ASTSerializer& serializer) const;
};

} // namespace slang
