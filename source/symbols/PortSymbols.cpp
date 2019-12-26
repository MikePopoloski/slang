//------------------------------------------------------------------------------
// PortSymbols.cpp
// Contains port-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/PortSymbols.h"

#include <nlohmann/json.hpp>

#include "slang/binding/MiscExpressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/symbols/AllTypes.h"
#include "slang/symbols/AttributeSymbol.h"
#include "slang/symbols/DefinitionSymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/StackContainer.h"

namespace slang {

namespace {

const NetType& getDefaultNetType(const Scope& scope, SourceLocation location) {
    auto& netType = scope.getDefaultNetType();
    if (!netType.isError())
        return netType;

    scope.addDiag(diag::ImplicitNetPortNoDefault, location);
    return scope.getCompilation().getWireNetType();
}

// Helper class to build up lists of port symbols.
class AnsiPortListBuilder {
public:
    AnsiPortListBuilder(const Scope& scope,
                        SmallVector<std::pair<Symbol*, const Symbol*>>& implicitMembers) :
        compilation(scope.getCompilation()),
        scope(scope), implicitMembers(implicitMembers) {}

    Symbol* createPort(const ImplicitAnsiPortSyntax& syntax) {
        // Helper function to check if an implicit type syntax is totally empty.
        auto typeSyntaxEmpty = [](const DataTypeSyntax& typeSyntax) {
            if (typeSyntax.kind != SyntaxKind::ImplicitType)
                return false;

            const auto& implicitType = typeSyntax.as<ImplicitTypeSyntax>();
            return !implicitType.signing && implicitType.dimensions.empty();
        };

        auto& decl = *syntax.declarator;
        switch (syntax.header->kind) {
            case SyntaxKind::VariablePortHeader: {
                // A VariablePortHeader is parsed as a catch-all when we aren't sure what kind of
                // port this is. There are three components to a port that matter: kind, type,
                // direction. If all three are omitted, inherit them all from the previous port.
                // We'll never even get into this code path if the very first port omitted all three
                // because then it would be a non-ansi port list.
                auto& header = syntax.header->as<VariablePortHeaderSyntax>();
                if (!header.direction && !header.varKeyword && typeSyntaxEmpty(*header.dataType))
                    return addInherited(decl, syntax.attributes);

                // It's possible that this is actually an interface port if the data type is just an
                // identifier. The only way to know is to do a lookup and see what comes back.
                const DefinitionSymbol* definition = nullptr;
                string_view simpleName = getSimpleTypeName(*header.dataType);
                if (!simpleName.empty()) {
                    auto found = scope.lookupUnqualifiedName(simpleName, LookupFlags::Type);

                    // If we didn't find a valid type, try to find a definition.
                    if (!found || !found->isType())
                        definition = compilation.getDefinition(simpleName, scope);
                }

                if (definition) {
                    if (definition->definitionKind != DefinitionKind::Interface) {
                        auto& diag = scope.addDiag(diag::PortTypeNotInterfaceOrData,
                                                   header.dataType->sourceRange());
                        diag << definition->name;
                        diag.addNote(diag::NoteDeclarationHere, definition->location);
                        definition = nullptr;
                    }
                    else {
                        if (header.varKeyword) {
                            scope.addDiag(diag::VarWithInterfacePort, header.varKeyword.location());
                        }

                        if (header.direction) {
                            scope.addDiag(diag::DirectionWithInterfacePort,
                                          header.direction.location());
                        }
                    }

                    return add(decl, definition, nullptr, syntax.attributes);
                }

                // Rules from [23.2.2.3]:
                // - If we have a var keyword, it's a var
                // - For input and inout, default to a net
                // - For output, if we have a data type it's a var, otherwise net
                // - For ref it's always a var
                PortDirection direction = getDirection(header.direction);
                const NetType* netType = nullptr;
                if (!header.varKeyword &&
                    (direction == PortDirection::In || direction == PortDirection::InOut ||
                     (direction == PortDirection::Out &&
                      header.dataType->kind == SyntaxKind::ImplicitType))) {

                    netType = &getDefaultNetType(scope, decl.name.location());
                }

                // TODO: user-defined nettypes
                return add(decl, direction, *header.dataType, netType, syntax.attributes);
            }
            case SyntaxKind::NetPortHeader: {
                auto& header = syntax.header->as<NetPortHeaderSyntax>();
                return add(decl, getDirection(header.direction), *header.dataType,
                           &compilation.getNetType(header.netType.kind), syntax.attributes);
            }
            case SyntaxKind::InterfacePortHeader: {
                // TODO: handle generic interface header
                auto& header = syntax.header->as<InterfacePortHeaderSyntax>();
                auto token = header.nameOrKeyword;
                auto definition = compilation.getDefinition(token.valueText(), scope);
                const ModportSymbol* modport = nullptr;

                if (!definition) {
                    scope.addDiag(diag::UnknownInterface, token.range()) << token.valueText();
                }
                else if (definition->definitionKind != DefinitionKind::Interface) {
                    auto& diag = scope.addDiag(diag::PortTypeNotInterfaceOrData,
                                               header.nameOrKeyword.range());
                    diag << definition->name;
                    diag.addNote(diag::NoteDeclarationHere, definition->location);
                    definition = nullptr;
                }
                else if (header.modport) {
                    auto member = header.modport->member;
                    modport =
                        definition->getModportOrError(member.valueText(), scope, member.range());
                }

                return add(decl, definition, modport, syntax.attributes);
            }
            case SyntaxKind::InterconnectPortHeader:
                scope.addDiag(diag::NotYetSupported, syntax.header->sourceRange());
                return addInherited(decl, syntax.attributes);
            default:
                THROW_UNREACHABLE;
        }
    }

    Symbol* createPort(const ExplicitAnsiPortSyntax& syntax) {
        auto port = compilation.emplace<PortSymbol>(syntax.name.valueText(), syntax.name.location(),
                                                    DeclaredTypeFlags::LookupMax |
                                                        DeclaredTypeFlags::InferImplicit);
        port->direction = getDirection(syntax.direction);
        port->setSyntax(syntax);
        port->setDeclaredType(UnsetType);
        port->setAttributes(scope, syntax.attributes);

        if (syntax.expr)
            port->setInitializerSyntax(*syntax.expr, syntax.expr->getFirstToken().location());

        lastDirection = port->direction;
        lastType = &UnsetType;
        lastNetType = nullptr;
        lastInterface = nullptr;

        return port;
    }

private:
    PortDirection getDirection(Token token) const {
        return token ? SemanticFacts::getPortDirection(token.kind) : lastDirection;
    }

    Symbol* addInherited(const DeclaratorSyntax& decl,
                         span<const AttributeInstanceSyntax* const> attrs) {
        if (lastInterface) {
            // TODO: inherit modport
            return add(decl, lastInterface, nullptr, attrs);
        }

        return add(decl, lastDirection, *lastType, lastNetType, attrs);
    }

    Symbol* add(const DeclaratorSyntax& decl, PortDirection direction, const DataTypeSyntax& type,
                const NetType* netType, span<const AttributeInstanceSyntax* const> attrs) {

        auto port = compilation.emplace<PortSymbol>(decl.name.valueText(), decl.name.location());
        port->direction = direction;
        port->setSyntax(decl);
        port->setDeclaredType(type, decl.dimensions);
        port->setAttributes(scope, attrs);

        if (port->direction == PortDirection::InOut && !netType)
            scope.addDiag(diag::InOutPortCannotBeVariable, port->location) << port->name;
        else if (port->direction == PortDirection::Ref && netType)
            scope.addDiag(diag::RefPortMustBeVariable, port->location) << port->name;

        // Create a new symbol to represent this port internally to the instance.
        ValueSymbol* symbol;
        if (netType) {
            symbol = compilation.emplace<NetSymbol>(port->name, port->location, *netType);
        }
        else {
            // TODO: variable lifetime
            auto variable = compilation.emplace<VariableSymbol>(port->name, port->location);
            symbol = variable;
        }

        // Initializers here are evaluated in the context of the port list and
        // must always be a constant value.
        // TODO: handle initializers
        symbol->setSyntax(decl);
        symbol->getDeclaredType()->copyTypeFrom(*port->getDeclaredType());
        symbol->setAttributes(scope, attrs);
        port->internalSymbol = symbol;
        implicitMembers.emplace(symbol, port);

        // Remember the properties of this port in case the next port wants to inherit from it.
        lastDirection = direction;
        lastType = &type;
        lastNetType = netType;
        lastInterface = nullptr;

        return port;
    }

    Symbol* add(const DeclaratorSyntax& decl, const DefinitionSymbol* iface,
                const ModportSymbol* modport, span<const AttributeInstanceSyntax* const> attrs) {
        auto port =
            compilation.emplace<InterfacePortSymbol>(decl.name.valueText(), decl.name.location());

        port->interfaceDef = iface;
        port->modport = modport;
        port->setSyntax(decl);
        port->setAttributes(scope, attrs);

        lastDirection = PortDirection::InOut;
        lastType = &UnsetType;
        lastNetType = nullptr;
        lastInterface = iface;

        return port;
    }

    Compilation& compilation;
    const Scope& scope;
    SmallVector<std::pair<Symbol*, const Symbol*>>& implicitMembers;

    PortDirection lastDirection = PortDirection::InOut;
    const DataTypeSyntax* lastType = &UnsetType;
    const NetType* lastNetType = nullptr;
    const DefinitionSymbol* lastInterface = nullptr;

    static const ImplicitTypeSyntax UnsetType;
};

const ImplicitTypeSyntax AnsiPortListBuilder::UnsetType{ Token(), nullptr };

class NonAnsiPortListBuilder {
public:
    NonAnsiPortListBuilder(
        const Scope& scope,
        span<std::pair<const PortDeclarationSyntax*, const Symbol*> const> portDeclarations,
        SmallVector<std::pair<Symbol*, const Symbol*>>& implicitMembers) :
        compilation(scope.getCompilation()),
        scope(scope), implicitMembers(implicitMembers) {

        // All port declarations in the scope have been collected; index them for easy lookup.
        for (auto [port, insertionPoint] : portDeclarations) {
            for (auto decl : port->declarators) {
                if (auto name = decl->name; !name.isMissing()) {
                    auto result =
                        portInfos.emplace(name.valueText(), PortInfo{ decl, port->attributes });

                    if (result.second) {
                        handleIODecl(*port->header, result.first->second, insertionPoint);
                    }
                    else {
                        auto& diag = scope.addDiag(diag::Redefinition, name.location());
                        diag << name.valueText();
                        diag.addNote(diag::NotePreviousDefinition,
                                     result.first->second.syntax->name.location());
                    }
                }
            }
        }
    }

    Symbol* createPort(const ImplicitNonAnsiPortSyntax& syntax) {
        // TODO: location for empty ports?
        auto port =
            compilation.emplace<PortSymbol>("", SourceLocation(), DeclaredTypeFlags::LookupMax);
        port->setSyntax(syntax);

        // Unnamed empty port is allowed.
        if (!syntax.expr)
            return port;

        switch (syntax.expr->kind) {
            case SyntaxKind::PortReference: {
                auto& ref = syntax.expr->as<PortReferenceSyntax>();
                port->name = ref.name.valueText();
                port->location = ref.name.location();

                auto info = getInfo(port->name, port->location);
                if (!info)
                    return port;

                // TODO: explicit connection expression

                ASSERT(info->internalSymbol);
                port->direction = info->direction;
                port->internalSymbol = info->internalSymbol;
                port->getDeclaredType()->copyTypeFrom(*info->internalSymbol->getDeclaredType());
                port->setAttributes(scope, info->attrs);
                return port;
            }
            case SyntaxKind::PortConcatenation:
                scope.addDiag(diag::NotYetSupported, syntax.sourceRange());
                return port;
            default:
                THROW_UNREACHABLE;
        }
    }

private:
    Compilation& compilation;
    const Scope& scope;
    SmallVector<std::pair<Symbol*, const Symbol*>>& implicitMembers;

    struct PortInfo {
        const DeclaratorSyntax* syntax = nullptr;
        span<const AttributeInstanceSyntax* const> attrs;
        const Symbol* internalSymbol = nullptr;
        PortDirection direction = PortDirection::In;
        bool used = false;

        PortInfo(const DeclaratorSyntax* syntax, span<const AttributeInstanceSyntax* const> attrs) :
            syntax(syntax), attrs(attrs) {}
    };
    SmallMap<string_view, PortInfo, 8> portInfos;

    const PortInfo* getInfo(string_view name, SourceLocation loc) {
        if (name.empty())
            return nullptr;

        auto it = portInfos.find(name);
        if (it == portInfos.end()) {
            scope.addDiag(diag::MissingPortIODeclaration, loc) << name;
            return nullptr;
        }

        // TODO: error at the end if a port I/O is unused
        it->second.used = true;
        return &it->second;
    }

    void handleIODecl(const PortHeaderSyntax& header, PortInfo& info,
                      const Symbol* insertionPoint) {
        auto& decl = *info.syntax;
        auto name = decl.name.valueText();
        auto declLoc = decl.name.location();

        switch (header.kind) {
            case SyntaxKind::VariablePortHeader: {
                auto& varHeader = header.as<VariablePortHeaderSyntax>();
                info.direction = SemanticFacts::getPortDirection(varHeader.direction.kind);

                // If the port has any kind of type declared, this constitutes a full symbol
                // definition. Otherwise we need to see if there's an existing symbol to match with.
                if (varHeader.varKeyword || varHeader.dataType->kind != SyntaxKind::ImplicitType) {
                    // TODO: check for user defined net type?
                    // TODO: variable lifetime
                    auto variable = compilation.emplace<VariableSymbol>(name, declLoc);
                    setInternalSymbol(*variable, decl, *varHeader.dataType, info, insertionPoint);
                }
                else if (auto symbol = scope.find(name);
                         symbol && (symbol->kind == SymbolKind::Variable ||
                                    symbol->kind == SymbolKind::Net)) {

                    // Port kind and type come from the matching symbol
                    info.internalSymbol = symbol;
                    mergePortTypes(symbol->as<ValueSymbol>(),
                                   varHeader.dataType->as<ImplicitTypeSyntax>(), declLoc, scope,
                                   decl.dimensions);
                }
                else {
                    // No symbol and no data type defaults to a basic net.
                    auto net = compilation.emplace<NetSymbol>(name, declLoc,
                                                              getDefaultNetType(scope, declLoc));
                    setInternalSymbol(*net, decl, *varHeader.dataType, info, insertionPoint);
                }

                if (info.direction == PortDirection::InOut &&
                    info.internalSymbol->kind != SymbolKind::Net) {
                    scope.addDiag(diag::InOutPortCannotBeVariable, declLoc) << name;
                }
                else if (info.direction == PortDirection::Ref &&
                         info.internalSymbol->kind == SymbolKind::Net) {
                    scope.addDiag(diag::RefPortMustBeVariable, declLoc) << name;
                }
                break;
            }
            case SyntaxKind::NetPortHeader: {
                auto& netHeader = header.as<NetPortHeaderSyntax>();
                info.direction = SemanticFacts::getPortDirection(netHeader.direction.kind);
                if (info.direction == PortDirection::Ref)
                    scope.addDiag(diag::RefPortMustBeVariable, declLoc) << name;

                // Create a new symbol to represent this port internally to the instance.
                auto net = compilation.emplace<NetSymbol>(
                    name, declLoc, compilation.getNetType(netHeader.netType.kind));
                setInternalSymbol(*net, decl, *netHeader.dataType, info, insertionPoint);
                break;
            }
            case SyntaxKind::InterconnectPortHeader:
            case SyntaxKind::InterfacePortHeader:
                scope.addDiag(diag::NotYetSupported, header.sourceRange());
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    void setInternalSymbol(ValueSymbol& symbol, const DeclaratorSyntax& decl,
                           const DataTypeSyntax& dataType, PortInfo& info,
                           const Symbol* insertionPoint) {
        symbol.setSyntax(decl);
        symbol.setDeclaredType(dataType, decl.dimensions);
        symbol.setAttributes(scope, info.attrs);
        implicitMembers.emplace(&symbol, insertionPoint);
        info.internalSymbol = &symbol;
    }

    static void mergePortTypes(const ValueSymbol& symbol, const ImplicitTypeSyntax& implicit,
                               SourceLocation location, const Scope& scope,
                               span<const VariableDimensionSyntax* const> unpackedDimensions) {
        // There's this really terrible "feature" where the port declaration can influence the type
        // of the actual symbol somewhere else in the tree. This is ugly but should be safe since
        // nobody else can look at that symbol's type until we've gone through elaboration.

        if (implicit.signing) {
            // Drill past any unpacked arrays to figure out if this thing is even integral.
            const Type* type = &symbol.getType();
            while (type->isUnpackedArray())
                type = &type->getCanonicalType().as<UnpackedArrayType>().elementType;

            if (!type->isIntegral()) {
                auto& diag = scope.addDiag(diag::CantDeclarePortSigned, location);
                diag << symbol.name << *type;
            }
            else if (implicit.signing.kind == TokenKind::SignedKeyword && !type->isSigned()) {
                // Yeah, this is ugly.
                const_cast<DeclaredType&>(*symbol.getDeclaredType()).setForceSigned();

                // Verify that the sign flag had an effect; it's not always possible to force it.
                type = &symbol.getType();
                while (type->isUnpackedArray())
                    type = &type->getCanonicalType().as<UnpackedArrayType>().elementType;

                if (!type->isSigned()) {
                    // TODO: error
                }
            }
        }

        if (!implicit.dimensions.empty() || !unpackedDimensions.empty()) {
            // TODO: check dimensions
        }
    }
};

class PortConnectionBuilder {
public:
    PortConnectionBuilder(const Scope& childScope, const Scope& instanceScope,
                          const SeparatedSyntaxList<PortConnectionSyntax>& portConnections) :
        scope(instanceScope),
        instance(childScope.asSymbol().as<InstanceSymbol>()) {

        // This needs to be a lookup for the instance's parent in the hierarchy, not its lexical
        // location. Usually all lookups want the lexical location, so we have to specifically ask
        // for the parent here.
        lookupLocation = LookupLocation(instance.getParentScope(), (uint32_t)instance.getIndex());

        bool hasConnections = false;
        for (auto conn : portConnections) {
            bool isOrdered = conn->kind == SyntaxKind::OrderedPortConnection;
            if (!hasConnections) {
                hasConnections = true;
                usingOrdered = isOrdered;
            }
            else if (isOrdered != usingOrdered) {
                scope.addDiag(diag::MixingOrderedAndNamedPorts, conn->getFirstToken().location());
                break;
            }

            if (isOrdered) {
                orderedConns.append(&conn->as<OrderedPortConnectionSyntax>());
            }
            else if (conn->kind == SyntaxKind::WildcardPortConnection) {
                if (!std::exchange(hasWildcard, true)) {
                    wildcardRange = conn->sourceRange();
                    wildcardAttrs =
                        AttributeSymbol::fromSyntax(conn->attributes, scope, lookupLocation);
                }
                else {
                    auto& diag =
                        scope.addDiag(diag::DuplicateWildcardPortConnection, conn->sourceRange());
                    diag.addNote(diag::NotePreviousUsage, wildcardRange.start());
                }
            }
            else {
                auto& npc = conn->as<NamedPortConnectionSyntax>();
                auto name = npc.name.valueText();
                if (!name.empty()) {
                    auto pair = namedConns.emplace(name, std::make_pair(&npc, false));
                    if (!pair.second) {
                        auto& diag =
                            scope.addDiag(diag::DuplicatePortConnection, npc.name.location());
                        diag << name;
                        diag.addNote(diag::NotePreviousUsage,
                                     pair.first->second.first->name.location());
                    }
                }
            }
        }

        // Build up the set of dimensions for the instantiating instance's array parent, if any.
        // This builds up the dimensions in reverse order, so we have to reverse them back.
        auto parent = instance.getParentScope();
        while (parent && parent->asSymbol().kind == SymbolKind::InstanceArray) {
            auto& sym = parent->asSymbol().as<InstanceArraySymbol>();
            instanceDims.append(sym.range);
            parent = sym.getParentScope();
        }
        std::reverse(instanceDims.begin(), instanceDims.end());
    }

    void setConnection(PortSymbol& port) {
        if (usingOrdered) {
            if (orderedIndex >= orderedConns.size()) {
                orderedIndex++;
                if (port.defaultValue)
                    port.setConnection(port.defaultValue, {});
                else if (port.name.empty()) {
                    if (!warnedAboutUnnamed) {
                        auto& diag = scope.addDiag(diag::UnconnectedUnnamedPort, instance.location);
                        diag.addNote(diag::NoteDeclarationHere, port.location);
                        warnedAboutUnnamed = true;
                    }
                }
                else {
                    scope.addDiag(diag::UnconnectedNamedPort, instance.location) << port.name;
                }

                return;
            }

            const OrderedPortConnectionSyntax& opc = *orderedConns[orderedIndex++];
            auto attrs = AttributeSymbol::fromSyntax(opc.attributes, scope, lookupLocation);
            if (opc.expr)
                port.setConnection(*opc.expr, attrs);
            else
                port.setConnection(port.defaultValue, attrs);

            return;
        }

        if (port.name.empty()) {
            // port is unnamed so can never be connected by name
            if (!warnedAboutUnnamed) {
                auto& diag = scope.addDiag(diag::UnconnectedUnnamedPort, instance.location);
                diag.addNote(diag::NoteDeclarationHere, port.location);
                warnedAboutUnnamed = true;
            }
            return;
        }

        auto it = namedConns.find(port.name);
        if (it == namedConns.end()) {
            if (hasWildcard) {
                implicitNamedPort(port, wildcardAttrs, wildcardRange, true);
                return;
            }

            if (port.defaultValue)
                port.setConnection(port.defaultValue, {});
            else
                scope.addDiag(diag::UnconnectedNamedPort, instance.location) << port.name;
            return;
        }

        // We have a named connection; there are two possibilities here:
        // - An explicit connection (with an optional expression)
        // - An implicit connection, where we have to look up the name ourselves
        const NamedPortConnectionSyntax& conn = *it->second.first;
        it->second.second = true;

        auto attrs = AttributeSymbol::fromSyntax(conn.attributes, scope, lookupLocation);
        if (conn.openParen) {
            // For explicit named port connections, having an empty expression means no connection,
            // so we never take the default value here.
            if (conn.expr)
                port.setConnection(*conn.expr, attrs);

            return;
        }

        implicitNamedPort(port, attrs, conn.name.range(), false);
    }

    void setConnection(InterfacePortSymbol& port) {
        // TODO: verify that interface ports must always have a name
        ASSERT(!port.name.empty());

        auto reportUnconnected = [&]() {
            auto& diag = scope.addDiag(diag::InterfacePortNotConnected, instance.location);
            diag << port.name;
            diag.addNote(diag::NoteDeclarationHere, port.location);
        };

        if (usingOrdered) {
            const ExpressionSyntax* expr = nullptr;
            if (orderedIndex < orderedConns.size()) {
                const OrderedPortConnectionSyntax& opc = *orderedConns[orderedIndex];
                expr = opc.expr;
                port.connectionAttributes =
                    AttributeSymbol::fromSyntax(opc.attributes, scope, lookupLocation);
            }

            orderedIndex++;
            if (!expr) {
                reportUnconnected();
                return;
            }

            setInterfaceExpr(port, *expr);
            return;
        }

        auto it = namedConns.find(port.name);
        if (it == namedConns.end()) {
            port.connectionAttributes = wildcardAttrs;
            if (hasWildcard)
                setImplicitInterface(port, wildcardRange);
            else
                reportUnconnected();
            return;
        }

        // We have a named connection; there are two possibilities here:
        // - An explicit connection (with an optional expression)
        // - An implicit connection, where we have to look up the name ourselves
        const NamedPortConnectionSyntax& conn = *it->second.first;
        it->second.second = true;

        port.connectionAttributes =
            AttributeSymbol::fromSyntax(conn.attributes, scope, lookupLocation);

        if (conn.openParen) {
            // For explicit named port connections, having an empty expression means no connection.
            if (!conn.expr)
                reportUnconnected();
            else
                setInterfaceExpr(port, *conn.expr);
            return;
        }

        setImplicitInterface(port, conn.name.range());
    }

    void finalize() {
        if (usingOrdered) {
            if (orderedIndex < orderedConns.size()) {
                auto loc = orderedConns[orderedIndex]->getFirstToken().location();
                auto& diag = scope.addDiag(diag::TooManyPortConnections, loc);
                diag << instance.name;
                diag << orderedConns.size();
                diag << orderedIndex;
            }
        }
        else {
            for (auto& pair : namedConns) {
                // We marked all the connections that we used, so anything left over is a connection
                // for a non-existent port.
                if (!pair.second.second) {
                    auto& diag =
                        scope.addDiag(diag::PortDoesNotExist, pair.second.first->name.location());
                    diag << pair.second.first->name.valueText();
                    diag << instance.name;
                }
            }
        }
    }

private:
    void implicitNamedPort(PortSymbol& port, span<const AttributeSymbol* const> attributes,
                           SourceRange range, bool isWildcard) {
        // An implicit named port connection is semantically equivalent to `.port(port)` except:
        // - Can't create implicit net declarations this way
        // - Port types need to be equivalent, not just assignment compatible
        // - An implicit connection between nets of two dissimilar net types shall issue an
        //   error when it is a warning in an explicit named port connection

        LookupFlags flags = isWildcard ? LookupFlags::DisallowWildcardImport : LookupFlags::None;
        auto symbol = scope.lookupUnqualifiedName(port.name, flags);
        if (!symbol) {
            // If this is a wildcard connection, we're allowed to use the port's default value,
            // if it has one.
            if (isWildcard && port.defaultValue)
                port.setConnection(port.defaultValue, attributes);
            else
                scope.addDiag(diag::ImplicitNamedPortNotFound, range) << port.name;
            return;
        }

        if (!symbol->isDeclaredBefore(lookupLocation).value_or(true)) {
            auto& diag = scope.addDiag(diag::UsedBeforeDeclared, range);
            diag << port.name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
        }

        auto& portType = port.getType();
        if (portType.isError())
            return;

        auto expr = &NamedValueExpression::fromSymbol(scope, *symbol, false, range);
        if (expr->bad())
            return;

        if (!expr->type->isEquivalent(portType)) {
            auto& diag = scope.addDiag(diag::ImplicitNamedPortTypeMismatch, range);
            diag << port.name;
            diag << portType;
            diag << *expr->type;
            return;
        }

        // TODO: direction of assignment
        auto& assign = Expression::convertAssignment(BindContext(scope, LookupLocation::max),
                                                     portType, *expr, range.start());
        port.setConnection(&assign, attributes);
    }

    void setInterfaceExpr(InterfacePortSymbol& port, const ExpressionSyntax& syntax) {
        const ExpressionSyntax* expr = &syntax;
        while (expr->kind == SyntaxKind::ParenthesizedExpression)
            expr = expr->as<ParenthesizedExpressionSyntax>().expression;

        if (!NameSyntax::isKind(expr->kind)) {
            scope.addDiag(diag::InterfacePortInvalidExpression, expr->sourceRange()) << port.name;
            return;
        }

        LookupResult result;
        scope.lookupName(expr->as<NameSyntax>(), lookupLocation, LookupFlags::None, result);
        if (result.hasError())
            scope.getCompilation().addDiagnostics(result.getDiagnostics());

        // If we found the interface but it's actually a port, unwrap to the target connection.
        const Symbol* symbol = result.found;
        if (symbol && symbol->kind == SymbolKind::InterfacePort) {
            symbol = symbol->as<InterfacePortSymbol>().connection;
            if (symbol && !result.selectors.empty()) {
                SmallVectorSized<const ElementSelectSyntax*, 4> selectors;
                for (auto& sel : result.selectors)
                    selectors.append(std::get<0>(sel));

                symbol = Scope::selectChild(*symbol, selectors, BindContext(scope, lookupLocation),
                                            result);
            }
        }

        if (!symbol)
            return;

        setInterface(port, symbol, expr->sourceRange());
    }

    void setImplicitInterface(InterfacePortSymbol& port, SourceRange range) {
        auto symbol = scope.lookupUnqualifiedName(port.name);
        if (!symbol) {
            scope.addDiag(diag::ImplicitNamedPortNotFound, range) << port.name;
            return;
        }

        if (!symbol->isDeclaredBefore(lookupLocation).value_or(true)) {
            auto& diag = scope.addDiag(diag::UsedBeforeDeclared, range);
            diag << port.name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
        }

        setInterface(port, symbol, range);
    }

    static bool areDimSizesEqual(span<const ConstantRange> left, span<const ConstantRange> right) {
        if (left.size() != right.size())
            return false;

        for (size_t i = 0; i < left.size(); i++) {
            if (left[i].width() != right[i].width())
                return false;
        }

        return true;
    }

    void setInterface(InterfacePortSymbol& port, const Symbol* symbol, SourceRange range) {
        if (!port.interfaceDef)
            return;

        // If the symbol is another port, unwrap it now.
        if (symbol->kind == SymbolKind::InterfacePort) {
            symbol = symbol->as<InterfacePortSymbol>().connection;
            if (!symbol)
                return;
        }

        // Make sure the thing we're connecting to is an interface or array of interfaces.
        SmallVectorSized<ConstantRange, 4> dims;
        const Symbol* child = symbol;
        while (child->kind == SymbolKind::InstanceArray) {
            auto& array = child->as<InstanceArraySymbol>();
            if (array.elements.empty())
                return;

            dims.append(array.range);
            child = array.elements[0];
        }

        // TODO: handle interface/modport ports as well
        if (child->kind != SymbolKind::InterfaceInstance) {
            scope.addDiag(diag::NotAnInterface, range) << symbol->name;
            return;
        }

        auto connDef = &child->as<InterfaceInstanceSymbol>().definition;
        if (connDef != port.interfaceDef) {
            // TODO: print the potentially nested name path instead of the simple name
            auto& diag = scope.addDiag(diag::InterfacePortTypeMismatch, range);
            diag << connDef->name << port.interfaceDef->name;
            diag.addNote(diag::NoteDeclarationHere, port.location);
            return;
        }

        // If the dimensions match exactly what the port is expecting make the connection.
        auto portDims = port.getDeclaredRange();
        if (areDimSizesEqual(portDims, dims)) {
            port.connection = symbol;
            return;
        }

        // Otherwise, if the instance being instantiated is part of an array of instances *and*
        // the symbol we're connecting to is an array of interfaces, we need to check to see whether
        // to slice up that array among all the instances. We do the slicing operation if:
        // instance array dimensions + port dimensions == connection dimensions
        span<const ConstantRange> dimSpan = dims;
        if (dimSpan.size() >= instanceDims.size() &&
            areDimSizesEqual(dimSpan.subspan(0, instanceDims.size()), instanceDims) &&
            areDimSizesEqual(dimSpan.subspan(instanceDims.size()), portDims)) {

            // It's ok to do the slicing, so pick the correct slice for the connection
            // based on the actual path of the instance we're elaborating.
            for (size_t i = 0; i < instance.arrayPath.size(); i++) {
                auto& array = symbol->as<InstanceArraySymbol>();
                int32_t index = instanceDims[i].translateIndex(instance.arrayPath[i]);
                if (!array.range.isLittleEndian())
                    index = array.range.upper() - index;

                symbol = array.elements[size_t(index)];
            }

            port.connection = symbol;
            return;
        }

        auto& diag = scope.addDiag(diag::PortConnDimensionsMismatch, range);
        diag.addNote(diag::NoteDeclarationHere, port.location);
    }

    const Scope& scope;
    const InstanceSymbol& instance;
    SmallVectorSized<ConstantRange, 4> instanceDims;
    SmallVectorSized<const OrderedPortConnectionSyntax*, 8> orderedConns;
    SmallMap<string_view, std::pair<const NamedPortConnectionSyntax*, bool>, 8> namedConns;
    span<const AttributeSymbol* const> wildcardAttrs;
    LookupLocation lookupLocation;
    SourceRange wildcardRange;
    size_t orderedIndex = 0;
    bool usingOrdered = true;
    bool hasWildcard = false;
    bool warnedAboutUnnamed = false;
};

} // end anonymous namespace

PortSymbol::PortSymbol(string_view name, SourceLocation loc, bitmask<DeclaredTypeFlags> flags) :
    ValueSymbol(SymbolKind::Port, name, loc, flags) {
}

const Expression* PortSymbol::getConnection() const {
    if (!conn) {
        if (!connSyntax)
            conn = nullptr;
        else {
            BindContext context(*getParentScope(), LookupLocation::before(*this));
            auto loc = connSyntax->getFirstToken().location();

            switch (direction) {
                case PortDirection::In:
                    conn = &Expression::bind(getType(), *connSyntax, loc, context);
                    break;
                case PortDirection::Out:
                    // TODO: require assignable
                    // TODO: assignment-like context
                    conn = &Expression::bind(*connSyntax, context);
                    context.requireLValue(*conn.value(), loc);
                    break;
                case PortDirection::InOut:
                    // TODO: require assignable
                    // TODO: check not variable
                    conn = &Expression::bind(*connSyntax, context);
                    context.requireLValue(*conn.value(), loc);
                    break;
                case PortDirection::Ref:
                    // TODO: implement this
                    conn = nullptr;
                    break;
            }

            // TODO: if port is explicit, check that expression as well
        }
    }
    return *conn;
}

void PortSymbol::setConnection(const Expression* expr,
                               span<const AttributeSymbol* const> attributes) {
    conn = expr;
    connSyntax = nullptr;
    connAttrs = attributes;
}

void PortSymbol::setConnection(const ExpressionSyntax& syntax,
                               span<const AttributeSymbol* const> attributes) {
    conn = nullptr;
    connSyntax = &syntax;
    connAttrs = attributes;
}

void PortSymbol::fromSyntax(
    const PortListSyntax& syntax, const Scope& scope, SmallVector<Symbol*>& results,
    SmallVector<std::pair<Symbol*, const Symbol*>>& implicitMembers,
    span<std::pair<const PortDeclarationSyntax*, const Symbol*> const> portDeclarations) {

    switch (syntax.kind) {
        case SyntaxKind::AnsiPortList: {
            AnsiPortListBuilder builder{ scope, implicitMembers };
            for (auto port : syntax.as<AnsiPortListSyntax>().ports) {
                switch (port->kind) {
                    case SyntaxKind::ImplicitAnsiPort:
                        results.append(builder.createPort(port->as<ImplicitAnsiPortSyntax>()));
                        break;
                    case SyntaxKind::ExplicitAnsiPort:
                        results.append(builder.createPort(port->as<ExplicitAnsiPortSyntax>()));
                        break;
                    default:
                        THROW_UNREACHABLE;
                }
            }

            if (!portDeclarations.empty()) {
                scope.addDiag(diag::PortDeclInANSIModule,
                              portDeclarations[0].first->getFirstToken().location());
            }
            break;
        }
        case SyntaxKind::NonAnsiPortList: {
            NonAnsiPortListBuilder builder{ scope, portDeclarations, implicitMembers };
            for (auto port : syntax.as<NonAnsiPortListSyntax>().ports) {
                switch (port->kind) {
                    case SyntaxKind::ImplicitNonAnsiPort:
                        results.append(builder.createPort(port->as<ImplicitNonAnsiPortSyntax>()));
                        break;
                    case SyntaxKind::ExplicitNonAnsiPort:
                        scope.addDiag(diag::NotYetSupported, port->sourceRange());
                        break;
                    default:
                        THROW_UNREACHABLE;
                }
            }
            break;
        }
        case SyntaxKind::WildcardPortList:
            scope.addDiag(diag::NotYetSupported, syntax.sourceRange());
            break;
        default:
            THROW_UNREACHABLE;
    }
}

void PortSymbol::makeConnections(const Scope& childScope, span<Symbol* const> ports,
                                 const SeparatedSyntaxList<PortConnectionSyntax>& portConnections) {
    const Scope* instanceScope = childScope.asSymbol().getParentScope();
    ASSERT(instanceScope);

    PortConnectionBuilder builder(childScope, *instanceScope, portConnections);
    for (auto portBase : ports) {
        if (portBase->kind == SymbolKind::Port)
            builder.setConnection(portBase->as<PortSymbol>());
        else
            builder.setConnection(portBase->as<InterfacePortSymbol>());
    }

    builder.finalize();
}

void PortSymbol::toJson(json& j) const {
    j["direction"] = toString(direction);

    if (internalSymbol)
        j["internalSymbol"] = jsonLink(*internalSymbol);

    if (defaultValue)
        j["default"] = *defaultValue;

    if (auto ext = getConnection())
        j["externalConnection"] = *ext;
}

span<const ConstantRange> InterfacePortSymbol::getDeclaredRange() const {
    if (range)
        return *range;

    auto syntax = getSyntax();
    ASSERT(syntax);

    auto scope = getParentScope();
    ASSERT(scope);

    BindContext context(*scope, LookupLocation::before(*this));

    SmallVectorSized<ConstantRange, 4> buffer;
    for (auto dimSyntax : syntax->as<DeclaratorSyntax>().dimensions) {
        EvaluatedDimension dim = context.evalDimension(*dimSyntax, true);
        if (!dim.isRange()) {
            buffer.clear();
            break;
        }

        buffer.append(dim.range);
    }

    range = buffer.copy(scope->getCompilation());
    return *range;
}

void InterfacePortSymbol::toJson(json& j) const {
    if (interfaceDef)
        j["interfaceDef"] = jsonLink(*interfaceDef);
    if (modport)
        j["modport"] = jsonLink(*modport);
    if (connection)
        j["connection"] = jsonLink(*connection);
}

} // namespace slang