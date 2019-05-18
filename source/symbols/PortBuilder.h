//------------------------------------------------------------------------------
// PortBuilder.h
// Internal helpers to build port symbols and connections.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/compilation/Compilation.h"
#include "slang/symbols/HierarchySymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/util/StackContainer.h"

namespace slang {

namespace {

const NetType& getDefaultNetType(const Scope& scope, SourceLocation location) {
    auto& netType = scope.getDefaultNetType();
    if (!netType.isError())
        return netType;

    scope.addDiag(DiagCode::ImplicitNetPortNoDefault, location);
    return scope.getCompilation().getWireNetType();
}

// Helper class to build up lists of port symbols.
class AnsiPortListBuilder {
public:
    explicit AnsiPortListBuilder(const Scope& scope) :
        compilation(scope.getCompilation()), scope(scope) {}

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
                // direction If all three are omitted, inherit them all from the previous port.
                // We'll never even get into this code path if the very first port omitted all three
                // because then it would be a non-ansi port list.
                auto& header = syntax.header->as<VariablePortHeaderSyntax>();
                if (!header.direction && !header.varKeyword && typeSyntaxEmpty(*header.dataType))
                    return addInherited(decl);

                // It's possible that this is actually an interface port if the data type is just an
                // identifier. The only way to know is to do a lookup and see what comes back.
                const DefinitionSymbol* definition = nullptr;
                string_view simpleName = getSimpleTypeName(*header.dataType);
                if (!simpleName.empty()) {
                    auto found = scope.lookupUnqualifiedName(simpleName, LookupLocation::max,
                                                             header.dataType->sourceRange(),
                                                             LookupFlags::Type);

                    // If we didn't find a valid type, try to find a definition.
                    if (!found || !found->isType())
                        definition = compilation.getDefinition(simpleName, scope);
                }

                if (definition) {
                    if (definition->definitionKind != DefinitionKind::Interface) {
                        auto& diag = scope.addDiag(DiagCode::PortTypeNotInterfaceOrData,
                                                   header.dataType->sourceRange());
                        diag << definition->name;
                        diag.addNote(DiagCode::NoteDeclarationHere, definition->location);
                        definition = nullptr;
                    }
                    else {
                        if (header.varKeyword) {
                            scope.addDiag(DiagCode::VarWithInterfacePort,
                                          header.varKeyword.location());
                        }

                        if (header.direction) {
                            scope.addDiag(DiagCode::DirectionWithInterfacePort,
                                          header.direction.location());
                        }
                    }

                    return add(decl, definition, nullptr);
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
                return add(decl, direction, *header.dataType, netType);
            }
            case SyntaxKind::NetPortHeader: {
                auto& header = syntax.header->as<NetPortHeaderSyntax>();
                return add(decl, getDirection(header.direction), *header.dataType,
                           &compilation.getNetType(header.netType.kind));
            }
            case SyntaxKind::InterfacePortHeader: {
                // TODO: handle generic interface header
                auto& header = syntax.header->as<InterfacePortHeaderSyntax>();
                auto token = header.nameOrKeyword;
                auto definition = compilation.getDefinition(token.valueText(), scope);
                const ModportSymbol* modport = nullptr;

                if (!definition) {
                    scope.addDiag(DiagCode::UnknownInterface, token.range()) << token.valueText();
                }
                else if (definition->definitionKind != DefinitionKind::Interface) {
                    auto& diag = scope.addDiag(DiagCode::PortTypeNotInterfaceOrData,
                                               header.nameOrKeyword.range());
                    diag << definition->name;
                    diag.addNote(DiagCode::NoteDeclarationHere, definition->location);
                    definition = nullptr;
                }
                else if (header.modport) {
                    auto member = header.modport->member;
                    modport =
                        definition->getModportOrError(member.valueText(), scope, member.range());
                }

                return add(decl, definition, modport);
            }
            case SyntaxKind::InterconnectPortHeader:
                scope.addDiag(DiagCode::NotYetSupported, syntax.header->sourceRange());
                return addInherited(decl);
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

    Symbol* addInherited(const DeclaratorSyntax& decl) {
        if (lastInterface) {
            // TODO: inherit modport
            return add(decl, lastInterface, nullptr);
        }

        return add(decl, lastDirection, *lastType, lastNetType);
    }

    Symbol* add(const DeclaratorSyntax& decl, PortDirection direction, const DataTypeSyntax& type,
                const NetType* netType) {

        auto port = compilation.emplace<PortSymbol>(decl.name.valueText(), decl.name.location());
        port->direction = direction;
        port->setSyntax(decl);
        port->setDeclaredType(type, decl.dimensions);

        if (port->direction == PortDirection::InOut && !netType)
            scope.addDiag(DiagCode::InOutPortCannotBeVariable, port->location) << port->name;
        else if (port->direction == PortDirection::Ref && netType)
            scope.addDiag(DiagCode::RefPortMustBeVariable, port->location) << port->name;

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
        port->internalSymbol = symbol;

        // Remember the properties of this port in case the next port wants to inherit from it.
        lastDirection = direction;
        lastType = &type;
        lastNetType = netType;
        lastInterface = nullptr;

        return port;
    }

    Symbol* add(const DeclaratorSyntax& decl, const DefinitionSymbol* iface,
                const ModportSymbol* modport) {
        auto port =
            compilation.emplace<InterfacePortSymbol>(decl.name.valueText(), decl.name.location());

        port->interfaceDef = iface;
        port->modport = modport;
        port->setSyntax(decl);

        lastDirection = PortDirection::InOut;
        lastType = &UnsetType;
        lastNetType = nullptr;
        lastInterface = iface;

        return port;
    }

    Compilation& compilation;
    const Scope& scope;

    PortDirection lastDirection = PortDirection::InOut;
    const DataTypeSyntax* lastType = &UnsetType;
    const NetType* lastNetType = nullptr;
    const DefinitionSymbol* lastInterface = nullptr;

    static const ImplicitTypeSyntax UnsetType;
};

const ImplicitTypeSyntax AnsiPortListBuilder::UnsetType{ Token(), nullptr };

class NonAnsiPortListBuilder {
public:
    NonAnsiPortListBuilder(const Scope& scope,
                           span<const PortDeclarationSyntax* const> portDeclarations) :
        compilation(scope.getCompilation()),
        scope(scope) {

        // All port declarations in the scope have been collected; index them for easy lookup.
        for (auto port : portDeclarations) {
            for (auto decl : port->declarators) {
                if (auto name = decl->name; !name.isMissing()) {
                    auto result = portInfos.emplace(name.valueText(), PortInfo{ decl });
                    if (result.second) {
                        handleIODecl(*port->header, result.first->second);
                    }
                    else {
                        auto& diag = scope.addDiag(DiagCode::Redefinition, name.location());
                        diag << name.valueText();
                        diag.addNote(DiagCode::NotePreviousDefinition,
                                     result.first->second.syntax->name.location());
                    }
                }
            }
        }
    }

    Symbol* createPort(const ImplicitNonAnsiPortSyntax& syntax) {
        // TODO: location for empty ports?
        auto port = compilation.emplace<PortSymbol>("", SourceLocation());
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
                return port;
            }
            case SyntaxKind::PortConcatenation:
                scope.addDiag(DiagCode::NotYetSupported, syntax.sourceRange());
                return port;
            default:
                THROW_UNREACHABLE;
        }
    }

private:
    Compilation& compilation;
    const Scope& scope;

    struct PortInfo {
        const DeclaratorSyntax* syntax = nullptr;
        const Symbol* internalSymbol = nullptr;
        PortDirection direction;
        bool used = false;

        PortInfo(const DeclaratorSyntax* syntax) : syntax(syntax) {}
    };
    SmallMap<string_view, PortInfo, 8> portInfos;

    const PortInfo* getInfo(string_view name, SourceLocation loc) {
        if (name.empty())
            return nullptr;

        auto it = portInfos.find(name);
        if (it == portInfos.end()) {
            scope.addDiag(DiagCode::MissingPortIODeclaration, loc) << name;
            return nullptr;
        }

        // TODO: error at the end if a port I/O is unused
        it->second.used = true;
        return &it->second;
    }

    void handleIODecl(const PortHeaderSyntax& header, PortInfo& info) {
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
                    variable->setSyntax(decl);
                    variable->setDeclaredType(*varHeader.dataType, decl.dimensions);
                    info.internalSymbol = variable;
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
                    net->setSyntax(decl);
                    net->setDeclaredType(*varHeader.dataType, decl.dimensions);
                    info.internalSymbol = net;
                }

                if (info.direction == PortDirection::InOut &&
                    info.internalSymbol->kind != SymbolKind::Net) {
                    scope.addDiag(DiagCode::InOutPortCannotBeVariable, declLoc) << name;
                }
                else if (info.direction == PortDirection::Ref &&
                         info.internalSymbol->kind == SymbolKind::Net) {
                    scope.addDiag(DiagCode::RefPortMustBeVariable, declLoc) << name;
                }
                break;
            }
            case SyntaxKind::NetPortHeader: {
                auto& netHeader = header.as<NetPortHeaderSyntax>();
                info.direction = SemanticFacts::getPortDirection(netHeader.direction.kind);
                if (info.direction == PortDirection::Ref)
                    scope.addDiag(DiagCode::RefPortMustBeVariable, declLoc) << name;

                // Create a new symbol to represent this port internally to the instance.
                auto net = compilation.emplace<NetSymbol>(
                    name, declLoc, compilation.getNetType(netHeader.netType.kind));
                net->setSyntax(decl);
                net->setDeclaredType(*netHeader.dataType, decl.dimensions);
                info.internalSymbol = net;
                break;
            }
            case SyntaxKind::InterconnectPortHeader:
            case SyntaxKind::InterfacePortHeader:
                scope.addDiag(DiagCode::NotYetSupported, header.sourceRange());
                break;
            default:
                THROW_UNREACHABLE;
        }
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
                auto& diag = scope.addDiag(DiagCode::CantDeclarePortSigned, location);
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

        bool hasConnections = false;
        lookupLocation = LookupLocation::before(instance);

        for (auto conn : portConnections) {
            bool isOrdered = conn->kind == SyntaxKind::OrderedPortConnection;
            if (!hasConnections) {
                hasConnections = true;
                usingOrdered = isOrdered;
            }
            else if (isOrdered != usingOrdered) {
                scope.addDiag(DiagCode::MixingOrderedAndNamedPorts,
                              conn->getFirstToken().location());
                break;
            }

            if (isOrdered) {
                orderedConns.append(conn->as<OrderedPortConnectionSyntax>().expr);
            }
            else if (conn->kind == SyntaxKind::WildcardPortConnection) {
                if (!std::exchange(hasWildcard, true))
                    wildcardRange = conn->sourceRange();
                else {
                    auto& diag = scope.addDiag(DiagCode::DuplicateWildcardPortConnection,
                                               conn->sourceRange());
                    diag.addNote(DiagCode::NotePreviousUsage, wildcardRange.start());
                }
            }
            else {
                auto& npc = conn->as<NamedPortConnectionSyntax>();
                auto name = npc.name.valueText();
                if (!name.empty()) {
                    auto pair = namedConns.emplace(name, std::make_pair(&npc, false));
                    if (!pair.second) {
                        auto& diag =
                            scope.addDiag(DiagCode::DuplicatePortConnection, npc.name.location());
                        diag << name;
                        diag.addNote(DiagCode::NotePreviousUsage,
                                     pair.first->second.first->name.location());
                    }
                }
            }
        }

        // Build up the set of dimensions for the instantiating instance's array parent, if any.
        // This builds up the dimensions in reverse order, so we have to reverse them back.
        auto parent = instance.getParent();
        while (parent && parent->asSymbol().kind == SymbolKind::InstanceArray) {
            auto& sym = parent->asSymbol().as<InstanceArraySymbol>();
            instanceDims.append(sym.range);
            parent = sym.getParent();
        }
        std::reverse(instanceDims.begin(), instanceDims.end());
    }

    void setConnection(PortSymbol& port) {
        if (usingOrdered) {
            if (orderedIndex >= orderedConns.size()) {
                orderedIndex++;
                if (port.defaultValue)
                    port.setConnection(port.defaultValue);
                else if (port.name.empty()) {
                    if (!warnedAboutUnnamed) {
                        auto& diag =
                            scope.addDiag(DiagCode::UnconnectedUnnamedPort, instance.location);
                        diag.addNote(DiagCode::NoteDeclarationHere, port.location);
                        warnedAboutUnnamed = true;
                    }
                }
                else {
                    scope.addDiag(DiagCode::UnconnectedNamedPort, instance.location) << port.name;
                }

                return;
            }

            const ExpressionSyntax* expr = orderedConns[orderedIndex++];
            if (expr)
                port.setConnection(*expr);
            else
                port.setConnection(port.defaultValue);

            return;
        }

        if (port.name.empty()) {
            // port is unnamed so can never be connected by name
            if (!warnedAboutUnnamed) {
                auto& diag = scope.addDiag(DiagCode::UnconnectedUnnamedPort, instance.location);
                diag.addNote(DiagCode::NoteDeclarationHere, port.location);
                warnedAboutUnnamed = true;
            }
            return;
        }

        auto it = namedConns.find(port.name);
        if (it == namedConns.end()) {
            if (hasWildcard) {
                implicitNamedPort(port, wildcardRange, true);
                return;
            }

            if (port.defaultValue)
                port.setConnection(port.defaultValue);
            else
                scope.addDiag(DiagCode::UnconnectedNamedPort, instance.location) << port.name;
            return;
        }

        // We have a named connection; there are two possibilities here:
        // - An explicit connection (with an optional expression)
        // - An implicit connection, where we have to look up the name ourselves
        const NamedPortConnectionSyntax& conn = *it->second.first;
        it->second.second = true;

        if (conn.openParen) {
            // For explicit named port connections, having an empty expression means no connection,
            // so we never take the default value here.
            if (conn.expr)
                port.setConnection(*conn.expr);

            return;
        }

        implicitNamedPort(port, conn.name.range(), false);
    }

    void setConnection(InterfacePortSymbol& port) {
        // TODO: verify that interface ports must always have a name
        ASSERT(!port.name.empty());

        auto reportUnconnected = [&]() {
            auto& diag = scope.addDiag(DiagCode::InterfacePortNotConnected, instance.location);
            diag << port.name;
            diag.addNote(DiagCode::NoteDeclarationHere, port.location);
        };

        if (usingOrdered) {
            const ExpressionSyntax* expr = nullptr;
            if (orderedIndex < orderedConns.size())
                expr = orderedConns[orderedIndex];

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
                auto& diag = scope.addDiag(DiagCode::TooManyPortConnections, loc);
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
                    auto& diag = scope.addDiag(DiagCode::PortDoesNotExist,
                                               pair.second.first->name.location());
                    diag << pair.second.first->name.valueText();
                    diag << instance.name;
                }
            }
        }
    }

private:
    void implicitNamedPort(PortSymbol& port, SourceRange range, bool isWildcard) {
        // An implicit named port connection is semantically equivalent to `.port(port)` except:
        // - Can't create implicit net declarations this way
        // - Port types need to be equivalent, not just assignment compatible
        // - An implicit connection between nets of two dissimilar net types shall issue an
        //   error when it is a warning in an explicit named port connection

        LookupFlags flags = isWildcard ? LookupFlags::DisallowWildcardImport : LookupFlags::None;
        auto symbol = scope.lookupUnqualifiedName(port.name, lookupLocation, range, flags);
        if (!symbol) {
            // If this is a wildcard connection, we're allowed to use the port's default value,
            // if it has one.
            if (isWildcard && port.defaultValue)
                port.setConnection(port.defaultValue);
            else
                scope.addDiag(DiagCode::ImplicitNamedPortNotFound, range) << port.name;
            return;
        }

        auto expr = &NamedValueExpression::fromSymbol(scope, *symbol, false, range);
        if (expr->bad())
            return;

        if (!expr->type->isEquivalent(port.getType())) {
            auto& diag = scope.addDiag(DiagCode::ImplicitNamedPortTypeMismatch, range);
            diag << port.name;
            diag << port.getType();
            diag << *expr->type;
            return;
        }

        // TODO: direction of assignment
        port.setConnection(&Expression::convertAssignment(BindContext(scope, LookupLocation::max),
                                                          port.getType(), *expr, range.start()));
    }

    void setInterfaceExpr(InterfacePortSymbol& port, const ExpressionSyntax& syntax) {
        if (!NameSyntax::isKind(syntax.kind)) {
            scope.addDiag(DiagCode::InterfacePortInvalidExpression, syntax.sourceRange())
                << port.name;
            return;
        }

        LookupResult result;
        scope.lookupName(syntax.as<NameSyntax>(), lookupLocation, LookupFlags::None, result);
        if (result.hasError())
            scope.getCompilation().addDiagnostics(result.getDiagnostics());

        const Symbol* symbol = result.found;
        if (!symbol)
            return;

        setInterface(port, symbol, syntax.sourceRange());
    }

    void setImplicitInterface(InterfacePortSymbol& port, SourceRange range) {
        auto symbol = scope.lookupUnqualifiedName(port.name, lookupLocation, range);
        if (!symbol) {
            scope.addDiag(DiagCode::ImplicitNamedPortNotFound, range) << port.name;
            return;
        }

        setInterface(port, symbol, range);
    }

    static bool areDimSizesEqual(span<const ConstantRange> left, span<const ConstantRange> right) {
        if (left.size() != right.size())
            return false;

        for (ptrdiff_t i = 0; i < left.size(); i++) {
            if (left[i].width() != right[i].width())
                return false;
        }

        return true;
    }

    void setInterface(InterfacePortSymbol& port, const Symbol* symbol, SourceRange range) {
        if (!port.interfaceDef)
            return;

        // Make sure the thing we're connecting to is an interface or array of interfaces.
        SmallVectorSized<ConstantRange, 4> dims;
        const Symbol* child = symbol;
        while (child->kind == SymbolKind::InstanceArray) {
            // The array shouldn't be empty unless an error ocurred earlier in elaboration.
            auto& array = child->as<InstanceArraySymbol>();
            if (array.elements.empty())
                return;

            dims.append(array.range);
            child = array.elements[0];
        }

        // TODO: handle interface/modport ports as well
        if (child->kind != SymbolKind::InterfaceInstance) {
            scope.addDiag(DiagCode::NotAnInterface, range) << symbol->name;
            return;
        }

        auto connDef = &child->as<InterfaceInstanceSymbol>().definition;
        if (connDef != port.interfaceDef) {
            // TODO: print the potentially nested name path instead of the simple name
            auto& diag = scope.addDiag(DiagCode::InterfacePortTypeMismatch, range);
            diag << connDef->name << port.interfaceDef->name;
            diag.addNote(DiagCode::NoteDeclarationHere, port.location);
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
            for (ptrdiff_t i = 0; i < instance.arrayPath.size(); i++) {
                auto& array = symbol->as<InstanceArraySymbol>();
                int32_t index = instanceDims[i].translateIndex(instance.arrayPath[i]);
                if (!array.range.isLittleEndian())
                    index = array.range.upper() - index;

                symbol = array.elements[index];
            }

            port.connection = symbol;
            return;
        }

        auto& diag = scope.addDiag(DiagCode::PortConnDimensionsMismatch, range);
        diag.addNote(DiagCode::NoteDeclarationHere, port.location);
    }

    const Scope& scope;
    const InstanceSymbol& instance;
    SmallVectorSized<ConstantRange, 4> instanceDims;
    SmallVectorSized<const ExpressionSyntax*, 8> orderedConns;
    SmallMap<string_view, std::pair<const NamedPortConnectionSyntax*, bool>, 8> namedConns;
    LookupLocation lookupLocation;
    SourceRange wildcardRange;
    size_t orderedIndex = 0;
    bool usingOrdered = true;
    bool hasWildcard = false;
    bool warnedAboutUnnamed = false;
};

} // end anonymous namespace

} // namespace slang