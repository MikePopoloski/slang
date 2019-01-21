//------------------------------------------------------------------------------
// MemberSymbols.cpp
// Contains member-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/MemberSymbols.h"

#include <nlohmann/json.hpp>

#include "slang/compilation/Compilation.h"
#include "slang/symbols/HierarchySymbols.h"
#include "slang/util/StackContainer.h"

namespace slang {

const PackageSymbol* ExplicitImportSymbol::package() const {
    importedSymbol();
    return package_;
}

const Symbol* ExplicitImportSymbol::importedSymbol() const {
    if (!initialized) {
        initialized = true;

        const Scope* scope = getScope();
        ASSERT(scope);

        if (packageName.empty())
            return nullptr;

        package_ = scope->getCompilation().getPackage(packageName);
        if (!package_) {
            auto loc = location;
            if (auto syntax = getSyntax(); syntax)
                loc = syntax->as<PackageImportItemSyntax>().package.location();

            scope->addDiag(DiagCode::UnknownPackage, loc) << packageName;
        }
        else if (importName.empty()) {
            return nullptr;
        }
        else {
            import = package_->find(importName);
            if (!import) {
                auto loc = location;
                if (auto syntax = getSyntax())
                    loc = syntax->as<PackageImportItemSyntax>().item.location();

                auto& diag = scope->addDiag(DiagCode::UnknownPackageMember, loc);
                diag << importName << packageName;
            }
        }
    }
    return import;
}

void ExplicitImportSymbol::toJson(json& j) const {
    if (auto pkg = package())
        j["package"] = jsonLink(*pkg);

    if (auto sym = importedSymbol())
        j["import"] = jsonLink(*sym);
}

const PackageSymbol* WildcardImportSymbol::getPackage() const {
    if (!package) {
        const Scope* scope = getScope();
        ASSERT(scope);

        if (packageName.empty()) {
            package = nullptr;
        }
        else {
            package = scope->getCompilation().getPackage(packageName);
            if (!package.value()) {
                auto loc = location;
                if (auto syntax = getSyntax(); syntax)
                    loc = syntax->as<PackageImportItemSyntax>().package.location();

                scope->addDiag(DiagCode::UnknownPackage, loc) << packageName;
            }
        }
    }
    return *package;
}

void WildcardImportSymbol::toJson(json& j) const {
    if (auto pkg = getPackage())
        j["package"] = jsonLink(*pkg);
}

ParameterSymbol::ParameterSymbol(string_view name, SourceLocation loc, bool isLocal, bool isPort) :
    ValueSymbol(SymbolKind::Parameter, name, loc,
                DeclaredTypeFlags::InferImplicit | DeclaredTypeFlags::RequireConstant),
    isLocal(isLocal), isPort(isPort) {
}

void ParameterSymbol::fromSyntax(const Scope& scope, const ParameterDeclarationSyntax& syntax,
                                 bool isLocal, bool isPort,
                                 SmallVector<ParameterSymbol*>& results) {
    for (auto decl : syntax.declarators) {
        auto loc = decl->name.location();
        auto param = scope.getCompilation().emplace<ParameterSymbol>(decl->name.valueText(), loc,
                                                                     isLocal, isPort);
        param->setDeclaredType(*syntax.type);
        param->setFromDeclarator(*decl);

        if (!decl->initializer) {
            if (!isPort)
                scope.addDiag(DiagCode::BodyParamNoInitializer, loc);
            else if (isLocal)
                scope.addDiag(DiagCode::LocalParamNoInitializer, loc);
        }

        results.append(param);
    }
}

ParameterSymbol& ParameterSymbol::createOverride(Compilation& compilation,
                                                 const Expression* newInitializer) const {
    auto result = compilation.emplace<ParameterSymbol>(name, location, isLocal, isPort);
    if (auto syntax = getSyntax())
        result->setSyntax(*syntax);

    auto declared = getDeclaredType();
    if (auto typeSyntax = declared->getTypeSyntax()) {
        if (auto dimensions = declared->getDimensionSyntax())
            result->setDeclaredType(*typeSyntax, *dimensions);
        else
            result->setDeclaredType(*typeSyntax);
    }

    if (newInitializer) {
        result->setType(*newInitializer->type);
        result->setInitializer(*newInitializer);
    }
    else if (auto init = declared->getInitializerSyntax()) {
        result->setInitializerSyntax(*init, declared->getInitializerLocation());
    }

    return *result;
}

const ConstantValue& ParameterSymbol::getValue() const {
    return overriden ? *overriden : getConstantValue();
}

void ParameterSymbol::setValue(ConstantValue value) {
    auto scope = getScope();
    ASSERT(scope);
    overriden = scope->getCompilation().allocConstant(std::move(value));
}

void ParameterSymbol::toJson(json& j) const {
    j["value"] = getValue();
    j["isLocal"] = isLocalParam();
    j["isPort"] = isPortParam();
    j["isBody"] = isBodyParam();
}

namespace {

string_view getSimpleName(const DataTypeSyntax& syntax) {
    if (syntax.kind == SyntaxKind::NamedType) {
        auto& namedType = syntax.as<NamedTypeSyntax>();
        if (namedType.name->kind == SyntaxKind::IdentifierName)
            return namedType.name->as<IdentifierNameSyntax>().identifier.valueText();
    }
    return "";
}

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
    AnsiPortListBuilder(const Scope& scope, SmallVector<Symbol*>& ports) :
        compilation(scope.getCompilation()), scope(scope), ports(ports) {}

    PortDirection getDirection(Token token) const {
        return token ? SemanticFacts::getPortDirection(token.kind) : lastDirection;
    }

    void addInherited(const DeclaratorSyntax& decl) {
        if (lastInterface) {
            // TODO: inherit modport
            add(decl, lastInterface, nullptr);
            return;
        }

        add(decl, lastDirection, *lastType, lastNetType);
    }

    void add(const DeclaratorSyntax& decl, PortDirection direction, const DataTypeSyntax& type,
             const NetType* netType) {

        auto port = compilation.emplace<PortSymbol>(decl.name.valueText(), decl.name.location());
        ports.append(port);

        port->direction = direction;
        port->setSyntax(decl);
        port->setDeclaredType(type, decl.dimensions);

        if (port->direction == PortDirection::InOut && !netType)
            scope.addDiag(DiagCode::InOutPortCannotBeVariable, port->location) << port->name;
        else if (port->direction == PortDirection::Ref && netType)
            scope.addDiag(DiagCode::RefPortMustBeVariable, port->location) << port->name;

        // Create a new symbol to represent this port internally to the instance.
        // TODO: interconnect ports don't have a datatype
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
        lastType = port->getDeclaredType()->getTypeSyntax();
        lastNetType = netType;
        lastInterface = nullptr;
    }

    void add(const DeclaratorSyntax& decl, const DefinitionSymbol* iface,
             const ModportSymbol* modport) {
        // TODO: dimensions
        auto port =
            compilation.emplace<InterfacePortSymbol>(decl.name.valueText(), decl.name.location());
        ports.append(port);

        port->interfaceDef = iface;
        port->modport = modport;
        port->setSyntax(decl);

        lastDirection = PortDirection::InOut;
        lastType = &UnsetType;
        lastNetType = nullptr;
        lastInterface = iface;
    }

private:
    Compilation& compilation;
    const Scope& scope;
    SmallVector<Symbol*>& ports;

    PortDirection lastDirection = PortDirection::InOut;
    const DataTypeSyntax* lastType = &UnsetType;
    const NetType* lastNetType = nullptr;
    const DefinitionSymbol* lastInterface = nullptr;

    static const ImplicitTypeSyntax UnsetType;
};

const ImplicitTypeSyntax AnsiPortListBuilder::UnsetType{ Token(), nullptr };

void handleImplicitAnsiPort(const ImplicitAnsiPortSyntax& syntax, AnsiPortListBuilder& builder,
                            const Scope& scope) {
    Compilation& comp = scope.getCompilation();
    auto& decl = *syntax.declarator;

    // Helper function to check if an implicit type syntax is totally empty.
    auto typeSyntaxEmpty = [](const DataTypeSyntax& typeSyntax) {
        if (typeSyntax.kind != SyntaxKind::ImplicitType)
            return false;

        const auto& implicitType = typeSyntax.as<ImplicitTypeSyntax>();
        return !implicitType.signing && implicitType.dimensions.empty();
    };

    switch (syntax.header->kind) {
        case SyntaxKind::VariablePortHeader: {
            // A VariablePortHeader is parsed as a catch-all when we aren't sure what kind of port
            // this is. There are three components to a port that matter: kind, type, direction If
            // all three are omitted, inherit them all from the previous port. We'll never even get
            // into this code path if the very first port omitted all three because then it would be
            // a non-ansi port list.
            auto& header = syntax.header->as<VariablePortHeaderSyntax>();
            if (!header.direction && !header.varKeyword && typeSyntaxEmpty(*header.dataType)) {
                builder.addInherited(decl);
                return;
            }

            // It's possible that this is actually an interface port if the data type is just an
            // identifier. The only way to know is to do a lookup and see what comes back.
            const DefinitionSymbol* definition = nullptr;
            string_view simpleName = getSimpleName(*header.dataType);
            if (!simpleName.empty()) {
                auto found =
                    scope.lookupUnqualifiedName(simpleName, LookupLocation::max,
                                                header.dataType->sourceRange(), LookupFlags::Type);

                // If we didn't find a valid type, try to find a definition.
                if (!found || !found->isType())
                    definition = comp.getDefinition(simpleName, scope);
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
                        scope.addDiag(DiagCode::VarWithInterfacePort, header.varKeyword.location());
                    }

                    if (header.direction) {
                        scope.addDiag(DiagCode::DirectionWithInterfacePort,
                                      header.direction.location());
                    }
                }

                builder.add(decl, definition, nullptr);
                return;
            }

            // Rules from [23.2.2.3]:
            // - If we have a var keyword, it's a var
            // - For input and inout, default to a net
            // - For output, if we have a data type it's a var, otherwise net
            // - For ref it's always a var
            PortDirection direction = builder.getDirection(header.direction);
            const NetType* netType = nullptr;
            if (!header.varKeyword &&
                (direction == PortDirection::In || direction == PortDirection::InOut ||
                 (direction == PortDirection::Out &&
                  header.dataType->kind == SyntaxKind::ImplicitType))) {

                netType = &getDefaultNetType(scope, decl.name.location());
            }

            // TODO: user-defined nettypes
            builder.add(decl, direction, *header.dataType, netType);
            return;
        }
        case SyntaxKind::NetPortHeader: {
            auto& header = syntax.header->as<NetPortHeaderSyntax>();
            builder.add(decl, builder.getDirection(header.direction), *header.dataType,
                        &comp.getNetType(header.netType.kind));
            return;
        }
        case SyntaxKind::InterfacePortHeader: {
            // TODO: handle generic interface header
            auto& header = syntax.header->as<InterfacePortHeaderSyntax>();
            auto definition = comp.getDefinition(header.nameOrKeyword.valueText(), scope);
            const ModportSymbol* modport = nullptr;

            if (!definition) {
                // TODO: report error if unable to find definition
            }
            else if (definition->definitionKind != DefinitionKind::Interface) {
                // TODO: report error here
                /*auto& diag = scope.addDiag(DiagCode::PortTypeNotInterfaceOrData,
                                            header.dataType->sourceRange());
                diag << definition->name;
                diag.addNote(DiagCode::NoteDeclarationHere, definition->location);*/
                definition = nullptr;
            }
            else if (header.modport && !header.modport->member.valueText().empty()) {
                // TODO: error if unfound or not actually a modport
                // TODO: handle arrays
                auto member = header.modport->member;
                auto symbol = definition->find(member.valueText());
                if (!symbol) {
                    auto& diag = scope.addDiag(DiagCode::UnknownMember, member.range());
                    diag << member.valueText();
                    diag << definition->name;
                }
                else if (symbol->kind != SymbolKind::Modport) {
                    auto& diag = scope.addDiag(DiagCode::NotAModport, member.range());
                    diag << member.valueText();
                    diag.addNote(DiagCode::NoteDeclarationHere, symbol->location);
                }
                else {
                    modport = &symbol->as<ModportSymbol>();
                }
            }

            builder.add(decl, definition, modport);
            return;
        }
        default:
            // TODO:
            THROW_UNREACHABLE;
    }
}

struct NonAnsiPortListBuilder {
    Compilation& compilation;
    SmallVector<Symbol*>& ports;

    struct PortInfo {
        const DeclaratorSyntax* syntax = nullptr;
        const Symbol* internalSymbol = nullptr;
        PortDirection direction;
        bool used = false;

        PortInfo(const DeclaratorSyntax* syntax) : syntax(syntax) {}
    };
    SmallMap<string_view, PortInfo, 8> portInfos;

    NonAnsiPortListBuilder(SmallVector<Symbol*>& ports, const Scope& scope,
                           span<const PortDeclarationSyntax* const> portDeclarations) :
        compilation(scope.getCompilation()),
        ports(ports) {

        // All port declarations in the scope have been collected; index them for easy lookup.
        for (auto port : portDeclarations) {
            for (auto decl : port->declarators) {
                if (auto name = decl->name; !name.isMissing()) {
                    auto result = portInfos.emplace(name.valueText(), PortInfo{ decl });
                    if (result.second) {
                        handleIODecl(*port->header, result.first->second, scope);
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

    void handleIODecl(const PortHeaderSyntax& header, PortInfo& info, const Scope& scope);

    const PortInfo* getInfo(string_view name, SourceLocation loc, const Scope& scope) {
        if (name.empty())
            return nullptr;

        auto it = portInfos.find(name);
        if (it == portInfos.end()) {
            scope.addDiag(DiagCode::MissingPortIODeclaration, loc);
            return nullptr;
        }

        // TODO: error at the end if a port I/O is unused
        it->second.used = true;
        return &it->second;
    }
};

void mergePortTypes(const ValueSymbol& symbol, const ImplicitTypeSyntax& implicit,
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

void NonAnsiPortListBuilder::handleIODecl(const PortHeaderSyntax& header, PortInfo& info,
                                          const Scope& scope) {
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
                     symbol &&
                     (symbol->kind == SymbolKind::Variable || symbol->kind == SymbolKind::Net)) {

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
        default:
            // TODO:
            THROW_UNREACHABLE;
    }
}

void handleImplicitNonAnsiPort(const ImplicitNonAnsiPortSyntax& syntax,
                               NonAnsiPortListBuilder& builder, const Scope& scope) {

    // TODO: location for empty ports?
    auto& comp = builder.compilation;
    auto& port = *comp.emplace<PortSymbol>("", SourceLocation());
    port.setSyntax(syntax);
    builder.ports.append(&port);

    // Unnamed empty port is allowed.
    if (!syntax.expr)
        return;

    switch (syntax.expr->kind) {
        case SyntaxKind::PortReference: {
            auto& ref = syntax.expr->as<PortReferenceSyntax>();
            port.name = ref.name.valueText();
            port.location = ref.name.location();

            auto info = builder.getInfo(port.name, port.location, scope);
            if (!info)
                return;

            // TODO: explicit connection expression

            ASSERT(info->internalSymbol);
            port.direction = info->direction;
            port.internalSymbol = info->internalSymbol;
            port.getDeclaredType()->copyTypeFrom(*info->internalSymbol->getDeclaredType());
            break;
        }
        default:
            // TODO: handle concatenations
            THROW_UNREACHABLE;
    }
}

struct PortConnectionBuilder {
    PortConnectionBuilder(const Scope& childScope, const Scope& instanceScope,
                          const SeparatedSyntaxList<PortConnectionSyntax>& portConnections) :
        scope(instanceScope),
        instance(childScope.asSymbol()) {

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
    }

    void setConnection(PortSymbol& port) {
        if (usingOrdered) {
            if (orderedIndex >= orderedConns.size()) {
                orderedIndex++;
                if (port.defaultValue)
                    port.setExternalConnection(port.defaultValue);
                else {
                    // TODO: warning about unconnected port
                }

                return;
            }

            const ExpressionSyntax* expr = orderedConns[orderedIndex++];
            if (expr)
                port.setExternalConnection(*expr);
            else
                port.setExternalConnection(port.defaultValue);

            return;
        }

        if (port.name.empty()) {
            // TODO: warning about unconnected?
            // port is unnamed so can never be connected by name
            return;
        }

        auto it = namedConns.find(port.name);
        if (it == namedConns.end()) {
            if (hasWildcard) {
                implicitNamedPort(port, wildcardRange, true);
                return;
            }

            if (port.defaultValue)
                port.setExternalConnection(port.defaultValue);
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
                port.setExternalConnection(*conn.expr);

            return;
        }

        implicitNamedPort(port, conn.name.range(), false);
    }

    const InterfaceInstanceSymbol* getConnection(const InterfacePortSymbol& port) {
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
                return nullptr;
            }

            return lookupInterface(port, *expr);
        }

        auto it = namedConns.find(port.name);
        if (it == namedConns.end()) {
            if (hasWildcard)
                return lookupImplicitInterface(port, wildcardRange);

            reportUnconnected();
            return nullptr;
        }

        // We have a named connection; there are two possibilities here:
        // - An explicit connection (with an optional expression)
        // - An implicit connection, where we have to look up the name ourselves
        const NamedPortConnectionSyntax& conn = *it->second.first;
        it->second.second = true;

        if (conn.openParen) {
            // For explicit named port connections, having an empty expression means no connection.
            if (!conn.expr) {
                reportUnconnected();
                return nullptr;
            }

            return lookupInterface(port, *conn.expr);
        }

        return lookupImplicitInterface(port, conn.name.range());
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
                port.setExternalConnection(port.defaultValue);
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

        port.setExternalConnection(
            &Expression::convertAssignment(scope, port.getType(), *expr, range.start()));
    }

    const InterfaceInstanceSymbol* lookupInterface(const InterfacePortSymbol& port,
                                                   const ExpressionSyntax& syntax) {
        if (!NameSyntax::isKind(syntax.kind)) {
            scope.addDiag(DiagCode::InterfacePortInvalidExpression, syntax.sourceRange())
                << port.name;
            return nullptr;
        }

        LookupResult result;
        scope.lookupName(syntax.as<NameSyntax>(), lookupLocation, LookupFlags::None, result);

        // TODO: check selectors

        if (result.hasError())
            scope.getCompilation().addDiagnostics(result.getDiagnostics());

        const Symbol* symbol = result.found;
        if (!symbol)
            return nullptr;

        return checkInterfaceLookup(port, symbol, syntax.sourceRange());
    }

    const InterfaceInstanceSymbol* lookupImplicitInterface(const InterfacePortSymbol& port,
                                                           SourceRange range) {

        auto symbol = scope.lookupUnqualifiedName(port.name, lookupLocation, range);
        if (!symbol) {
            scope.addDiag(DiagCode::ImplicitNamedPortNotFound, range) << port.name;
            return nullptr;
        }

        return checkInterfaceLookup(port, symbol, range);
    }

    const InterfaceInstanceSymbol* checkInterfaceLookup(const InterfacePortSymbol&,
                                                        const Symbol* symbol, SourceRange range) {
        // TODO: handle interface/modport ports as well
        if (symbol->kind != SymbolKind::InterfaceInstance) {
            scope.addDiag(DiagCode::NotAnInterface, range) << symbol->name;
            return nullptr;
        }

        return &symbol->as<InterfaceInstanceSymbol>();
    }

    const Scope& scope;
    const Symbol& instance;
    SmallVectorSized<const ExpressionSyntax*, 8> orderedConns;
    SmallMap<string_view, std::pair<const NamedPortConnectionSyntax*, bool>, 8> namedConns;
    LookupLocation lookupLocation;
    SourceRange wildcardRange;
    size_t orderedIndex = 0;
    bool usingOrdered = true;
    bool hasWildcard = false;
};

} // end anonymous namespace

const Expression* PortSymbol::getExternalConnection() const {
    if (!externalConn) {
        if (!externalSyntax)
            externalConn = nullptr;
        else {
            BindContext context(*getScope(), LookupLocation::before(*this));
            externalConn = &Expression::bind(getType(), *externalSyntax,
                                             externalSyntax->getFirstToken().location(), context);
        }
    }
    return *externalConn;
}

void PortSymbol::setExternalConnection(const Expression* expr) {
    externalConn = expr;
    externalSyntax = nullptr;
}

void PortSymbol::setExternalConnection(const ExpressionSyntax& syntax) {
    externalConn = nullptr;
    externalSyntax = &syntax;
}

void PortSymbol::fromSyntax(const PortListSyntax& syntax, const Scope& scope,
                            SmallVector<Symbol*>& results,
                            span<const PortDeclarationSyntax* const> portDeclarations) {
    switch (syntax.kind) {
        case SyntaxKind::AnsiPortList: {
            // TODO: error if we have port declaration members
            AnsiPortListBuilder builder{ scope, results };
            for (auto port : syntax.as<AnsiPortListSyntax>().ports) {
                switch (port->kind) {
                    case SyntaxKind::ImplicitAnsiPort:
                        handleImplicitAnsiPort(port->as<ImplicitAnsiPortSyntax>(), builder, scope);
                        break;
                    default:
                        // TODO:
                        THROW_UNREACHABLE;
                }
            }
            break;
        }
        case SyntaxKind::NonAnsiPortList: {
            NonAnsiPortListBuilder builder{ results, scope, portDeclarations };
            for (auto port : syntax.as<NonAnsiPortListSyntax>().ports) {
                switch (port->kind) {
                    case SyntaxKind::ImplicitNonAnsiPort:
                        handleImplicitNonAnsiPort(port->as<ImplicitNonAnsiPortSyntax>(), builder,
                                                  scope);
                        break;
                    default:
                        THROW_UNREACHABLE;
                }
            }
            break;
        }
        default:
            THROW_UNREACHABLE;
    }
}

void PortSymbol::makeConnections(const Scope& childScope, span<Symbol* const> ports,
                                 const SeparatedSyntaxList<PortConnectionSyntax>& portConnections) {
    const Scope* instanceScope = childScope.getParent();
    ASSERT(instanceScope);

    PortConnectionBuilder builder(childScope, *instanceScope, portConnections);
    for (auto portBase : ports) {
        if (portBase->kind == SymbolKind::Port) {
            PortSymbol& port = portBase->as<PortSymbol>();
            builder.setConnection(port);
        }
        else {
            InterfacePortSymbol& port = portBase->as<InterfacePortSymbol>();
            port.connection = builder.getConnection(port);
        }
    }

    builder.finalize();
}

void PortSymbol::toJson(json& j) const {
    j["direction"] = toString(direction);

    if (internalSymbol)
        j["internalSymbol"] = jsonLink(*internalSymbol);

    if (defaultValue)
        j["default"] = *defaultValue;

    if (internalConnection)
        j["internalConnection"] = *internalConnection;

    if (auto ext = getExternalConnection())
        j["externalConnection"] = *ext;
}

void InterfacePortSymbol::toJson(json& j) const {
    if (interfaceDef)
        j["interfaceDef"] = jsonLink(*interfaceDef);
    if (modport)
        j["modport"] = jsonLink(*modport);
    if (connection)
        j["connection"] = jsonLink(*connection);
}

void NetSymbol::fromSyntax(Compilation& compilation, const NetDeclarationSyntax& syntax,
                           SmallVector<const NetSymbol*>& results) {

    // TODO: other net features
    const NetType& netType = compilation.getNetType(syntax.netType.kind);

    for (auto declarator : syntax.declarators) {
        auto net = compilation.emplace<NetSymbol>(declarator->name.valueText(),
                                                  declarator->name.location(), netType);

        net->setDeclaredType(*syntax.type, declarator->dimensions);
        net->setFromDeclarator(*declarator);
        results.append(net);
    }
}

void VariableSymbol::fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                                const Scope& scope, SmallVector<const ValueSymbol*>& results) {
    // TODO: check modifiers

    // This might actually be a net declaration with a user defined net type. That can only
    // be true if the data type syntax is a simple identifier, so if we see that it is,
    // perform a lookup (without forcing the scope to elaborate) and see what comes back.
    string_view simpleName = getSimpleName(*syntax.type);
    if (!simpleName.empty()) {
        auto result = scope.lookupUnqualifiedName(
            simpleName, LookupLocation::max, syntax.type->sourceRange(), LookupFlags::None, true);

        if (result && result->kind == SymbolKind::NetType) {
            const NetType& netType = result->as<NetType>();
            netType.getAliasTarget(); // force resolution of target

            auto& declaredType = *netType.getDeclaredType();
            for (auto declarator : syntax.declarators) {
                auto net = compilation.emplace<NetSymbol>(declarator->name.valueText(),
                                                          declarator->name.location(), netType);

                net->getDeclaredType()->copyTypeFrom(declaredType);
                net->setFromDeclarator(*declarator);
                results.append(net);
            }
            return;
        }
    }

    for (auto declarator : syntax.declarators) {
        auto variable = compilation.emplace<VariableSymbol>(declarator->name.valueText(),
                                                            declarator->name.location());
        variable->setDeclaredType(*syntax.type);
        variable->setFromDeclarator(*declarator);
        results.append(variable);
    }
}

VariableSymbol& VariableSymbol::fromSyntax(Compilation& compilation,
                                           const ForVariableDeclarationSyntax& syntax) {
    auto var = compilation.emplace<VariableSymbol>(syntax.declarator->name.valueText(),
                                                   syntax.declarator->name.location());
    var->setDeclaredType(*syntax.type);
    var->setFromDeclarator(*syntax.declarator);
    return *var;
}

void VariableSymbol::toJson(json& j) const {
    j["lifetime"] = toString(lifetime);
    j["isConst"] = isConst;
}

void FormalArgumentSymbol::toJson(json& j) const {
    VariableSymbol::toJson(j);
    j["direction"] = toString(direction);
}

SubroutineSymbol& SubroutineSymbol::fromSyntax(Compilation& compilation,
                                               const FunctionDeclarationSyntax& syntax,
                                               const Scope& parent) {
    // TODO: non simple names?
    auto proto = syntax.prototype;
    Token nameToken = proto->name->getFirstToken();

    auto result = compilation.emplace<SubroutineSymbol>(
        compilation, nameToken.valueText(), nameToken.location(),
        SemanticFacts::getVariableLifetime(proto->lifetime).value_or(VariableLifetime::Automatic),
        syntax.kind == SyntaxKind::TaskDeclaration, parent);
    result->setSyntax(syntax);

    SmallVectorSized<const FormalArgumentSymbol*, 8> arguments;
    if (proto->portList) {
        const DataTypeSyntax* lastType = nullptr;
        auto lastDirection = FormalArgumentDirection::In;

        for (const FunctionPortSyntax* portSyntax : proto->portList->ports) {
            FormalArgumentDirection direction;
            bool directionSpecified = true;
            switch (portSyntax->direction.kind) {
                case TokenKind::InputKeyword:
                    direction = FormalArgumentDirection::In;
                    break;
                case TokenKind::OutputKeyword:
                    direction = FormalArgumentDirection::Out;
                    break;
                case TokenKind::InOutKeyword:
                    direction = FormalArgumentDirection::InOut;
                    break;
                case TokenKind::RefKeyword:
                    if (portSyntax->constKeyword)
                        direction = FormalArgumentDirection::ConstRef;
                    else
                        direction = FormalArgumentDirection::Ref;
                    break;
                case TokenKind::Unknown:
                    // Otherwise, we "inherit" the previous argument
                    direction = lastDirection;
                    directionSpecified = false;
                    break;
                default:
                    THROW_UNREACHABLE;
            }

            auto declarator = portSyntax->declarator;
            auto arg = compilation.emplace<FormalArgumentSymbol>(
                declarator->name.valueText(), declarator->name.location(), direction);

            // If we're given a type, use that. Otherwise, if we were given a
            // direction, default to logic. Otherwise, use the last type.
            if (portSyntax->dataType) {
                arg->setDeclaredType(*portSyntax->dataType);
                lastType = portSyntax->dataType;
            }
            else if (directionSpecified || !lastType) {
                arg->setType(compilation.getLogicType());
                lastType = nullptr;
            }
            else {
                arg->setDeclaredType(*lastType);
            }

            arg->setFromDeclarator(*declarator);

            result->addMember(*arg);
            arguments.append(arg);
            lastDirection = direction;
        }
    }

    // The function gets an implicit variable inserted that represents the return value.
    // TODO: don't do this if returning void; also handle name collisions with this thing
    auto implicitReturnVar = compilation.emplace<VariableSymbol>(result->name, result->location);
    implicitReturnVar->setDeclaredType(*proto->returnType);
    result->addMember(*implicitReturnVar);
    result->returnValVar = implicitReturnVar;

    // TODO: mising return type
    result->arguments = arguments.copy(compilation);
    result->declaredReturnType.setTypeSyntax(*proto->returnType);
    result->setBody(syntax.items);
    return *result;
}

void SubroutineSymbol::toJson(json& j) const {
    j["returnType"] = getReturnType();
    j["defaultLifetime"] = toString(defaultLifetime);
    j["isTask"] = isTask;
}

ModportSymbol::ModportSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Modport, name, loc), Scope(compilation, this) {
}

ModportSymbol& ModportSymbol::fromSyntax(Compilation& compilation, const ModportItemSyntax& syntax,
                                         const Scope&) {
    auto& result = *compilation.emplace<ModportSymbol>(compilation, syntax.name.valueText(),
                                                       syntax.name.location());

    // TODO: handle port list
    return result;
}

ContinuousAssignSymbol::ContinuousAssignSymbol(const ExpressionSyntax& syntax) :
    Symbol(SymbolKind::ContinuousAssign, "", syntax.getFirstToken().location()) {

    setSyntax(syntax);
}

ContinuousAssignSymbol::ContinuousAssignSymbol(SourceLocation loc, const Expression& assignment) :
    Symbol(SymbolKind::ContinuousAssign, "", loc), assign(&assignment) {
}

const Expression& ContinuousAssignSymbol::getAssignment() const {
    if (assign)
        return *assign;

    auto scope = getScope();
    ASSERT(scope);

    auto syntax = getSyntax();
    ASSERT(syntax);

    // Parser has ensured that this is a proper variable assignment expression here.
    assign = &Expression::bind(syntax->as<ExpressionSyntax>(),
                               BindContext(*scope, LookupLocation::before(*this)));
    return *assign;
}

void ContinuousAssignSymbol::toJson(json& j) const {
    j["assignment"] = getAssignment();
}

} // namespace slang
