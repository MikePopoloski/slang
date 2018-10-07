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

        package_ = getScope()->getCompilation().getPackage(packageName);
        // TODO: errors, explicit imports, transparent members?
        if (package_)
            import = package_->find(importName);
    }
    return import;
}

void ExplicitImportSymbol::toJson(json& j) const {
    j["package"] = std::string(packageName);
}

const PackageSymbol* WildcardImportSymbol::getPackage() const {
    if (!package)
        package = getScope()->getCompilation().getPackage(packageName);
    return *package;
}

void WildcardImportSymbol::toJson(json& j) const {
    j["package"] = std::string(packageName);
}

ParameterSymbol::ParameterSymbol(string_view name, SourceLocation loc, bool isLocal, bool isPort) :
    ValueSymbol(SymbolKind::Parameter, name, loc,
                DeclaredTypeFlags::InferImplicit | DeclaredTypeFlags::RequireConstant),
    isLocal(isLocal), isPort(isPort) {
}

void ParameterSymbol::fromSyntax(Compilation& compilation, const ParameterDeclarationSyntax& syntax,
                                 bool isLocal, bool isPort,
                                 SmallVector<ParameterSymbol*>& results) {
    for (auto decl : syntax.declarators) {
        auto loc = decl->name.location();
        auto param =
            compilation.emplace<ParameterSymbol>(decl->name.valueText(), loc, isLocal, isPort);
        param->setDeclaredType(*syntax.type);
        param->setFromDeclarator(*decl);

        if (!decl->initializer) {
            if (!isPort)
                compilation.addDiag(*param, DiagCode::BodyParamNoInitializer, loc);
            else if (isLocal)
                compilation.addDiag(*param, DiagCode::LocalParamNoInitializer, loc);
        }

        param->setSyntax(*decl);
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
    overriden = scope->getCompilation().createConstant(std::move(value));
}

void ParameterSymbol::toJson(json& j) const {
    j["type"] = getType();
    j["value"] = getValue();
    j["isLocal"] = isLocalParam();
    j["isPort"] = isPortParam();
    j["isBody"] = isBodyParam();
}

namespace {

// Helper class to build up lists of port symbols.
struct AnsiPortListBuilder {
    Compilation& compilation;
    SmallVector<const PortSymbol*>& ports;

    PortKind lastKind = PortKind::Net;
    PortDirection lastDirection = PortDirection::InOut;
    const DataTypeSyntax* lastType = nullptr;
    const DefinitionSymbol* lastInterface = nullptr;

    AnsiPortListBuilder(Compilation& compilation, SmallVector<const PortSymbol*>& ports) :
        compilation(compilation), ports(ports) {}

    void add(const PortSymbol& port) {
        ports.append(&port);

        lastKind = port.portKind;
        lastDirection = port.direction;
        lastType = port.getDeclaredType()->getTypeSyntax();
        lastInterface = port.interfaceDef;

        if (lastDirection == PortDirection::NotApplicable)
            lastDirection = PortDirection::InOut;

        if (lastKind == PortKind::Explicit || lastKind == PortKind::Interface) {
            switch (lastDirection) {
                case PortDirection::In:
                case PortDirection::InOut:
                case PortDirection::Out:
                    // TODO: default nettype
                    lastKind = PortKind::Net;
                    break;
                case PortDirection::Ref:
                    lastKind = PortKind::Variable;
                    break;
                case PortDirection::NotApplicable:
                    THROW_UNREACHABLE;
            }
        }
    }
};

void copyTypeFrom(ValueSymbol& dest, const DeclaredType& source) {
    if (auto typeSyntax = source.getTypeSyntax()) {
        if (auto dims = source.getDimensionSyntax())
            dest.setDeclaredType(*typeSyntax, *dims);
        else
            dest.setDeclaredType(*typeSyntax);
    }

    if (source.isTypeResolved())
        dest.setType(source.getType());
}

void handleImplicitAnsiPort(const ImplicitAnsiPortSyntax& syntax, AnsiPortListBuilder& builder,
                            const Scope& scope) {
    Compilation& comp = builder.compilation;
    auto token = syntax.declarator->name;
    auto& port = *comp.emplace<PortSymbol>(token.valueText(), token.location());
    port.setSyntax(syntax);

    // Helper function to check if an implicit type syntax is totally empty.
    auto typeSyntaxEmpty = [](const DataTypeSyntax& typeSyntax) {
        if (typeSyntax.kind != SyntaxKind::ImplicitType)
            return false;

        const auto& implicitType = typeSyntax.as<ImplicitTypeSyntax>();
        return !implicitType.signing && implicitType.dimensions.empty();
    };

    // Helper function to set the port's direction and data type, which are both optional.
    auto setDirectionAndType = [&](const auto& header, const auto& dimensions) {
        port.setDeclaredType(*header.dataType, dimensions);
        if (!header.direction)
            port.direction = builder.lastDirection;
        else
            port.direction = SemanticFacts::getPortDirection(header.direction.kind);
    };

    switch (syntax.header->kind) {
        case SyntaxKind::VariablePortHeader: {
            auto& header = syntax.header->as<VariablePortHeaderSyntax>();
            if (!header.direction && !header.varKeyword && typeSyntaxEmpty(*header.dataType)) {
                // If all three are omitted, take all from the previous port.
                // TODO: default nettype?
                port.portKind = builder.lastKind;
                port.direction = builder.lastDirection;
                port.interfaceDef = builder.lastInterface;

                if (port.interfaceDef) {
                    port.portKind = PortKind::Interface;
                    // TODO: dimensions
                }
                else {
                    if (builder.lastType)
                        port.setDeclaredType(*builder.lastType, syntax.declarator->dimensions);
                    else
                        port.setDeclaredType(*header.dataType, syntax.declarator->dimensions);
                }
            }
            else {
                // It's possible that this is actually an interface port if the data type is just
                // an identifier. The only way to know is to do a lookup and see what comes back.
                const DefinitionSymbol* definition = nullptr;
                if (header.dataType->kind == SyntaxKind::NamedType) {
                    auto& namedType = header.dataType->as<NamedTypeSyntax>();
                    if (namedType.name->kind == SyntaxKind::IdentifierName) {
                        LookupResult lookupResult;
                        scope.lookupName(*namedType.name, LookupLocation::max, LookupNameKind::Type,
                                         LookupFlags::None, lookupResult);

                        if (lookupResult.hasError() || !lookupResult.found ||
                            !lookupResult.found->isType()) {
                            // Didn't find a valid type; try to find a definition.
                            auto name =
                                namedType.name->as<IdentifierNameSyntax>().identifier.valueText();
                            definition = comp.getDefinition(name, scope);
                        }
                    }
                }

                if (definition) {
                    // TODO: dimensions
                    port.portKind = PortKind::Interface;

                    if (definition->definitionKind != DefinitionKind::Interface) {
                        auto& diag = scope.addDiag(DiagCode::PortTypeNotInterfaceOrData,
                                                   header.dataType->sourceRange());
                        diag << definition->name;
                        diag.addNote(DiagCode::NoteDeclarationHere, definition->location);

                        port.interfaceDef = nullptr;
                    }
                    else {
                        port.interfaceDef = definition;

                        if (header.varKeyword) {
                            scope.addDiag(DiagCode::VarWithInterfacePort,
                                          header.varKeyword.location());
                        }

                        if (header.direction) {
                            scope.addDiag(DiagCode::DirectionWithInterfacePort,
                                          header.direction.location());
                        }
                    }
                }
                else {
                    // TODO: handle user defined nettypes here
                    setDirectionAndType(header, syntax.declarator->dimensions);
                    if (header.varKeyword)
                        port.portKind = PortKind::Variable;
                    else {
                        // Rules from [23.2.2.3]:
                        // - For input and inout, default to a net
                        // - For output, if we have a data type it's a var, otherwise net
                        // - For ref it's always a var
                        switch (port.direction) {
                            case PortDirection::In:
                            case PortDirection::InOut:
                                // TODO: default nettype
                                port.portKind = PortKind::Net;
                                break;
                            case PortDirection::Out:
                                if (header.dataType->kind == SyntaxKind::ImplicitType)
                                    port.portKind = PortKind::Net;
                                else
                                    port.portKind = PortKind::Variable;
                                break;
                            case PortDirection::Ref:
                                port.portKind = PortKind::Variable;
                                break;
                            case PortDirection::NotApplicable:
                                THROW_UNREACHABLE;
                        }
                    }

                    if (port.direction == PortDirection::InOut &&
                        port.portKind == PortKind::Variable) {

                        scope.addDiag(DiagCode::InOutPortCannotBeVariable, port.location)
                            << port.name;
                    }
                    else if (port.direction == PortDirection::Ref &&
                             port.portKind != PortKind::Variable) {
                        scope.addDiag(DiagCode::RefPortMustBeVariable, port.location) << port.name;
                    }
                }
            }

            if (port.portKind == PortKind::Interface) {
                port.direction = PortDirection::NotApplicable;
            }
            else {
                // Create a new symbol to represent this port internally to the instance.
                // TODO: interconnect ports don't have a datatype
                // TODO: variable lifetime
                auto variable =
                    comp.emplace<VariableSymbol>(port.name, syntax.declarator->name.location());
                variable->setSyntax(syntax);
                copyTypeFrom(*variable, *port.getDeclaredType());
                port.internalSymbol = variable;

                // Initializers here are evaluated in the context of the port list and
                // must always be a constant value.
                // TODO: handle initializers
            }
            break;
        }
        case SyntaxKind::NetPortHeader: {
            auto& header = syntax.header->as<NetPortHeaderSyntax>();
            port.portKind = PortKind::Net;
            setDirectionAndType(header, syntax.declarator->dimensions);

            if (port.direction == PortDirection::Ref)
                scope.addDiag(DiagCode::RefPortMustBeVariable, port.location) << port.name;

            // Create a new symbol to represent this port internally to the instance.
            // TODO: net type
            auto net = comp.emplace<NetSymbol>(port.name, syntax.declarator->name.location());
            net->setSyntax(syntax);
            copyTypeFrom(*net, *port.getDeclaredType());
            port.internalSymbol = net;
            break;
        }
        case SyntaxKind::InterfacePortHeader: {
            // TODO: handle generic interface header
            auto& header = syntax.header->as<InterfacePortHeaderSyntax>();
            port.portKind = PortKind::Interface;
            port.direction = PortDirection::NotApplicable;

            port.interfaceDef = comp.getDefinition(header.nameOrKeyword.valueText(), scope);
            if (!port.interfaceDef) {
                // TODO: report error if unable to find definition
            }
            else if (port.interfaceDef->definitionKind != DefinitionKind::Interface) {
                // TODO: report error here
                /*auto& diag = scope.addDiag(DiagCode::PortTypeNotInterfaceOrData,
                                            header.dataType->sourceRange());
                diag << definition->name;
                diag.addNote(DiagCode::NoteDeclarationHere, definition->location);*/
                port.interfaceDef = nullptr;
            }
            else if (header.modport && !header.modport->member.valueText().empty()) {
                // TODO: error if unfound or not actually a modport
                // TODO: handle arrays
                auto member = header.modport->member;
                auto symbol = port.interfaceDef->find(member.valueText());
                if (!symbol) {
                    auto& diag = scope.addDiag(DiagCode::UnknownMember, member.range());
                    diag << member.valueText();
                    diag << port.interfaceDef->name;
                }
                else if (symbol->kind != SymbolKind::Modport) {
                    auto& diag = scope.addDiag(DiagCode::NotAModport, member.range());
                    diag << member.valueText();
                    diag.addNote(DiagCode::NoteDeclarationHere, symbol->location);
                }
                else {
                    port.modport = &symbol->as<ModportSymbol>();
                }
            }
            break;
        }
        default:
            // TODO:
            THROW_UNREACHABLE;
    }

    builder.add(port);
}

struct NonAnsiPortListBuilder {
    Compilation& compilation;
    SmallVector<const PortSymbol*>& ports;

    struct PortInfo {
        const VariableDeclaratorSyntax* syntax = nullptr;
        const Symbol* internalSymbol = nullptr;
        PortDirection direction;
        PortKind kind;
        bool used = false;

        PortInfo(const VariableDeclaratorSyntax* syntax) : syntax(syntax) {}
    };
    SmallMap<string_view, PortInfo, 8> portInfos;

    NonAnsiPortListBuilder(Compilation& compilation, SmallVector<const PortSymbol*>& ports,
                           const Scope& scope,
                           span<const PortDeclarationSyntax* const> portDeclarations) :
        compilation(compilation),
        ports(ports) {
        // All port declarations in the scope have been collected; index them for easy lookup.
        // The additional boolean is for tracking whether the declaration has been used by the
        // time we're done creating ports.
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

            // If the port has any kind of type declared, this constitutes a full symbol definition.
            // Otherwise we need to see if there's an existing symbol to match with.
            if (varHeader.varKeyword || varHeader.dataType->kind != SyntaxKind::ImplicitType) {
                // TODO: check for user defined net type?
                info.kind = PortKind::Variable;

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
                info.kind =
                    symbol->kind == SymbolKind::Variable ? PortKind::Variable : PortKind::Net;
                info.internalSymbol = symbol;

                mergePortTypes(symbol->as<ValueSymbol>(),
                               varHeader.dataType->as<ImplicitTypeSyntax>(), declLoc, scope,
                               decl.dimensions);
            }
            else {
                // No symbol and no data type defaults to a basic net.
                info.kind = PortKind::Net;

                // TODO: net type
                auto net = compilation.emplace<NetSymbol>(name, declLoc);
                net->setSyntax(decl);
                net->setDeclaredType(*varHeader.dataType, decl.dimensions);
                info.internalSymbol = net;
            }

            if (info.direction == PortDirection::InOut && info.kind == PortKind::Variable)
                scope.addDiag(DiagCode::InOutPortCannotBeVariable, declLoc) << name;
            else if (info.direction == PortDirection::Ref && info.kind != PortKind::Variable)
                scope.addDiag(DiagCode::RefPortMustBeVariable, declLoc) << name;

            break;
        }
        case SyntaxKind::NetPortHeader: {
            auto& netHeader = header.as<NetPortHeaderSyntax>();
            info.kind = PortKind::Net;
            info.direction = SemanticFacts::getPortDirection(netHeader.direction.kind);

            if (info.direction == PortDirection::Ref)
                scope.addDiag(DiagCode::RefPortMustBeVariable, declLoc) << name;

            // Create a new symbol to represent this port internally to the instance.
            // TODO: net type
            auto net = compilation.emplace<NetSymbol>(name, declLoc);
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

            port.direction = info->direction;
            port.portKind = info->kind;
            port.internalSymbol = info->internalSymbol;

            ASSERT(info->internalSymbol);
            copyTypeFrom(port, *info->internalSymbol->getDeclaredType());
            break;
        }
        default:
            // TODO: handle concatenations
            THROW_UNREACHABLE;
    }
}

} // end anonymous namespace

void PortSymbol::fromSyntax(Compilation& compilation, const PortListSyntax& syntax,
                            const Scope& scope, SmallVector<const PortSymbol*>& results,
                            span<const PortDeclarationSyntax* const> portDeclarations) {
    switch (syntax.kind) {
        case SyntaxKind::AnsiPortList: {
            // TODO: error if we have port declaration members
            AnsiPortListBuilder builder{ compilation, results };
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
            NonAnsiPortListBuilder builder{ compilation, results, scope, portDeclarations };
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

void PortSymbol::toJson(json&) const {
    // TODO: implement this
}

void NetSymbol::fromSyntax(Compilation& compilation, const NetDeclarationSyntax& syntax,
                           SmallVector<const NetSymbol*>& results) {
    for (auto declarator : syntax.declarators) {
        auto net = compilation.emplace<NetSymbol>(declarator->name.valueText(),
                                                  declarator->name.location());

        // TODO: net types, initializers, etc
        net->setDeclaredType(*syntax.type, declarator->dimensions);
        net->setSyntax(*declarator);
        results.append(net);
    }
}

void NetSymbol::toJson(json&) const {
    // TODO:
    // j["dataType"] = *dataType;
}

void VariableSymbol::fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                                SmallVector<const VariableSymbol*>& results) {
    for (auto declarator : syntax.declarators) {
        auto variable = compilation.emplace<VariableSymbol>(declarator->name.valueText(),
                                                            declarator->name.location());
        variable->setDeclaredType(*syntax.type);
        variable->setFromDeclarator(*declarator);
        variable->setSyntax(*declarator);
        results.append(variable);
    }
}

VariableSymbol& VariableSymbol::fromSyntax(Compilation& compilation,
                                           const ForVariableDeclarationSyntax& syntax) {
    auto var = compilation.emplace<VariableSymbol>(syntax.declarator->name.valueText(),
                                                   syntax.declarator->name.location());
    var->setDeclaredType(*syntax.type);
    var->setFromDeclarator(*syntax.declarator);
    var->setSyntax(*syntax.declarator);
    return *var;
}

void VariableSymbol::toJson(json& j) const {
    j["type"] = getType();
    j["lifetime"] = lifetime; // TODO: tostring
    j["isConst"] = isConst;

    // TODO:
    // if (initializer)
    //    j["initializer"] =
}

void FormalArgumentSymbol::toJson(json& j) const {
    VariableSymbol::toJson(j);
    j["direction"] = direction; // TODO: tostring
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
            arg->setSyntax(*portSyntax);

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
    j["defaultLifetime"] = defaultLifetime; // TODO: tostring
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

} // namespace slang
