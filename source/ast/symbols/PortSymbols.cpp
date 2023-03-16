//------------------------------------------------------------------------------
// PortSymbols.cpp
// Contains port-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/PortSymbols.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/Definition.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/symbols/AttributeSymbol.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/NetType.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxFacts.h"
#include "slang/util/StackContainer.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

namespace {

const NetType& getDefaultNetType(const Scope& scope, SourceLocation location) {
    auto& netType = scope.getDefaultNetType();
    if (!netType.isError())
        return netType;

    scope.addDiag(diag::ImplicitNetPortNoDefault, location);
    return scope.getCompilation().getWireNetType();
}

std::tuple<const Definition*, string_view> getInterfacePortInfo(
    const Scope& scope, const InterfacePortHeaderSyntax& header) {

    auto& comp = scope.getCompilation();
    auto token = header.nameOrKeyword;
    auto def = comp.getDefinition(token.valueText(), scope);
    string_view modport;

    if (!def) {
        scope.addDiag(diag::UnknownInterface, token.range()) << token.valueText();
    }
    else if (def->definitionKind != DefinitionKind::Interface) {
        auto& diag = scope.addDiag(diag::PortTypeNotInterfaceOrData, header.nameOrKeyword.range());
        diag << def->name;
        diag.addNote(diag::NoteDeclarationHere, def->location);
        def = nullptr;
    }
    else if (header.modport) {
        auto member = header.modport->member;
        modport = member.valueText();
        if (auto it = def->modports.find(modport); it == def->modports.end() && !modport.empty()) {
            auto& diag = scope.addDiag(diag::NotAModport, member.range());
            diag << modport;
            diag << def->name;
            modport = {};
        }
    }

    return {def, modport};
}

// This checks factors other than types when making a port connection
// to a specific symbol.
void checkSymbolConnection(const Expression& expr, ArgumentDirection direction,
                           const ASTContext& context, SourceLocation loc,
                           bitmask<AssignFlags> flags) {
    switch (direction) {
        case ArgumentDirection::In:
            // All expressions are fine for inputs.
            break;
        case ArgumentDirection::Out:
            expr.requireLValue(context, loc, flags);
            break;
        case ArgumentDirection::InOut:
            expr.requireLValue(context, loc, AssignFlags::InOutPort);
            break;
        case ArgumentDirection::Ref:
            if (!expr.canConnectToRefArg(/* isConstRef */ false))
                context.addDiag(diag::InvalidRefArg, loc) << expr.sourceRange;
            break;
    }
}

// Helper class to build up lists of port symbols.
class AnsiPortListBuilder {
public:
    AnsiPortListBuilder(const Scope& scope,
                        SmallVectorBase<std::pair<Symbol*, const Symbol*>>& implicitMembers) :
        comp(scope.getCompilation()),
        scope(scope), implicitMembers(implicitMembers) {}

    Symbol* createPort(const ImplicitAnsiPortSyntax& syntax) {
        // Helper function to check if an implicit type syntax is totally empty.
        auto isEmpty = [](const DataTypeSyntax& typeSyntax) {
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
                if (!header.direction && !header.varKeyword && isEmpty(*header.dataType))
                    return addInherited(decl, syntax.attributes);

                // It's possible that this is actually an interface port if the data type is just an
                // identifier. The only way to know is to do a lookup and see what comes back.
                string_view simpleName = SyntaxFacts::getSimpleTypeName(*header.dataType);
                if (!simpleName.empty()) {
                    auto found = Lookup::unqualified(scope, simpleName, LookupFlags::Type);
                    if (found && found->kind == SymbolKind::NetType) {
                        return add(decl, getDirection(header.direction), nullptr,
                                   &found->as<NetType>(), syntax.attributes);
                    }

                    // If we didn't find a valid type, try to find a definition.
                    if (!found || !found->isType()) {
                        if (auto definition = comp.getDefinition(simpleName, scope)) {
                            if (definition->definitionKind != DefinitionKind::Interface) {
                                auto& diag = scope.addDiag(diag::PortTypeNotInterfaceOrData,
                                                           header.dataType->sourceRange());
                                diag << definition->name;
                                diag.addNote(diag::NoteDeclarationHere, definition->location);
                                definition = nullptr;
                            }
                            else {
                                if (header.varKeyword) {
                                    scope.addDiag(diag::VarWithInterfacePort,
                                                  header.varKeyword.location());
                                }

                                if (header.direction) {
                                    scope.addDiag(diag::DirectionWithInterfacePort,
                                                  header.direction.location());
                                }
                            }

                            return add(decl, definition, ""sv, /* isGeneric */ false,
                                       syntax.attributes);
                        }
                    }
                }

                // Rules from [23.2.2.3]:
                // - If we have a var keyword, it's a var
                // - For input and inout, default to a net
                // - For output, if we have a data type it's a var, otherwise net
                // - For ref it's always a var
                //
                // Unfortunately, all major simulators ignore the rule for input ports,
                // and treat them the same as output ports (i.e. it's not a net if there
                // is a data type specified). This is pretty noticeable as otherwise a
                // port like this:
                //    input int i
                // will throw an error because int is not a valid type for a net. Actually
                // noticing the other fact, that it's a net port vs a variable port, is very
                // hard to do, so we go along with everyone else and use the same rule.

                ArgumentDirection direction = getDirection(header.direction);
                const NetType* netType = nullptr;
                if (!header.varKeyword && (direction == ArgumentDirection::InOut ||
                                           (direction != ArgumentDirection::Ref &&
                                            header.dataType->kind == SyntaxKind::ImplicitType))) {
                    netType = &getDefaultNetType(scope, decl.name.location());
                }

                return add(decl, direction, header.dataType, netType, syntax.attributes);
            }
            case SyntaxKind::NetPortHeader: {
                auto& header = syntax.header->as<NetPortHeaderSyntax>();
                return add(decl, getDirection(header.direction), header.dataType,
                           &comp.getNetType(header.netType.kind), syntax.attributes);
            }
            case SyntaxKind::InterfacePortHeader: {
                auto& header = syntax.header->as<InterfacePortHeaderSyntax>();
                if (header.nameOrKeyword.kind == TokenKind::InterfaceKeyword) {
                    string_view modport;
                    if (header.modport)
                        modport = header.modport->member.valueText();
                    return add(decl, nullptr, modport, /* isGeneric */ true, syntax.attributes);
                }

                auto [definition, modport] = getInterfacePortInfo(scope, header);
                return add(decl, definition, modport, /* isGeneric */ false, syntax.attributes);
            }
            default:
                ASSUME_UNREACHABLE;
        }
    }

    Symbol* createPort(const ExplicitAnsiPortSyntax& syntax) {
        auto port = comp.emplace<PortSymbol>(syntax.name.valueText(), syntax.name.location(),
                                             /* isAnsiPort */ true);
        port->direction = getDirection(syntax.direction);
        port->setSyntax(syntax);
        port->setAttributes(scope, syntax.attributes);

        if (!syntax.expr)
            port->isNullPort = true;

        lastDirection = port->direction;
        lastType = nullptr;
        lastNetType = nullptr;
        lastInterface = nullptr;
        lastModport = ""sv;
        lastGenericIface = false;

        return port;
    }

private:
    ArgumentDirection getDirection(Token token) const {
        return token ? SemanticFacts::getDirection(token.kind) : lastDirection;
    }

    Symbol* addInherited(const DeclaratorSyntax& decl,
                         span<const AttributeInstanceSyntax* const> attrs) {
        if (lastInterface || lastGenericIface)
            return add(decl, lastInterface, lastModport, lastGenericIface, attrs);

        if (!lastType && !lastNetType)
            lastType = &comp.createEmptyTypeSyntax(decl.getFirstToken().location());

        return add(decl, lastDirection, lastType, lastNetType, attrs);
    }

    Symbol* add(const DeclaratorSyntax& decl, ArgumentDirection direction,
                const DataTypeSyntax* type, const NetType* netType,
                span<const AttributeInstanceSyntax* const> attrs) {
        auto port = comp.emplace<PortSymbol>(decl.name.valueText(), decl.name.location(),
                                             /* isAnsiPort */ true);
        port->direction = direction;
        port->setSyntax(decl);
        port->setAttributes(scope, attrs);

        if (!port->name.empty()) {
            if (port->direction == ArgumentDirection::InOut && !netType) {
                scope.addDiag(diag::InOutPortCannotBeVariable, port->location) << port->name;
            }
            else if (port->direction == ArgumentDirection::InOut &&
                     netType->netKind == NetType::UWire) {
                scope.addDiag(diag::InOutUWirePort, port->location) << port->name;
            }
            else if (port->direction == ArgumentDirection::Ref && netType) {
                scope.addDiag(diag::RefPortMustBeVariable, port->location) << port->name;
            }
        }

        // Create a new symbol to represent this port internally to the instance.
        ValueSymbol* symbol;
        if (netType) {
            symbol = comp.emplace<NetSymbol>(port->name, port->location, *netType);
        }
        else {
            symbol = comp.emplace<VariableSymbol>(port->name, port->location,
                                                  VariableLifetime::Static);
        }

        if (type) {
            symbol->setDeclaredType(*type, decl.dimensions);
        }
        else {
            ASSERT(netType);
            if (!decl.dimensions.empty())
                symbol->getDeclaredType()->setDimensionSyntax(decl.dimensions);
        }

        symbol->setSyntax(decl);
        symbol->setAttributes(scope, attrs);
        port->internalSymbol = symbol;
        implicitMembers.emplace_back(symbol, port);

        if (decl.initializer) {
            if (netType && netType->netKind == NetType::Interconnect) {
                scope.addDiag(diag::InterconnectInitializer, decl.initializer->sourceRange());
            }
            else {
                port->setInitializerSyntax(*decl.initializer->expr,
                                           decl.initializer->equals.location());
            }
        }

        // Remember the properties of this port in case the next port wants to inherit from it.
        lastDirection = direction;
        lastType = type;
        lastNetType = netType;
        lastInterface = nullptr;
        lastModport = ""sv;
        lastGenericIface = false;

        return port;
    }

    Symbol* add(const DeclaratorSyntax& decl, const Definition* iface, string_view modport,
                bool isGeneric, span<const AttributeInstanceSyntax* const> attrs) {
        auto port = comp.emplace<InterfacePortSymbol>(decl.name.valueText(), decl.name.location());
        port->interfaceDef = iface;
        port->modport = modport;
        port->isGeneric = isGeneric;
        port->setSyntax(decl);
        port->setAttributes(scope, attrs);

        if (decl.initializer)
            scope.addDiag(diag::AnsiIfacePortDefault, decl.initializer->sourceRange());

        lastDirection = ArgumentDirection::InOut;
        lastType = nullptr;
        lastNetType = nullptr;
        lastInterface = iface;
        lastModport = modport;
        lastGenericIface = isGeneric;

        return port;
    }

    Compilation& comp;
    const Scope& scope;
    SmallVectorBase<std::pair<Symbol*, const Symbol*>>& implicitMembers;

    ArgumentDirection lastDirection = ArgumentDirection::InOut;
    const DataTypeSyntax* lastType = nullptr;
    const NetType* lastNetType = nullptr;
    const Definition* lastInterface = nullptr;
    string_view lastModport;
    bool lastGenericIface = false;
};

class NonAnsiPortListBuilder {
public:
    NonAnsiPortListBuilder(const Scope& scope,
                           span<std::pair<const SyntaxNode*, const Symbol*> const> portDeclarations,
                           SmallVectorBase<std::pair<Symbol*, const Symbol*>>& implicitMembers) :
        comp(scope.getCompilation()),
        scope(scope), implicitMembers(implicitMembers) {

        // All port declarations in the scope have been collected; index them for easy lookup.
        for (auto [syntax, insertionPoint] : portDeclarations) {
            if (syntax->kind == SyntaxKind::PortDeclaration) {
                auto& port = syntax->as<PortDeclarationSyntax>();
                for (auto decl : port.declarators) {
                    if (auto name = decl->name; !name.isMissing()) {
                        auto [it, inserted] = portInfos.emplace(name.valueText(),
                                                                PortInfo{*decl, port.attributes});

                        if (inserted) {
                            it->second.insertionPoint = insertionPoint;
                            handleIODecl(*port.header, it->second);
                        }
                        else {
                            auto& diag = scope.addDiag(diag::Redefinition, name.location());
                            diag << name.valueText();
                            diag.addNote(diag::NotePreviousDefinition,
                                         it->second.syntax->name.location());
                        }
                    }
                }
            }
            else {
                auto& data = syntax->as<DataDeclarationSyntax>();
                auto& namedType = data.type->as<NamedTypeSyntax>();
                auto typeName = namedType.name->as<IdentifierNameSyntax>().identifier.valueText();
                auto def = comp.getDefinition(typeName, scope);

                ASSERT(def && def->definitionKind == DefinitionKind::Interface);

                for (auto decl : data.declarators) {
                    if (auto name = decl->name; !name.isMissing()) {
                        auto [it, inserted] = portInfos.emplace(name.valueText(),
                                                                PortInfo{*decl, data.attributes});

                        if (inserted) {
                            auto& info = it->second;
                            info.isIface = true;
                            info.ifaceDef = def;
                            info.insertionPoint = insertionPoint;

                            if (decl->initializer) {
                                scope.addDiag(diag::DisallowedPortDefault,
                                              decl->initializer->sourceRange());
                            }
                        }
                        else {
                            auto& diag = scope.addDiag(diag::Redefinition, name.location());
                            diag << name.valueText();
                            diag.addNote(diag::NotePreviousDefinition,
                                         it->second.syntax->name.location());
                        }
                    }
                }
            }
        }
    }

    Symbol* createPort(const ImplicitNonAnsiPortSyntax& syntax) {
        auto loc = syntax.expr->getFirstToken().location();
        switch (syntax.expr->kind) {
            case SyntaxKind::PortReference:
                return &createPort(""sv, loc, syntax.expr->as<PortReferenceSyntax>());
            case SyntaxKind::PortConcatenation:
                return &createPort(""sv, loc, syntax.expr->as<PortConcatenationSyntax>());
            default:
                ASSUME_UNREACHABLE;
        }
    }

    Symbol* createPort(const ExplicitNonAnsiPortSyntax& syntax) {
        auto name = syntax.name.valueText();
        auto loc = syntax.name.location();

        if (!syntax.expr) {
            auto port = comp.emplace<PortSymbol>(name, loc, /* isAnsiPort */ false);
            port->direction = ArgumentDirection::In;
            port->setSyntax(syntax);
            port->isNullPort = true;
            return port;
        }

        switch (syntax.expr->kind) {
            case SyntaxKind::PortReference:
                return &createPort(name, loc, syntax.expr->as<PortReferenceSyntax>());
            case SyntaxKind::PortConcatenation:
                return &createPort(name, loc, syntax.expr->as<PortConcatenationSyntax>());
            default:
                ASSUME_UNREACHABLE;
        }
    }

    Symbol* createPort(const EmptyNonAnsiPortSyntax& syntax) {
        auto port = comp.emplace<PortSymbol>("", syntax.placeholder.location(),
                                             /* isAnsiPort */ false);
        port->direction = ArgumentDirection::In;
        port->setSyntax(syntax);
        port->isNullPort = true;
        return port;
    }

    void finalize() {
        // Error if any port declarations are unused.
        for (auto& [name, info] : portInfos) {
            if (!info.used)
                scope.addDiag(diag::UnusedPortDecl, info.syntax->sourceRange()) << name;
        }
    }

private:
    Compilation& comp;
    const Scope& scope;
    SmallVectorBase<std::pair<Symbol*, const Symbol*>>& implicitMembers;

    struct PortInfo {
        not_null<const DeclaratorSyntax*> syntax;
        span<const AttributeInstanceSyntax* const> attrs;
        const Symbol* internalSymbol = nullptr;
        const Symbol* insertionPoint = nullptr;
        const Definition* ifaceDef = nullptr;
        string_view modport;
        ArgumentDirection direction = ArgumentDirection::In;
        bool used = false;
        bool isIface = false;

        PortInfo(const DeclaratorSyntax& syntax, span<const AttributeInstanceSyntax* const> attrs) :
            syntax(&syntax), attrs(attrs) {}
    };
    SmallMap<string_view, PortInfo, 8> portInfos;

    void handleIODecl(const PortHeaderSyntax& header, PortInfo& info) {
        auto& decl = *info.syntax;
        auto name = decl.name.valueText();
        auto declLoc = decl.name.location();

        ASSERT(!name.empty());

        switch (header.kind) {
            case SyntaxKind::VariablePortHeader: {
                auto& varHeader = header.as<VariablePortHeaderSyntax>();
                info.direction = SemanticFacts::getDirection(varHeader.direction.kind);

                if (varHeader.constKeyword)
                    scope.addDiag(diag::ConstPortNotAllowed, varHeader.constKeyword.range());

                // If the port has any kind of type declared, this constitutes a full symbol
                // definition. Otherwise we need to see if there's an existing symbol to match with.
                if (varHeader.varKeyword || varHeader.dataType->kind != SyntaxKind::ImplicitType) {
                    if (!varHeader.varKeyword) {
                        auto typeName = SyntaxFacts::getSimpleTypeName(*varHeader.dataType);
                        auto result = Lookup::unqualified(scope, typeName, LookupFlags::Type);
                        if (result && result->kind == SymbolKind::NetType) {
                            auto net = comp.emplace<NetSymbol>(name, declLoc,
                                                               result->as<NetType>());
                            setInternalSymbol(*net, decl, nullptr, info);
                            break;
                        }
                    }

                    auto variable = comp.emplace<VariableSymbol>(name, declLoc,
                                                                 VariableLifetime::Static);
                    setInternalSymbol(*variable, decl, varHeader.dataType, info);
                }
                else if (auto symbol = scope.find(name);
                         symbol && (symbol->kind == SymbolKind::Variable ||
                                    symbol->kind == SymbolKind::Net)) {
                    // Port kind and type come from the matching symbol. Unfortunately
                    // that means we need to merge our own type info with whatever is
                    // declared for that symbol, so we need this ugly const_cast here.
                    info.internalSymbol = symbol;
                    ValueSymbol& val = const_cast<ValueSymbol&>(symbol->as<ValueSymbol>());

                    // If the I/O declaration is located prior to the symbol, we should update
                    // its index so that lookups in between will resolve correctly.
                    uint32_t ioIndex = info.insertionPoint
                                           ? uint32_t(info.insertionPoint->getIndex()) + 1
                                           : 1;
                    if (uint32_t(symbol->getIndex()) > ioIndex) {
                        val.getDeclaredType()->setOverrideIndex(symbol->getIndex());
                        val.setIndex(SymbolIndex(ioIndex));
                    }

                    val.getDeclaredType()->mergeImplicitPort(
                        varHeader.dataType->as<ImplicitTypeSyntax>(), declLoc, decl.dimensions);
                }
                else {
                    // No symbol and no data type defaults to a basic net.
                    auto net = comp.emplace<NetSymbol>(name, declLoc,
                                                       getDefaultNetType(scope, declLoc));
                    setInternalSymbol(*net, decl, varHeader.dataType, info);
                }

                if (info.direction == ArgumentDirection::InOut &&
                    info.internalSymbol->kind != SymbolKind::Net) {
                    scope.addDiag(diag::InOutPortCannotBeVariable, declLoc) << name;
                }
                break;
            }
            case SyntaxKind::NetPortHeader: {
                auto& netHeader = header.as<NetPortHeaderSyntax>();
                info.direction = SemanticFacts::getDirection(netHeader.direction.kind);

                // Create a new symbol to represent this port internally to the instance.
                auto net = comp.emplace<NetSymbol>(name, declLoc,
                                                   comp.getNetType(netHeader.netType.kind));
                setInternalSymbol(*net, decl, netHeader.dataType, info);
                break;
            }
            case SyntaxKind::InterfacePortHeader: {
                auto& ifaceHeader = header.as<InterfacePortHeaderSyntax>();
                auto [definition, modport] = getInterfacePortInfo(scope, ifaceHeader);
                ASSERT(ifaceHeader.nameOrKeyword.kind == TokenKind::Identifier);
                info.isIface = true;
                info.ifaceDef = definition;
                info.modport = modport;

                if (decl.initializer)
                    scope.addDiag(diag::DisallowedPortDefault, decl.initializer->sourceRange());

                break;
            }
            default:
                ASSUME_UNREACHABLE;
        }

        const bool isNet = info.internalSymbol && info.internalSymbol->kind == SymbolKind::Net;
        if (info.direction == ArgumentDirection::Ref && isNet)
            scope.addDiag(diag::RefPortMustBeVariable, declLoc) << name;

        if (info.direction == ArgumentDirection::InOut && isNet &&
            info.internalSymbol->as<NetSymbol>().netType.netKind == NetType::UWire) {
            scope.addDiag(diag::InOutUWirePort, declLoc) << name;
        }

        if ((info.direction != ArgumentDirection::Out || isNet) && decl.initializer)
            scope.addDiag(diag::DisallowedPortDefault, decl.initializer->sourceRange());
    }

    void setInternalSymbol(ValueSymbol& symbol, const DeclaratorSyntax& decl,
                           const DataTypeSyntax* dataType, PortInfo& info) {
        symbol.setSyntax(decl);
        symbol.setAttributes(scope, info.attrs);
        implicitMembers.emplace_back(&symbol, info.insertionPoint);
        info.internalSymbol = &symbol;

        if (dataType)
            symbol.setDeclaredType(*dataType, decl.dimensions);
        else if (!decl.dimensions.empty())
            symbol.getDeclaredType()->setDimensionSyntax(decl.dimensions);

        if (info.insertionPoint)
            symbol.getDeclaredType()->setOverrideIndex(info.insertionPoint->getIndex());
    }

    Symbol& createPort(string_view externalName, SourceLocation externalLoc,
                       const PortReferenceSyntax& syntax) {
        auto name = syntax.name.valueText();
        if (externalName.empty() && !syntax.select)
            externalName = name;

        auto it = portInfos.find(name);
        if (it == portInfos.end()) {
            if (!name.empty())
                scope.addDiag(diag::MissingPortIODeclaration, externalLoc) << name;

            auto port = comp.emplace<PortSymbol>(externalName, externalLoc, /* isAnsiPort */ false);
            port->setType(comp.getErrorType());
            return *port;
        }

        auto& info = it->second;
        info.used = true;

        auto loc = info.syntax->name.location();
        if (info.isIface) {
            // Interface ports should not have empty names. We'll be ignoring the
            // select if there is one (along with issuing an error) so just set the name.
            if (externalName.empty())
                externalName = name;

            if (syntax.select) {
                auto& diag = scope.addDiag(diag::IfacePortInExpr, syntax.select->sourceRange());
                diag << externalName;
            }

            auto port = comp.emplace<InterfacePortSymbol>(externalName, loc);
            port->setSyntax(*info.syntax);
            port->interfaceDef = info.ifaceDef;
            port->modport = info.modport;

            if (info.insertionPoint) {
                comp.setAttributes(
                    *port, AttributeSymbol::fromSyntax(
                               info.attrs, scope,
                               LookupLocation(&scope, (uint32_t)info.insertionPoint->getIndex())));
            }

            return *port;
        }

        auto port = comp.emplace<PortSymbol>(externalName, loc, /* isAnsiPort */ false);
        port->setSyntax(syntax);
        port->externalLoc = externalLoc;

        ASSERT(info.internalSymbol);
        port->direction = info.direction;
        port->internalSymbol = info.internalSymbol;

        if (auto init = info.syntax->initializer)
            port->setInitializerSyntax(*init->expr, init->equals.location());

        return *port;
    }

    Symbol& createPort(string_view name, SourceLocation externalLoc,
                       const PortConcatenationSyntax& syntax) {
        ArgumentDirection dir = ArgumentDirection::In;
        SmallVector<const PortSymbol*> buffer;
        bool allNets = true;
        bool allVars = true;
        bool hadError = false;

        auto reportDirError = [&](DiagCode code) {
            if (!hadError) {
                scope.addDiag(code, syntax.sourceRange());
                hadError = true;
            }
        };

        for (auto item : syntax.references) {
            auto& port = createPort(""sv, item->getFirstToken().location(), *item);
            if (port.kind == SymbolKind::Port) {
                auto& ps = port.as<PortSymbol>();
                auto sym = ps.internalSymbol;
                if (!sym)
                    continue;

                buffer.push_back(&ps);
                ps.setParent(scope);

                // We need to merge the port direction with all of the other component port
                // directions to come up with our "effective" direction, which is what we use
                // to create connection expressions. The rules here are not spelled out in the
                // LRM, but here's what I think makes sense based on other language rules:
                // - If all the directions are the same, that's the effective direction.
                // - inputs and outputs can be freely mixed; output direction dominates.
                // - if any port is ref, all ports must be variables. Effective direction is ref.
                // - if any port is inout, all ports must be nets. Effective direction is inout.
                // - ref and inout can never mix (implied by above two points).
                if (ps.direction == ArgumentDirection::InOut) {
                    dir = ArgumentDirection::InOut;
                    if (!allNets)
                        reportDirError(diag::PortConcatInOut);
                }
                else if (ps.direction == ArgumentDirection::Ref) {
                    dir = ArgumentDirection::Ref;
                    if (!allVars)
                        reportDirError(diag::PortConcatRef);
                }
                else if (ps.direction == ArgumentDirection::Out && dir == ArgumentDirection::In) {
                    dir = ArgumentDirection::Out;
                }

                if (sym->kind == SymbolKind::Net) {
                    allVars = false;
                    if (dir == ArgumentDirection::Ref)
                        reportDirError(diag::PortConcatRef);

                    auto& net = sym->as<NetSymbol>();
                    if (net.netType.netKind == NetType::UWire) {
                        // UWire nets aren't resolvable nets and so act like variables
                        // for the purposes of these checks.
                        allNets = false;
                        if (dir == ArgumentDirection::InOut)
                            reportDirError(diag::PortConcatInOut);
                    }
                    else if (net.netType.netKind == NetType::Interconnect) {
                        // Can't use interconnects in a port concat.
                        scope.addDiag(diag::InterconnectMultiPort, item->sourceRange());
                    }
                }
                else {
                    allNets = false;
                    if (dir == ArgumentDirection::InOut)
                        reportDirError(diag::PortConcatInOut);
                }
            }
            else {
                auto& diag = scope.addDiag(diag::IfacePortInExpr, item->sourceRange());
                diag << port.name;
            }
        }

        auto result = comp.emplace<MultiPortSymbol>(name, externalLoc, buffer.copy(comp), dir);
        result->setSyntax(syntax);
        return *result;
    }
};

class PortConnectionBuilder {
public:
    PortConnectionBuilder(const InstanceSymbol& instance,
                          const SeparatedSyntaxList<PortConnectionSyntax>& portConnections) :
        scope(*instance.getParentScope()),
        instance(instance), comp(scope.getCompilation()),
        lookupLocation(LookupLocation::after(instance)) {

        bool hasConnections = false;
        for (auto conn : portConnections) {
            bool isOrdered = conn->kind == SyntaxKind::OrderedPortConnection ||
                             conn->kind == SyntaxKind::EmptyPortConnection;
            if (!hasConnections) {
                hasConnections = true;
                usingOrdered = isOrdered;
            }
            else if (isOrdered != usingOrdered) {
                scope.addDiag(diag::MixingOrderedAndNamedPorts, conn->getFirstToken().location());
                break;
            }

            if (isOrdered) {
                orderedConns.push_back(conn);
            }
            else if (conn->kind == SyntaxKind::WildcardPortConnection) {
                if (!std::exchange(hasWildcard, true)) {
                    wildcardRange = conn->sourceRange();
                    wildcardAttrs = AttributeSymbol::fromSyntax(conn->attributes, scope,
                                                                lookupLocation);
                }
                else {
                    auto& diag = scope.addDiag(diag::DuplicateWildcardPortConnection,
                                               conn->sourceRange());
                    diag.addNote(diag::NotePreviousUsage, wildcardRange);
                }
            }
            else {
                auto& npc = conn->as<NamedPortConnectionSyntax>();
                auto name = npc.name.valueText();
                if (!name.empty()) {
                    auto pair = namedConns.emplace(name, std::make_pair(&npc, false));
                    if (!pair.second) {
                        auto& diag = scope.addDiag(diag::DuplicatePortConnection,
                                                   npc.name.location());
                        diag << name;
                        diag.addNote(diag::NotePreviousUsage,
                                     pair.first->second.first->name.location());
                    }
                }
            }
        }

        // Build up the set of dimensions for the instantiating instance's array parent, if any.
        // This builds up the dimensions in reverse order, so we have to reverse them back.
        auto parent = &scope;
        while (parent && parent->asSymbol().kind == SymbolKind::InstanceArray) {
            auto& sym = parent->asSymbol().as<InstanceArraySymbol>();
            instanceDims.push_back(sym.range);
            parent = sym.getParentScope();
        }
        std::reverse(instanceDims.begin(), instanceDims.end());
    }

    template<typename TPort>
    PortConnection* getConnection(const TPort& port) {
        auto reportUnconnected = [&] {
            if (port.direction == ArgumentDirection::Ref) {
                if (port.name.empty()) {
                    if (!unnamedRefError) {
                        auto& diag = scope.addDiag(diag::RefPortUnnamedUnconnected,
                                                   instance.location);
                        diag.addNote(diag::NoteDeclarationHere, port.location);
                        unnamedRefError = true;
                    }
                }
                else {
                    scope.addDiag(diag::RefPortUnconnected, instance.location) << port.name;
                }
            }
            else {
                if (port.name.empty()) {
                    if (!warnedAboutUnnamed) {
                        auto& diag = scope.addDiag(diag::UnconnectedUnnamedPort, instance.location);
                        diag.addNote(diag::NoteDeclarationHere, port.location);
                        warnedAboutUnnamed = true;
                    }
                }
                else {
                    scope.addDiag(diag::UnconnectedNamedPort, instance.location) << port.name;
                }
            }
            return emptyConnection(port);
        };

        const bool hasDefault = port.hasInitializer() && port.direction == ArgumentDirection::In;
        if (usingOrdered) {
            if (orderedIndex >= orderedConns.size()) {
                orderedIndex++;

                if (hasDefault)
                    return defaultConnection(port, {});

                return reportUnconnected();
            }

            const PortConnectionSyntax& pc = *orderedConns[orderedIndex++];
            auto attrs = AttributeSymbol::fromSyntax(pc.attributes, scope, lookupLocation);
            if (pc.kind == SyntaxKind::OrderedPortConnection)
                return createConnection(port, *pc.as<OrderedPortConnectionSyntax>().expr, attrs);
            else
                return defaultConnection(port, attrs);
        }

        if (port.name.empty()) {
            // port is unnamed so can never be connected by name
            return reportUnconnected();
        }

        auto it = namedConns.find(port.name);
        if (it == namedConns.end()) {
            if (hasWildcard)
                return implicitNamedPort(port, wildcardAttrs, wildcardRange, true);

            if (hasDefault)
                return defaultConnection(port, {});

            return reportUnconnected();
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
                return createConnection(port, *conn.expr, attrs);

            return emptyConnection(port);
        }

        return implicitNamedPort(port, attrs, conn.name.range(), false);
    }

    PortConnection* getIfaceConnection(const InterfacePortSymbol& port) {
        // If the port definition is empty it means an error already
        // occurred; there's no way to check this connection so early out.
        if (port.isInvalid() || port.name.empty()) {
            if (usingOrdered) {
                orderedIndex++;
            }
            else {
                auto it = namedConns.find(port.name);
                if (it != namedConns.end())
                    it->second.second = true;
            }
            return emptyConnection(port);
        }

        auto reportUnconnected = [&]() {
            auto& diag = scope.addDiag(diag::InterfacePortNotConnected, instance.location);
            diag << port.name;
            diag.addNote(diag::NoteDeclarationHere, port.location);
            return emptyConnection(port);
        };

        if (usingOrdered) {
            const PropertyExprSyntax* expr = nullptr;
            span<const AttributeSymbol* const> attributes;

            if (orderedIndex < orderedConns.size()) {
                const PortConnectionSyntax& pc = *orderedConns[orderedIndex];
                attributes = AttributeSymbol::fromSyntax(pc.attributes, scope, lookupLocation);
                if (pc.kind == SyntaxKind::OrderedPortConnection)
                    expr = pc.as<OrderedPortConnectionSyntax>().expr;
            }

            orderedIndex++;
            if (!expr)
                return reportUnconnected();

            return getInterfaceExpr(port, *expr, attributes);
        }

        auto it = namedConns.find(port.name);
        if (it == namedConns.end()) {
            if (hasWildcard)
                return getImplicitInterface(port, wildcardRange, wildcardAttrs);

            return reportUnconnected();
        }

        // We have a named connection; there are two possibilities here:
        // - An explicit connection (with an optional expression)
        // - An implicit connection, where we have to look up the name ourselves
        const NamedPortConnectionSyntax& conn = *it->second.first;
        it->second.second = true;

        auto attributes = AttributeSymbol::fromSyntax(conn.attributes, scope, lookupLocation);
        if (conn.openParen) {
            // For explicit named port connections, having an empty expression means no connection.
            if (!conn.expr)
                return reportUnconnected();

            return getInterfaceExpr(port, *conn.expr, attributes);
        }

        return getImplicitInterface(port, conn.name.range(), attributes);
    }

    void finalize() {
        if (usingOrdered) {
            if (orderedIndex < orderedConns.size()) {
                auto loc = orderedConns[orderedIndex]->getFirstToken().location();
                auto& diag = scope.addDiag(diag::TooManyPortConnections, loc);
                diag << instance.body.getDefinition().name;
                diag << orderedConns.size();
                diag << orderedIndex;
            }
        }
        else {
            for (auto& pair : namedConns) {
                // We marked all the connections that we used, so anything left over is a connection
                // for a non-existent port.
                if (!pair.second.second) {
                    auto& diag = scope.addDiag(diag::PortDoesNotExist,
                                               pair.second.first->name.location());
                    diag << pair.second.first->name.valueText();
                    diag << instance.body.getDefinition().name;
                }
            }
        }
    }

private:
    PortConnection* emptyConnection(const PortSymbol& port) {
        return comp.emplace<PortConnection>(port, instance);
    }

    PortConnection* emptyConnection(const MultiPortSymbol& port) {
        return comp.emplace<PortConnection>(port, instance);
    }

    PortConnection* emptyConnection(const InterfacePortSymbol& port) {
        return comp.emplace<PortConnection>(port, instance);
    }

    PortConnection* defaultConnection(const PortSymbol& port,
                                      span<const AttributeSymbol* const> attributes) {
        auto conn = comp.emplace<PortConnection>(port, instance, /* useDefault */ true);
        if (!attributes.empty())
            comp.setAttributes(*conn, attributes);

        return conn;
    }

    PortConnection* defaultConnection(const MultiPortSymbol& port,
                                      span<const AttributeSymbol* const> attributes) {
        auto conn = comp.emplace<PortConnection>(port, instance, /* useDefault */ false);
        if (!attributes.empty())
            comp.setAttributes(*conn, attributes);

        return conn;
    }

    template<typename TPort>
    PortConnection* createConnection(const TPort& port, const PropertyExprSyntax& syntax,
                                     span<const AttributeSymbol* const> attributes) {
        // If this is an empty port, it's an error to provide an expression.
        if (port.isNullPort) {
            auto& diag = scope.addDiag(diag::NullPortExpression, syntax.sourceRange());
            diag.addNote(diag::NoteDeclarationHere, port.location);
            return emptyConnection(port);
        }

        ASTContext context(scope, lookupLocation, ASTFlags::NonProcedural);
        auto exprSyntax = context.requireSimpleExpr(syntax);
        if (!exprSyntax)
            return emptyConnection(port);

        auto conn = comp.emplace<PortConnection>(port, instance, *exprSyntax);
        if (!attributes.empty())
            comp.setAttributes(*conn, attributes);

        return conn;
    }

    PortConnection* createConnection(const InterfacePortSymbol& port, const Symbol* ifaceInst,
                                     span<const AttributeSymbol* const> attributes) {
        auto conn = comp.emplace<PortConnection>(port, instance, ifaceInst);
        if (!attributes.empty())
            comp.setAttributes(*conn, attributes);

        return conn;
    }

    template<typename TPort>
    PortConnection* implicitNamedPort(const TPort& port,
                                      span<const AttributeSymbol* const> attributes,
                                      SourceRange range, bool isWildcard) {
        // An implicit named port connection is semantically equivalent to `.port(port)` except:
        // - Can't create implicit net declarations this way
        // - Port types need to be equivalent, not just assignment compatible
        // - An implicit connection between nets of two dissimilar net types shall issue an
        //   error when it is a warning in an explicit named port connection

        LookupFlags flags = isWildcard ? LookupFlags::DisallowWildcardImport : LookupFlags::None;
        auto symbol = Lookup::unqualified(scope, port.name, flags);
        if (!symbol) {
            // If this is a wildcard connection, we're allowed to use the port's default value,
            // if it has one.
            if (isWildcard && port.hasInitializer() && port.direction == ArgumentDirection::In)
                return defaultConnection(port, attributes);

            scope.addDiag(diag::ImplicitNamedPortNotFound, range) << port.name;
            return emptyConnection(port);
        }

        if (!symbol->isDeclaredBefore(lookupLocation).value_or(true)) {
            auto& diag = scope.addDiag(diag::UsedBeforeDeclared, range);
            diag << port.name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
        }

        auto conn = comp.emplace<PortConnection>(port, instance, symbol, range);
        if (!attributes.empty())
            comp.setAttributes(*conn, attributes);

        return conn;
    }

    PortConnection* getInterfaceExpr(const InterfacePortSymbol& port,
                                     const PropertyExprSyntax& syntax,
                                     span<const AttributeSymbol* const> attributes) {
        ASTContext context(scope, lookupLocation, ASTFlags::NonProcedural);
        auto expr = context.requireSimpleExpr(syntax);
        if (!expr)
            return emptyConnection(port);

        auto conn = getInterfaceConn(context, port, *expr);
        return createConnection(port, conn, attributes);
    }

    PortConnection* getImplicitInterface(const InterfacePortSymbol& port, SourceRange range,
                                         span<const AttributeSymbol* const> attributes) {
        auto symbol = Lookup::unqualified(scope, port.name);
        if (!symbol) {
            scope.addDiag(diag::ImplicitNamedPortNotFound, range) << port.name;
            return emptyConnection(port);
        }

        // This is a bit inefficient but it simplifies the implementation to just
        // wrap the name up in a fake expression and defer to the normal expression
        // handling connection path.
        Token id(comp, TokenKind::Identifier, {}, port.name, range.start());
        auto idName = comp.emplace<IdentifierNameSyntax>(id);

        ASTContext context(scope, lookupLocation, ASTFlags::NonProcedural);
        auto conn = getInterfaceConn(context, port, *idName);
        return createConnection(port, conn, attributes);
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

    const Symbol* getInterfaceConn(ASTContext& context, const InterfacePortSymbol& port,
                                   const ExpressionSyntax& syntax) {
        ASSERT(!port.isInvalid());

        auto portDims = port.getDeclaredRange();
        if (!portDims)
            return nullptr;

        auto expr = Expression::tryBindInterfaceRef(context, syntax,
                                                    /* isInterfacePort */ true);
        if (!expr || expr->bad())
            return nullptr;

        // Pull out the expression type, which should always be a virtual interface or
        // array of such types, and decompose into dims and interface info.
        SmallVector<ConstantRange, 4> dims;
        auto type = expr->type;
        while (type->isUnpackedArray()) {
            dims.push_back(type->getFixedRange());
            type = type->getArrayElementType();
        }

        auto& vit = type->as<VirtualInterfaceType>();
        auto& connDef = vit.iface.getDefinition();

        ASSERT(port.isGeneric || port.interfaceDef);
        if (&connDef != port.interfaceDef && !port.isGeneric) {
            std::string path;
            connDef.getHierarchicalPath(path);

            auto& diag = context.addDiag(diag::InterfacePortTypeMismatch, syntax.sourceRange());
            diag << path << port.interfaceDef->name;
            diag.addNote(diag::NoteDeclarationHere, port.location);
            return nullptr;
        }

        // Modport must match the specified requirement, if we have one.
        if (vit.modport && !port.modport.empty() && vit.modport->name != port.modport) {
            auto& diag = context.addDiag(diag::ModportConnMismatch, syntax.sourceRange());
            diag << connDef.name << vit.modport->name;
            diag << (port.isGeneric ? "interface"sv : port.interfaceDef->name);
            diag << port.modport;
            return nullptr;
        }

        if (port.isGeneric && !port.modport.empty() && !vit.modport) {
            if (auto it = connDef.modports.find(port.modport); it == connDef.modports.end()) {
                auto& diag = context.addDiag(diag::NotAModport, syntax.sourceRange());
                diag << port.modport;
                diag << connDef.name;
                diag.addNote(diag::NoteReferencedHere, port.location);
                return nullptr;
            }
        }

        // Make the connection if the dimensions match exactly what the port is expecting.
        const Symbol* symbol = expr->as<ArbitrarySymbolExpression>().symbol;
        if (areDimSizesEqual(*portDims, dims))
            return symbol;

        // Otherwise, if the instance being instantiated is part of an array of instances *and*
        // the symbol we're connecting to is an array of interfaces, we need to check to see whether
        // to slice up that array among all the instances. We do the slicing operation if:
        // instance array dimensions + port dimensions == connection dimensions
        span<const ConstantRange> dimSpan = dims;
        if (dimSpan.size() >= instanceDims.size() &&
            areDimSizesEqual(dimSpan.subspan(0, instanceDims.size()), instanceDims) &&
            areDimSizesEqual(dimSpan.subspan(instanceDims.size()), *portDims)) {

            // It's ok to do the slicing, so pick the correct slice for the connection
            // based on the actual path of the instance we're elaborating.
            for (size_t i = 0; i < instance.arrayPath.size(); i++) {
                // First translate the path index since it's relative to that particular
                // array's declared range.
                int32_t index = instanceDims[i].translateIndex(instance.arrayPath[i]);

                // Now translate back to be relative to the connecting interface's declared range.
                // Note that we want this to be zero based because we're going to index into
                // the actual span of elements, so we only need to flip the index if the range
                // is not little endian.
                auto& array = symbol->as<InstanceArraySymbol>();
                if (!array.range.isLittleEndian())
                    index = array.range.upper() - index - array.range.lower();

                symbol = array.elements[size_t(index)];
            }

            return symbol;
        }

        auto& diag = scope.addDiag(diag::PortConnDimensionsMismatch, syntax.sourceRange())
                     << port.name;
        diag.addNote(diag::NoteDeclarationHere, port.location);
        return nullptr;
    }

    const Scope& scope;
    const InstanceSymbol& instance;
    Compilation& comp;
    SmallVector<ConstantRange, 4> instanceDims;
    SmallVector<const PortConnectionSyntax*> orderedConns;
    SmallMap<string_view, std::pair<const NamedPortConnectionSyntax*, bool>, 8> namedConns;
    span<const AttributeSymbol* const> wildcardAttrs;
    LookupLocation lookupLocation;
    SourceRange wildcardRange;
    size_t orderedIndex = 0;
    bool usingOrdered = true;
    bool hasWildcard = false;
    bool warnedAboutUnnamed = false;
    bool unnamedRefError = false;
};

struct PortBackrefVisitor {
    const PortSymbol& port;

    PortBackrefVisitor(const PortSymbol& port) : port(port) {}

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_base_of_v<Expression, T>) {
            switch (expr.kind) {
                case ExpressionKind::NamedValue:
                    expr.template as<NamedValueExpression>().symbol.addPortBackref(port);
                    break;
                default:
                    if constexpr (is_detected_v<ASTDetectors::visitExprs_t, T,
                                                PortBackrefVisitor>) {
                        expr.visitExprs(*this);
                    }
                    break;
            }
        }
    }

    void visitInvalid(const Expression&) {}
    void visitInvalid(const AssertionExpr&) {}
};

} // end anonymous namespace

PortSymbol::PortSymbol(string_view name, SourceLocation loc, bool isAnsiPort) :
    Symbol(SymbolKind::Port, name, loc), isAnsiPort(isAnsiPort) {
    externalLoc = loc;
}

const Type& PortSymbol::getType() const {
    if (type)
        return *type;

    auto scope = getParentScope();
    auto syntax = getSyntax();
    ASSERT(scope && syntax);

    if (internalSymbol) {
        auto dt = internalSymbol->getDeclaredType();
        ASSERT(dt);
        type = &dt->getType();

        bitmask<ASTFlags> astFlags = ASTFlags::NonProcedural | ASTFlags::AllowInterconnect;
        if (direction != ArgumentDirection::Out)
            astFlags |= ASTFlags::LValue;

        ASTContext context(*scope, LookupLocation::before(*this), astFlags);

        auto& valExpr = ValueExpressionBase::fromSymbol(context, *internalSymbol, false,
                                                        {location, location + name.length()});

        if (syntax->kind == SyntaxKind::PortReference) {
            auto& prs = syntax->as<PortReferenceSyntax>();
            if (auto select = prs.select) {
                internalExpr = &Expression::bindSelector(valExpr, *select, context);
                type = internalExpr->type;
            }
        }

        internalSymbol->as<ValueSymbol>().addPortBackref(*this);
        if (direction == ArgumentDirection::In || direction == ArgumentDirection::InOut) {
            // Ensure that this driver gets registered with the internal symbol.
            auto flags = direction == ArgumentDirection::In ? AssignFlags::InputPort
                                                            : AssignFlags::InOutPort;
            if (internalExpr) {
                internalExpr->requireLValue(context, {}, flags);
            }
            else {
                context.addDriver(internalSymbol->as<ValueSymbol>(), valExpr, flags);
            }
        }
    }
    else if (isNullPort) {
        type = &scope->getCompilation().getVoidType();
    }
    else {
        // We should have an explicit port connection expression here.
        auto& eaps = syntax->as<ExplicitAnsiPortSyntax>();
        ASSERT(eaps.expr);

        // The direction of the connection is reversed, as data coming in to an input
        // port flows out to the internal symbol, and vice versa. Inout and ref
        // ports don't change.
        bitmask<ASTFlags> astFlags = ASTFlags::NonProcedural;
        ArgumentDirection checkDir = direction;
        switch (direction) {
            case ArgumentDirection::In:
                checkDir = ArgumentDirection::Out;
                astFlags |= ASTFlags::LValue;
                break;
            case ArgumentDirection::Out:
                checkDir = ArgumentDirection::In;
                break;
            case ArgumentDirection::InOut:
                astFlags |= ASTFlags::LValue;
                break;
            case ArgumentDirection::Ref:
                break;
        }

        ASTContext context(*scope, LookupLocation::max, astFlags);
        internalExpr = &Expression::bind(*eaps.expr, context);
        type = internalExpr->type;

        if (!internalExpr->bad()) {
            checkSymbolConnection(*internalExpr, checkDir, context, location,
                                  direction == ArgumentDirection::In ? AssignFlags::InputPort
                                                                     : AssignFlags::None);

            PortBackrefVisitor visitor(*this);
            internalExpr->visit(visitor);
        }
    }

    const Type* errorType;
    if (!type->isValidForPort(&errorType)) {
        if (errorType == type)
            scope->addDiag(diag::InvalidPortType, location) << *type;
        else
            scope->addDiag(diag::InvalidPortSubType, location) << *type << *errorType;
    }

    return *type;
}

const Expression* PortSymbol::getInitializer() const {
    if (!initializer && initializerSyntax) {
        auto scope = getParentScope();
        ASSERT(scope);
        ASSERT(internalSymbol);

        // Ansi ports bind their initializers in the context of the port list,
        // while non-ansi ports use the internal symbol context.
        LookupLocation ll;
        if (isAnsiPort)
            ll = LookupLocation::after(*this);
        else
            ll = LookupLocation::after(*internalSymbol);

        ASTContext context(*scope, ll, ASTFlags::NonProcedural | ASTFlags::StaticInitializer);
        initializer = &Expression::bindRValue(getType(), *initializerSyntax, initializerLoc,
                                              context);
        context.eval(*initializer);
    }

    return initializer;
}

const Expression* PortSymbol::getInternalExpr() const {
    getType();
    return internalExpr;
}

static void getNetRanges(const Expression& expr,
                         SmallVectorBase<PortSymbol::NetTypeRange>& ranges) {
    if (auto sym = expr.getSymbolReference(); sym && sym->kind == SymbolKind::Net) {
        auto& nt = sym->as<NetSymbol>().netType;
        bitwidth_t width = expr.type->getBitWidth();

        if (!ranges.empty() && ranges.back().netType == &nt)
            ranges.back().width += width;
        else
            ranges.push_back({&nt, width});
    }
    else if (expr.kind == ExpressionKind::Concatenation) {
        for (auto op : expr.as<ConcatenationExpression>().operands())
            getNetRanges(*op, ranges);
    }
    else if (expr.kind == ExpressionKind::Conversion) {
        auto& conv = expr.as<ConversionExpression>();
        if (conv.isImplicit())
            getNetRanges(conv.operand(), ranges);
    }
    else if (expr.kind == ExpressionKind::Assignment) {
        auto& assign = expr.as<AssignmentExpression>();
        if (assign.isLValueArg())
            getNetRanges(assign.left(), ranges);
    }
}

void PortSymbol::getNetTypes(SmallVectorBase<NetTypeRange>& ranges) const {
    if (auto ie = getInternalExpr()) {
        getNetRanges(*ie, ranges);
    }
    else if (internalSymbol && internalSymbol->kind == SymbolKind::Net) {
        auto& nt = internalSymbol->as<NetSymbol>().netType;
        ranges.push_back({&nt, getType().getBitWidth()});
    }
}

static bool isNetPortImpl(const Expression& expr) {
    if (auto sym = expr.getSymbolReference(); sym && sym->kind == SymbolKind::Net)
        return true;

    if (expr.kind == ExpressionKind::Concatenation) {
        for (auto op : expr.as<ConcatenationExpression>().operands()) {
            if (!isNetPortImpl(*op))
                return false;
        }
        return true;
    }

    if (expr.kind == ExpressionKind::Conversion) {
        auto& conv = expr.as<ConversionExpression>();
        if (conv.isImplicit())
            return isNetPortImpl(conv.operand());
    }

    if (expr.kind == ExpressionKind::Assignment) {
        auto& assign = expr.as<AssignmentExpression>();
        if (assign.isLValueArg())
            return isNetPortImpl(assign.left());
    }

    return false;
}

bool PortSymbol::isNetPort() const {
    if (auto ie = getInternalExpr())
        return isNetPortImpl(*ie);

    return internalSymbol && internalSymbol->kind == SymbolKind::Net;
}

void PortSymbol::fromSyntax(
    const PortListSyntax& syntax, const Scope& scope, SmallVectorBase<const Symbol*>& results,
    SmallVectorBase<std::pair<Symbol*, const Symbol*>>& implicitMembers,
    span<std::pair<const SyntaxNode*, const Symbol*> const> portDeclarations) {

    switch (syntax.kind) {
        case SyntaxKind::AnsiPortList: {
            AnsiPortListBuilder builder{scope, implicitMembers};
            for (auto port : syntax.as<AnsiPortListSyntax>().ports) {
                switch (port->kind) {
                    case SyntaxKind::ImplicitAnsiPort:
                        results.push_back(builder.createPort(port->as<ImplicitAnsiPortSyntax>()));
                        break;
                    case SyntaxKind::ExplicitAnsiPort:
                        results.push_back(builder.createPort(port->as<ExplicitAnsiPortSyntax>()));
                        break;
                    default:
                        ASSUME_UNREACHABLE;
                }
            }

            if (!portDeclarations.empty()) {
                scope.addDiag(diag::PortDeclInANSIModule,
                              portDeclarations[0].first->getFirstToken().location());
            }
            break;
        }
        case SyntaxKind::NonAnsiPortList: {
            NonAnsiPortListBuilder builder{scope, portDeclarations, implicitMembers};
            for (auto port : syntax.as<NonAnsiPortListSyntax>().ports) {
                switch (port->kind) {
                    case SyntaxKind::ImplicitNonAnsiPort:
                        results.push_back(
                            builder.createPort(port->as<ImplicitNonAnsiPortSyntax>()));
                        break;
                    case SyntaxKind::ExplicitNonAnsiPort:
                        results.push_back(
                            builder.createPort(port->as<ExplicitNonAnsiPortSyntax>()));
                        break;
                    case SyntaxKind::EmptyNonAnsiPort:
                        results.push_back(builder.createPort(port->as<EmptyNonAnsiPortSyntax>()));
                        break;
                    default:
                        ASSUME_UNREACHABLE;
                }
            }
            builder.finalize();
            break;
        }
        case SyntaxKind::WildcardPortList:
            scope.addDiag(diag::NotYetSupported, syntax.sourceRange());
            break;
        default:
            ASSUME_UNREACHABLE;
    }
}

void PortSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("type", getType());
    serializer.write("direction", toString(direction));

    if (auto init = getInitializer())
        serializer.write("initializer", *init);

    if (internalSymbol)
        serializer.writeLink("internalSymbol", *internalSymbol);
}

MultiPortSymbol::MultiPortSymbol(string_view name, SourceLocation loc,
                                 span<const PortSymbol* const> ports, ArgumentDirection direction) :
    Symbol(SymbolKind::MultiPort, name, loc),
    ports(ports), direction(direction) {
}

const Type& MultiPortSymbol::getType() const {
    if (type)
        return *type;

    auto scope = getParentScope();
    auto syntax = getSyntax();
    ASSERT(scope && syntax);

    auto& comp = scope->getCompilation();

    ASTContext context(*scope, LookupLocation::before(*this), ASTFlags::NonProcedural);
    bitwidth_t totalWidth = 0;
    bitmask<IntegralFlags> flags;

    for (auto port : ports) {
        auto& t = port->getType();
        if (t.isError() || t.isUntypedType()) {
            type = &comp.getErrorType();
            return *type;
        }

        if (!t.isIntegral()) {
            context.addDiag(diag::BadConcatExpression, port->externalLoc) << t;
            type = &comp.getErrorType();
            return *type;
        }

        totalWidth += t.getBitWidth();

        if (!context.requireValidBitWidth(totalWidth, syntax->sourceRange())) {
            type = &comp.getErrorType();
            return *type;
        }

        if (t.isFourState())
            flags |= IntegralFlags::FourState;
    }

    if (totalWidth == 0) {
        type = &comp.getErrorType();
        return *type;
    }

    type = &comp.getType(totalWidth, flags);
    return *type;
}

void MultiPortSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("type", getType());
    serializer.write("direction", toString(direction));

    serializer.startArray("ports");
    for (auto port : ports) {
        serializer.startObject();
        port->serializeTo(serializer);
        serializer.endObject();
    }
    serializer.endArray();
}

std::optional<span<const ConstantRange>> InterfacePortSymbol::getDeclaredRange() const {
    if (range)
        return *range;

    if (isInvalid()) {
        range.emplace();
        return *range;
    }

    auto syntax = getSyntax();
    ASSERT(syntax);

    auto scope = getParentScope();
    ASSERT(scope);

    ASTContext context(*scope, LookupLocation::before(*this), ASTFlags::NonProcedural);

    SmallVector<ConstantRange, 4> buffer;
    for (auto dimSyntax : syntax->as<DeclaratorSyntax>().dimensions) {
        auto dim = context.evalDimension(*dimSyntax, /* requireRange */ true, /* isPacked */ false);
        if (!dim.isRange())
            return std::nullopt;

        buffer.push_back(dim.range);
    }

    range = buffer.copy(scope->getCompilation());
    return *range;
}

const Symbol* InterfacePortSymbol::getConnection() const {
    auto scope = getParentScope();
    ASSERT(scope);

    auto& body = scope->asSymbol().as<InstanceBodySymbol>();
    ASSERT(body.parentInstance);

    auto conn = body.parentInstance->getPortConnection(*this);
    if (!conn)
        return nullptr;

    return conn->getIfaceInstance();
}

void InterfacePortSymbol::serializeTo(ASTSerializer& serializer) const {
    if (interfaceDef)
        serializer.write("interfaceDef", interfaceDef->name);
    if (!modport.empty())
        serializer.write("modport", modport);
    serializer.write("isGeneric", isGeneric);
}

PortConnection::PortConnection(const Symbol& port, const InstanceSymbol& parentInstance) :
    port(port), parentInstance(parentInstance) {
}

PortConnection::PortConnection(const Symbol& port, const InstanceSymbol& parentInstance,
                               const ExpressionSyntax& expr) :
    port(port),
    parentInstance(parentInstance), exprSyntax(&expr) {
}

PortConnection::PortConnection(const Symbol& port, const InstanceSymbol& parentInstance,
                               bool useDefault) :
    port(port),
    parentInstance(parentInstance), useDefault(useDefault) {
}

PortConnection::PortConnection(const InterfacePortSymbol& port,
                               const InstanceSymbol& parentInstance,
                               const Symbol* connectedSymbol) :
    port(port),
    parentInstance(parentInstance), connectedSymbol(connectedSymbol) {
}

PortConnection::PortConnection(const Symbol& port, const InstanceSymbol& parentInstance,
                               const Symbol* connectedSymbol, SourceRange implicitNameRange) :
    port(port),
    parentInstance(parentInstance), connectedSymbol(connectedSymbol),
    implicitNameRange(implicitNameRange) {
}

const Symbol* PortConnection::getIfaceInstance() const {
    if (port.kind == SymbolKind::InterfacePort)
        return connectedSymbol;
    return nullptr;
}

static std::pair<ArgumentDirection, const Type*> getDirAndType(const Symbol& port) {
    if (port.kind == SymbolKind::Port) {
        auto& ps = port.as<PortSymbol>();
        return {ps.direction, &ps.getType()};
    }
    else {
        auto& mp = port.as<MultiPortSymbol>();
        return {mp.direction, &mp.getType()};
    }
}

const Expression* PortConnection::getExpression() const {
    if (expr || port.kind == SymbolKind::InterfacePort)
        return expr;

    if (connectedSymbol || exprSyntax) {
        auto ll = LookupLocation::after(parentInstance);
        auto scope = ll.getScope();
        ASSERT(scope);

        const bool isNetPort = port.kind == SymbolKind::Port && port.as<PortSymbol>().isNetPort();
        auto [direction, type] = getDirAndType(port);

        bitmask<ASTFlags> flags = ASTFlags::NonProcedural;
        if (isNetPort)
            flags |= ASTFlags::AllowInterconnect;
        if (direction == ArgumentDirection::Out || direction == ArgumentDirection::InOut)
            flags |= ASTFlags::LValue;

        ASTContext context(*scope, ll, flags);
        context.setInstance(parentInstance);

        if (connectedSymbol) {
            Expression* e = &ValueExpressionBase::fromSymbol(context, *connectedSymbol, false,
                                                             implicitNameRange);

            bitmask<AssignFlags> assignFlags;
            if (direction == ArgumentDirection::Out)
                assignFlags = AssignFlags::OutputPort;

            if (!e->type->isEquivalent(*type)) {
                auto& comp = context.getCompilation();
                if (direction == ArgumentDirection::In) {
                    e = &Expression::convertAssignment(context, *type, *e,
                                                       implicitNameRange.start());
                }
                else if (direction != ArgumentDirection::Ref) {
                    auto rhs = comp.emplace<EmptyArgumentExpression>(*type, implicitNameRange);
                    Expression::convertAssignment(context, *e->type, *rhs,
                                                  implicitNameRange.start(), &e, &assignFlags);
                }

                // We should warn for this case unless convertAssignment already issued an error,
                // or if we're in an instance array unwrapping case.
                if ((parentInstance.arrayPath.empty() || direction == ArgumentDirection::Ref) &&
                    !e->bad() && !type->isError()) {
                    auto& diag = context.addDiag(diag::ImplicitNamedPortTypeMismatch,
                                                 implicitNameRange);
                    diag << port.name;
                    diag << *type;
                    diag << *e->type;

                    // There's no way to represent this expression for the ref case.
                    if (direction == ArgumentDirection::Ref)
                        e = comp.emplace<InvalidExpression>(e, comp.getErrorType());
                }
            }

            expr = e;
            if (!expr->bad()) {
                checkSymbolConnection(*expr, direction, context, expr->sourceRange.start(),
                                      assignFlags);
            }
        }
        else {
            expr = &Expression::bindArgument(*type, direction, *exprSyntax, context);
        }
    }
    else if (useDefault) {
        auto& ps = port.as<PortSymbol>();
        expr = ps.getInitializer();
    }

    return expr;
}

static const Symbol* findAnyVars(const Expression& expr) {
    if (auto sym = expr.getSymbolReference(); sym && sym->kind != SymbolKind::Net)
        return sym;

    if (expr.kind == ExpressionKind::Concatenation) {
        for (auto op : expr.as<ConcatenationExpression>().operands()) {
            if (auto sym = findAnyVars(*op))
                return sym;
        }
    }

    return nullptr;
}

void PortConnection::checkSimulatedNetTypes() const {
    getExpression();
    if (!expr || expr->bad())
        return;

    SmallVector<PortSymbol::NetTypeRange, 4> internal;
    if (port.kind == SymbolKind::Port)
        port.as<PortSymbol>().getNetTypes(internal);
    else {
        for (auto p : port.as<MultiPortSymbol>().ports)
            p->getNetTypes(internal);
    }

    SmallVector<PortSymbol::NetTypeRange, 4> external;
    getNetRanges(*expr, external);

    // There might not be any nets, in which case we should just leave.
    if (internal.empty() && external.empty())
        return;

    auto scope = parentInstance.getParentScope();
    ASSERT(scope);

    // Do additional checking on the expression for interconnect port connections.
    if (internal.size() == 1 && internal[0].netType->netKind == NetType::Interconnect) {
        if (auto sym = findAnyVars(*expr)) {
            scope->addDiag(diag::InterconnectPortVar, expr->sourceRange) << sym->name;
            return;
        }
    }

    auto requireMatching = [&](const NetType& udnt) {
        // Types are more restricted; they must match instead of just being
        // assignment compatible. Also direction must be input or output.
        // We need to do this dance to get at the type of the connection prior
        // to it being converted to match the type of the port.
        auto exprType = expr->type.get();
        if (expr->kind == ExpressionKind::Conversion) {
            auto& conv = expr->as<ConversionExpression>();
            if (conv.isImplicit())
                exprType = conv.operand().type;
        }
        else if (expr->kind == ExpressionKind::Assignment) {
            auto& assign = expr->as<AssignmentExpression>();
            if (assign.isLValueArg())
                exprType = assign.left().type;
        }

        auto [direction, type] = getDirAndType(port);
        if (!type->isMatching(*exprType)) {
            // If this is from an interconnect connection, don't require matching types.
            auto isInterconnect = [](const Type& t) {
                auto curr = &t;
                while (curr->isArray())
                    curr = curr->getArrayElementType();

                return curr->isUntypedType();
            };

            if (isInterconnect(*type) || isInterconnect(*exprType))
                return;

            auto& diag = scope->addDiag(diag::MismatchedUserDefPortConn, expr->sourceRange);
            diag << udnt.name;
            diag << *type;
            diag << *exprType;
        }
        else if (direction != ArgumentDirection::In && direction != ArgumentDirection::Out) {
            auto& diag = scope->addDiag(diag::MismatchedUserDefPortDir, expr->sourceRange);
            diag << udnt.name;
        }
    };

    // If only one side has net types, check for user-defined nettypes,
    // which impose additional restrictions on the connection.
    if (internal.empty() || external.empty()) {
        const NetType* udnt = nullptr;
        auto checker = [&](auto& list) {
            for (auto& ntr : list) {
                if (!ntr.netType->isBuiltIn()) {
                    udnt = ntr.netType;
                    break;
                }
            }
        };

        checker(internal);
        checker(external);
        if (udnt)
            requireMatching(*udnt);

        return;
    }

    // Simple case is one net connected on each side.
    if (internal.size() == 1 && external.size() == 1) {
        auto& inNt = *internal[0].netType;
        auto& exNt = *external[0].netType;
        if (&inNt == &exNt)
            return;

        if (!inNt.isBuiltIn() || !exNt.isBuiltIn()) {
            // If both sides are user-defined nettypes they need to match.
            if (!inNt.isBuiltIn() && !exNt.isBuiltIn()) {
                auto& diag = scope->addDiag(diag::UserDefPortTwoSided, expr->sourceRange);
                diag << inNt.name << exNt.name;
            }
            else if (!inNt.isBuiltIn()) {
                requireMatching(inNt);
            }
            else {
                requireMatching(exNt);
            }
        }
        else {
            // Otherwise both sides are built-in nettypes.
            bool shouldWarn;
            NetType::getSimulatedNetType(inNt, exNt, shouldWarn);
            if (shouldWarn) {
                auto& diag = scope->addDiag(diag::NetInconsistent, expr->sourceRange);
                diag << exNt.name;
                diag << inNt.name;
                diag.addNote(diag::NoteDeclarationHere, port.location);
            }
        }

        return;
    }

    // Otherwise we need to compare ranges of net types for differences.
    auto in = internal.begin();
    auto ex = external.begin();
    bitwidth_t currBit = 0;
    bitwidth_t exprWidth = expr->type->getBitWidth();
    bool shownDeclaredHere = false;

    while (true) {
        bool shouldWarn;
        auto& inNt = *in->netType;
        auto& exNt = *ex->netType;

        if (!inNt.isBuiltIn() || !exNt.isBuiltIn()) {
            if (&inNt != &exNt) {
                scope->addDiag(diag::UserDefPortMixedConcat, expr->sourceRange)
                    << inNt.name << exNt.name;
                return;
            }
            shouldWarn = false;
        }
        else {
            NetType::getSimulatedNetType(inNt, exNt, shouldWarn);
        }

        bitwidth_t width;
        if (in->width < ex->width) {
            width = in->width;
            ex->width -= width;
            in++;
        }
        else {
            width = ex->width;
            ex++;

            if (in->width == width)
                in++;
            else
                in->width -= width;
        }

        if (shouldWarn) {
            ASSERT(exprWidth >= currBit + width);
            bitwidth_t left = exprWidth - currBit - 1;
            bitwidth_t right = left - (width - 1);

            auto& diag = scope->addDiag(diag::NetRangeInconsistent, expr->sourceRange);
            diag << exNt.name;
            diag << left << right;
            diag << inNt.name;

            if (!shownDeclaredHere) {
                diag.addNote(diag::NoteDeclarationHere, port.location);
                shownDeclaredHere = true;
            }
        }

        if (in == internal.end() || ex == external.end()) {
            ASSERT(in == internal.end() && ex == external.end());
            break;
        }

        currBit += width;
    }
}

void PortConnection::makeConnections(
    const InstanceSymbol& instance, span<const Symbol* const> ports,
    const SeparatedSyntaxList<PortConnectionSyntax>& portConnections,
    SmallVector<const PortConnection*>& results) {

    PortConnectionBuilder builder(instance, portConnections);
    for (auto portBase : ports) {
        if (portBase->kind == SymbolKind::Port) {
            auto& port = portBase->as<PortSymbol>();
            auto conn = builder.getConnection(port);
            ASSERT(conn);
            results.push_back(conn);
        }
        else if (portBase->kind == SymbolKind::MultiPort) {
            auto& port = portBase->as<MultiPortSymbol>();
            auto conn = builder.getConnection(port);
            ASSERT(conn);
            results.push_back(conn);
        }
        else {
            auto& port = portBase->as<InterfacePortSymbol>();
            auto conn = builder.getIfaceConnection(port);
            ASSERT(conn);
            results.push_back(conn);
        }
    }

    builder.finalize();
}

void PortConnection::serializeTo(ASTSerializer& serializer) const {
    serializer.writeLink("port", port);
    if (port.kind == SymbolKind::InterfacePort) {
        if (connectedSymbol)
            serializer.writeLink("ifaceInstance", *connectedSymbol);
    }
    else {
        if (auto e = getExpression())
            serializer.write("expr", *e);
    }

    auto scope = parentInstance.getParentScope();
    ASSERT(scope);

    auto attributes = scope->getCompilation().getAttributes(*this);
    if (!attributes.empty()) {
        serializer.startArray("attributes");
        for (auto attr : attributes)
            serializer.serialize(*attr);
        serializer.endArray();
    }
}

} // namespace slang::ast
