//------------------------------------------------------------------------------
// Definition.cpp
// Module / interface / program definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/compilation/Definition.h"

#include "../symbols/ParameterBuilder.h"

#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/symbols/AttributeSymbol.h"
#include "slang/symbols/ParameterSymbols.h"
#include "slang/symbols/Scope.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxFacts.h"

namespace slang {

Definition::ParameterDecl::ParameterDecl(const Scope& scope,
                                         const ParameterDeclarationSyntax& syntax,
                                         const DeclaratorSyntax& decl, bool isLocal, bool isPort) :
    valueSyntax(&syntax),
    valueDecl(&decl), isTypeParam(false), isLocalParam(isLocal), isPortParam(isPort),
    hasSyntax(true) {

    name = decl.name.valueText();
    location = decl.name.location();

    if (!decl.initializer) {
        if (!isPort)
            scope.addDiag(diag::BodyParamNoInitializer, location);
        else if (isLocal)
            scope.addDiag(diag::LocalParamNoInitializer, location);
    }
}

Definition::ParameterDecl::ParameterDecl(const Scope& scope,
                                         const TypeParameterDeclarationSyntax& syntax,
                                         const TypeAssignmentSyntax& decl, bool isLocal,
                                         bool isPort) :
    typeSyntax(&syntax),
    typeDecl(&decl), isTypeParam(true), isLocalParam(isLocal), isPortParam(isPort),
    hasSyntax(true) {

    name = decl.name.valueText();
    location = decl.name.location();

    if (!decl.assignment) {
        if (!isPort)
            scope.addDiag(diag::BodyParamNoInitializer, location);
        else if (isLocal)
            scope.addDiag(diag::LocalParamNoInitializer, location);
    }
}

Definition::ParameterDecl::ParameterDecl(string_view name, SourceLocation location,
                                         const Type& givenType, bool isLocal, bool isPort,
                                         const Expression* givenInitializer) :
    givenType(&givenType),
    givenInitializer(givenInitializer), name(name), location(location), isTypeParam(false),
    isLocalParam(isLocal), isPortParam(isPort), hasSyntax(false) {
    ASSERT(givenInitializer || (isPort && !isLocal));
}

Definition::ParameterDecl::ParameterDecl(string_view name, SourceLocation location, bool isLocal,
                                         bool isPort, const Type* defaultType) :
    givenType(defaultType),
    name(name), location(location), isTypeParam(true), isLocalParam(isLocal), isPortParam(isPort),
    hasSyntax(false) {
    ASSERT(givenType || (isPort && !isLocal));
}

bool Definition::ParameterDecl::hasDefault() const {
    if (hasSyntax) {
        if (isTypeParam)
            return typeDecl && typeDecl->assignment != nullptr;
        else
            return valueDecl && valueDecl->initializer != nullptr;
    }
    else {
        if (isTypeParam)
            return givenType != nullptr;
        else
            return givenInitializer != nullptr;
    }
}

Definition::Definition(const Scope& scope, LookupLocation lookupLocation,
                       const ModuleDeclarationSyntax& syntax, const NetType& defaultNetType,
                       UnconnectedDrive unconnectedDrive, optional<TimeScale> directiveTimeScale,
                       const SyntaxTree* syntaxTree) :
    syntax(syntax),
    defaultNetType(defaultNetType), scope(scope), unconnectedDrive(unconnectedDrive),
    syntaxTree(syntaxTree) {

    // Extract and save various properties of the definition.
    auto& header = *syntax.header;
    name = header.name.valueText();
    location = header.name.location();
    indexInScope = lookupLocation.getIndex();
    definitionKind = SemanticFacts::getDefinitionKind(syntax.kind);
    defaultLifetime =
        SemanticFacts::getVariableLifetime(header.lifetime).value_or(VariableLifetime::Static);
    attributes = AttributeSymbol::fromSyntax(syntax.attributes, scope, lookupLocation);
    hasNonAnsiPorts =
        syntax.header->ports && syntax.header->ports->kind == SyntaxKind::NonAnsiPortList;

    // Find all port parameters.
    bool hasPortParams = header.parameters != nullptr;
    if (hasPortParams)
        ParameterBuilder::createDecls(scope, *header.parameters, parameters);

    bool first = true;
    optional<SourceRange> unitsRange;
    optional<SourceRange> precisionRange;

    for (auto member : syntax.members) {
        if (member->kind == SyntaxKind::TimeUnitsDeclaration) {
            SemanticFacts::populateTimeScale(timeScale, scope,
                                             member->as<TimeUnitsDeclarationSyntax>(), unitsRange,
                                             precisionRange, first);
            continue;
        }

        first = false;
        if (member->kind == SyntaxKind::ModportDeclaration) {
            for (auto item : member->as<ModportDeclarationSyntax>().items)
                modports.emplace(item->name.valueText());
        }
        else if (member->kind == SyntaxKind::ParameterDeclarationStatement) {
            auto declaration = member->as<ParameterDeclarationStatementSyntax>().parameter;
            bool isLocal =
                hasPortParams || declaration->keyword.kind == TokenKind::LocalParamKeyword;

            ParameterBuilder::createDecls(scope, *declaration, isLocal, /* isPort */ false,
                                          parameters);
        }
    }

    SemanticFacts::populateTimeScale(timeScale, scope, directiveTimeScale, unitsRange.has_value(),
                                     precisionRange.has_value());
}

void Definition::resolvePorts() const {
    // Index all of our ports. We do just enough work here to figure out the
    // names of each port and whether it's likely an interface port or not.
    resolvedPorts = true;
    auto portSyntax = syntax.header->ports;
    if (!portSyntax)
        return;

    uint32_t index = 0;
    if (portSyntax->kind == SyntaxKind::AnsiPortList) {
        for (auto port : portSyntax->as<AnsiPortListSyntax>().ports) {
            if (port->kind == SyntaxKind::ImplicitAnsiPort) {
                auto& iap = port->as<ImplicitAnsiPortSyntax>();
                bool isIface = iap.header->kind == SyntaxKind::InterfacePortHeader;
                if (iap.header->kind == SyntaxKind::VariablePortHeader) {
                    // A variable port header might still be an interface port; check if it has
                    // a simple type name that resolves to a definition name somewhere.
                    auto& vph = iap.header->as<VariablePortHeaderSyntax>();
                    if (!vph.varKeyword && !vph.direction) {
                        string_view simpleName = SyntaxFacts::getSimpleTypeName(*vph.dataType);
                        if (!simpleName.empty()) {
                            auto def = scope.getCompilation().getDefinition(simpleName, scope);
                            if (def && def->definitionKind == DefinitionKind::Interface)
                                isIface = true;
                        }
                    }
                }
                ports.emplace(iap.declarator->name.valueText(), index, isIface);
            }
            else {
                // TODO: can this be an iface?
                auto& eap = port->as<ExplicitAnsiPortSyntax>();
                ports.emplace(eap.name.valueText(), index, /* isIface */ false);
            }

            index++;
        }
    }
    else {
        // TODO: non-ansi iface ports not supported yet
        for (auto port : portSyntax->as<NonAnsiPortListSyntax>().ports) {
            if (port->kind == SyntaxKind::ImplicitNonAnsiPort) {
                auto& iap = port->as<ImplicitNonAnsiPortSyntax>();
                if (iap.expr) {
                    if (iap.expr->kind == SyntaxKind::PortReference) {
                        auto& ref = iap.expr->as<PortReferenceSyntax>();
                        ports.emplace(ref.name.valueText(), index, /* isIface */ false);
                    }
                    else {
                        // TODO: support this
                    }
                }
            }
            else if (port->kind == SyntaxKind::ExplicitNonAnsiPort) {
                auto& eap = port->as<ExplicitNonAnsiPortSyntax>();
                ports.emplace(eap.name.valueText(), index, /* isIface */ false);
            }
            else {
                ASSERT(port->kind == SyntaxKind::EmptyNonAnsiPort);
                ports.emplace("", index, /* isIface */ false);
            }

            index++;
        }
    }
}

string_view Definition::getKindString() const {
    switch (definitionKind) {
        case DefinitionKind::Module:
            return "module"sv;
        case DefinitionKind::Interface:
            return "interface"sv;
        case DefinitionKind::Program:
            return "program"sv;
        default:
            THROW_UNREACHABLE;
    }
}

string_view Definition::getArticleKindString() const {
    switch (definitionKind) {
        case DefinitionKind::Module:
            return "a module"sv;
        case DefinitionKind::Interface:
            return "an interface"sv;
        case DefinitionKind::Program:
            return "a program"sv;
        default:
            THROW_UNREACHABLE;
    }
}

} // namespace slang
