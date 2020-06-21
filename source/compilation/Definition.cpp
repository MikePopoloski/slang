//------------------------------------------------------------------------------
// Definition.cpp
// Module / interface / program definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/compilation/Definition.h"

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
    valueDecl(&decl), isTypeParam(false), isLocalParam(isLocal), isPortParam(isPort) {

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
    typeDecl(&decl), isTypeParam(true), isLocalParam(isLocal), isPortParam(isPort) {

    name = decl.name.valueText();
    location = decl.name.location();

    if (!decl.assignment) {
        if (!isPort)
            scope.addDiag(diag::BodyParamNoInitializer, location);
        else if (isLocal)
            scope.addDiag(diag::LocalParamNoInitializer, location);
    }
}

bool Definition::ParameterDecl::hasDefault() const {
    if (isTypeParam)
        return typeDecl && typeDecl->assignment != nullptr;
    else
        return valueDecl && valueDecl->initializer != nullptr;
}

Definition::Definition(const Scope& scope, LookupLocation lookupLocation,
                       const ModuleDeclarationSyntax& syntax, const NetType& defaultNetType,
                       UnconnectedDrive unconnectedDrive, optional<TimeScale> directiveTimeScale) :
    syntax(syntax),
    defaultNetType(defaultNetType), scope(scope), unconnectedDrive(unconnectedDrive) {

    // Extract and save various properties of the definition.
    auto& header = *syntax.header;
    name = header.name.valueText();
    location = header.name.location();
    indexInScope = lookupLocation.getIndex();
    definitionKind = SemanticFacts::getDefinitionKind(syntax.kind);
    defaultLifetime =
        SemanticFacts::getVariableLifetime(header.lifetime).value_or(VariableLifetime::Static);
    attributes = AttributeSymbol::fromSyntax(syntax.attributes, scope, lookupLocation);

    auto createParams = [&](auto syntax, bool isLocal, bool isPort) {
        if (syntax->kind == SyntaxKind::ParameterDeclaration) {
            auto& paramSyntax = syntax->template as<ParameterDeclarationSyntax>();
            for (auto decl : paramSyntax.declarators)
                parameters.emplace(scope, paramSyntax, *decl, isLocal, isPort);
        }
        else {
            auto& paramSyntax = syntax->template as<TypeParameterDeclarationSyntax>();
            for (auto decl : paramSyntax.declarators)
                parameters.emplace(scope, paramSyntax, *decl, isLocal, isPort);
        }
    };

    // Find all port parameters.
    bool hasPortParams = header.parameters != nullptr;
    if (hasPortParams) {
        bool lastLocal = false;
        for (auto declaration : header.parameters->declarations) {
            // It's legal to leave off the parameter keyword in the parameter port list.
            // If you do so, we "inherit" the parameter or localparam keyword from the
            // previous entry. This isn't allowed in a definition body, but the parser
            // will take care of the error for us.
            if (declaration->keyword)
                lastLocal = declaration->keyword.kind == TokenKind::LocalParamKeyword;

            createParams(declaration, lastLocal, /* isPort */ true);
        }
    }

    bool first = true;
    optional<SourceRange> unitsRange;
    optional<SourceRange> precisionRange;

    for (auto member : syntax.members) {
        if (member->kind == SyntaxKind::TimeUnitsDeclaration) {
            timeScale.setFromSyntax(scope, member->as<TimeUnitsDeclarationSyntax>(), unitsRange,
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
            createParams(declaration, isLocal, /* isPort */ false);
        }
    }

    timeScale.setDefault(scope, directiveTimeScale, unitsRange.has_value(),
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
                    string_view simpleName = SyntaxFacts::getSimpleTypeName(*vph.dataType);
                    if (!simpleName.empty()) {
                        auto def = scope.getCompilation().getDefinition(simpleName, scope);
                        if (def && def->definitionKind == DefinitionKind::Interface)
                            isIface = true;
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
            else {
                auto& eap = port->as<ExplicitNonAnsiPortSyntax>();
                ports.emplace(eap.name.valueText(), index, /* isIface */ false);
            }

            index++;
        }
    }
}

} // namespace slang