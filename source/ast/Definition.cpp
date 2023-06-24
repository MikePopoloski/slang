//------------------------------------------------------------------------------
// Definition.cpp
// Module / interface / program definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Definition.h"

#include "../ast/symbols/ParameterBuilder.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/Scope.h"
#include "slang/ast/symbols/AttributeSymbol.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

Definition::ParameterDecl::ParameterDecl(
    const Scope& scope, const ParameterDeclarationSyntax& syntax, const DeclaratorSyntax& decl,
    bool isLocal, bool isPort, std::span<const syntax::AttributeInstanceSyntax* const> attributes) :
    valueSyntax(&syntax),
    valueDecl(&decl), attributes(attributes), isTypeParam(false), isLocalParam(isLocal),
    isPortParam(isPort), hasSyntax(true) {

    name = decl.name.valueText();
    location = decl.name.location();

    if (!decl.initializer) {
        if (!isPort)
            scope.addDiag(diag::BodyParamNoInitializer, location);
        else if (isLocal)
            scope.addDiag(diag::LocalParamNoInitializer, location);
    }
}

Definition::ParameterDecl::ParameterDecl(
    const Scope& scope, const TypeParameterDeclarationSyntax& syntax,
    const TypeAssignmentSyntax& decl, bool isLocal, bool isPort,
    std::span<const syntax::AttributeInstanceSyntax* const> attributes) :
    typeSyntax(&syntax),
    typeDecl(&decl), attributes(attributes), isTypeParam(true), isLocalParam(isLocal),
    isPortParam(isPort), hasSyntax(true) {

    name = decl.name.valueText();
    location = decl.name.location();

    if (!decl.assignment) {
        if (!isPort)
            scope.addDiag(diag::BodyParamNoInitializer, location);
        else if (isLocal)
            scope.addDiag(diag::LocalParamNoInitializer, location);
    }
}

Definition::ParameterDecl::ParameterDecl(std::string_view name, SourceLocation location,
                                         const Type& givenType, bool isLocal, bool isPort,
                                         const Expression* givenInitializer) :
    givenType(&givenType),
    givenInitializer(givenInitializer), name(name), location(location), isTypeParam(false),
    isLocalParam(isLocal), isPortParam(isPort), hasSyntax(false) {
    SLANG_ASSERT(givenInitializer || (isPort && !isLocal));
}

Definition::ParameterDecl::ParameterDecl(std::string_view name, SourceLocation location,
                                         bool isLocal, bool isPort, const Type* defaultType) :
    givenType(defaultType),
    name(name), location(location), isTypeParam(true), isLocalParam(isLocal), isPortParam(isPort),
    hasSyntax(false) {
    SLANG_ASSERT(givenType || (isPort && !isLocal));
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
                       UnconnectedDrive unconnectedDrive,
                       std::optional<TimeScale> directiveTimeScale, const SyntaxTree* syntaxTree) :
    syntax(syntax),
    defaultNetType(defaultNetType), scope(scope), unconnectedDrive(unconnectedDrive),
    syntaxTree(syntaxTree) {

    // Extract and save various properties of the definition.
    name = syntax.header->name.valueText();
    location = syntax.header->name.location();
    indexInScope = lookupLocation.getIndex();
    definitionKind = SemanticFacts::getDefinitionKind(syntax.kind);
    defaultLifetime = SemanticFacts::getVariableLifetime(syntax.header->lifetime)
                          .value_or(VariableLifetime::Static);
    attributes = AttributeSymbol::fromSyntax(syntax.attributes, scope, lookupLocation);

    auto header = syntax.header.get();
    if (header->ports && header->ports->kind == SyntaxKind::WildcardPortList) {
        auto& comp = scope.getCompilation();
        auto externMod = comp.getExternModule(name, scope);
        if (!externMod)
            scope.addDiag(diag::MissingExternWildcardPorts, header->ports->sourceRange()) << name;
        else
            header = externMod->header;
    }

    portList = header->ports;
    hasNonAnsiPorts = portList && portList->kind == SyntaxKind::NonAnsiPortList;

    // Find all port parameters.
    bool hasPortParams = header->parameters != nullptr;
    if (hasPortParams)
        ParameterBuilder::createDecls(scope, *header->parameters, parameters);

    bool first = true;
    std::optional<SourceRange> unitsRange;
    std::optional<SourceRange> precisionRange;

    for (auto member : syntax.members) {
        if (member->kind == SyntaxKind::TimeUnitsDeclaration) {
            if (!timeScale)
                timeScale.emplace();

            SemanticFacts::populateTimeScale(*timeScale, scope,
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
            bool isLocal = hasPortParams ||
                           declaration->keyword.kind == TokenKind::LocalParamKeyword;

            ParameterBuilder::createDecls(scope, *declaration, isLocal, /* isPort */ false,
                                          member->attributes, parameters);
        }
    }

    SemanticFacts::populateTimeScale(timeScale, scope, directiveTimeScale, unitsRange,
                                     precisionRange);
}

std::string_view Definition::getKindString() const {
    switch (definitionKind) {
        case DefinitionKind::Module:
            return "module"sv;
        case DefinitionKind::Interface:
            return "interface"sv;
        case DefinitionKind::Program:
            return "program"sv;
        default:
            SLANG_UNREACHABLE;
    }
}

std::string_view Definition::getArticleKindString() const {
    switch (definitionKind) {
        case DefinitionKind::Module:
            return "a module"sv;
        case DefinitionKind::Interface:
            return "an interface"sv;
        case DefinitionKind::Program:
            return "a program"sv;
        default:
            SLANG_UNREACHABLE;
    }
}

void Definition::getHierarchicalPath(std::string& buffer) const {
    auto& parentSym = scope.asSymbol();
    if (parentSym.kind != SymbolKind::Root && parentSym.kind != SymbolKind::CompilationUnit) {
        parentSym.getHierarchicalPath(buffer);
        buffer.append(".");
    }

    buffer.append(name);
}

} // namespace slang::ast
