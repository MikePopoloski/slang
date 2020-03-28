//------------------------------------------------------------------------------
// Definition.cpp
// Module / interface / program definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/compilation/Definition.h"

#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/symbols/AttributeSymbol.h"
#include "slang/symbols/Scope.h"
#include "slang/syntax/AllSyntax.h"

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

Definition::Definition(const Scope& scope, LookupLocation lookupLocation,
                       const ModuleDeclarationSyntax& syntax, const NetType& defaultNetType,
                       UnconnectedDrive unconnectedDrive, optional<TimeScale> directiveTimeScale) :
    syntax(syntax),
    defaultNetType(defaultNetType), unconnectedDrive(unconnectedDrive) {

    // Extract and save various properties of the definition.
    auto& header = *syntax.header;
    name = header.name.valueText();
    location = header.name.location();
    definitionKind = SemanticFacts::getDefinitionKind(syntax.kind);
    defaultLifetime =
        SemanticFacts::getVariableLifetime(header.lifetime).value_or(VariableLifetime::Static);
    attributes = AttributeSymbol::fromSyntax(syntax.attributes, scope, lookupLocation);

    auto createParams = [&](auto syntax, bool isLocal, bool isPort) {
        if (syntax->kind == SyntaxKind::ParameterDeclaration) {
            auto& paramSyntax = syntax->as<ParameterDeclarationSyntax>();
            for (auto decl : paramSyntax.declarators)
                parameters.emplace(scope, paramSyntax, *decl, isLocal, isPort);
        }
        else {
            auto& paramSyntax = syntax->as<TypeParameterDeclarationSyntax>();
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
        if (member->kind != SyntaxKind::ParameterDeclarationStatement)
            continue;

        auto declaration = member->as<ParameterDeclarationStatementSyntax>().parameter;
        bool isLocal = hasPortParams || declaration->keyword.kind == TokenKind::LocalParamKeyword;
        createParams(declaration, isLocal, /* isPort */ false);
    }

    // If no time unit was set, infer one based on the following rules:
    // - If the scope is nested (inside another definition), inherit from that definition.
    // - Otherwise use a `timescale directive if there is one.
    // - Otherwise, look for a time unit in the compilation scope.
    // - Finally use the compilation default.
    if (unitsRange && precisionRange)
        return;

    optional<TimeScale> ts;
    if (scope.asSymbol().kind == SymbolKind::CompilationUnit)
        ts = directiveTimeScale;

    if (!ts)
        ts = scope.getTimeScale();

    if (!unitsRange)
        timeScale.base = ts->base;
    if (!precisionRange)
        timeScale.precision = ts->precision;

    // TODO: error if inferred timescale is invalid (because precision > units)

    // TODO:
    // result->setAttributes(scope, syntax.attributes);
}

} // namespace slang