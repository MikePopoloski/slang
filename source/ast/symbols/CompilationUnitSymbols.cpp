//------------------------------------------------------------------------------
// CompilationUnitSymbols.cpp
// Contains compilation unit-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/CompilationUnitSymbols.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

CompilationUnitSymbol::CompilationUnitSymbol(Compilation& compilation) :
    Symbol(SymbolKind::CompilationUnit, "", SourceLocation()), Scope(compilation, this) {

    // Default the time scale to the compilation default. If it turns out
    // this scope has a time unit declaration it will overwrite the member.
    timeScale = compilation.getDefaultTimeScale();

    // All compilation units import the std package automatically.
    auto& stdPkg = compilation.getStdPackage();
    auto import = compilation.emplace<WildcardImportSymbol>(stdPkg.name,
                                                            SourceLocation::NoLocation);
    import->setPackage(stdPkg);
    addWildcardImport(*import);
}

void CompilationUnitSymbol::addMembers(const SyntaxNode& syntax) {
    if (syntax.kind == SyntaxKind::TimeUnitsDeclaration) {
        if (!timeScale)
            timeScale.emplace();

        SemanticFacts::populateTimeScale(*timeScale, *this, syntax.as<TimeUnitsDeclarationSyntax>(),
                                         unitsRange, precisionRange, !anyMembers);
    }
    else if (syntax.kind == SyntaxKind::CompilationUnit) {
        auto& cu = syntax.as<CompilationUnitSyntax>();
        if (!cu.members.empty()) {
            anyMembers = true;
            for (auto member : cu.members)
                Scope::addMembers(*member);
        }
    }
    else {
        anyMembers = true;
        Scope::addMembers(syntax);
    }
}

PackageSymbol::PackageSymbol(Compilation& compilation, std::string_view name, SourceLocation loc,
                             const NetType& defaultNetType, VariableLifetime defaultLifetime) :
    Symbol(SymbolKind::Package, name, loc),
    Scope(compilation, this), defaultNetType(defaultNetType), defaultLifetime(defaultLifetime) {
}

PackageSymbol& PackageSymbol::fromSyntax(const Scope& scope, const ModuleDeclarationSyntax& syntax,
                                         const NetType& defaultNetType,
                                         std::optional<TimeScale> directiveTimeScale) {
    auto& comp = scope.getCompilation();
    auto lifetime = SemanticFacts::getVariableLifetime(syntax.header->lifetime);
    auto result = comp.emplace<PackageSymbol>(comp, syntax.header->name.valueText(),
                                              syntax.header->name.location(), defaultNetType,
                                              lifetime.value_or(VariableLifetime::Static));
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    bool first = true;
    std::optional<SourceRange> unitsRange;
    std::optional<SourceRange> precisionRange;
    SmallVector<const PackageImportItemSyntax*> exportDecls;

    for (auto member : syntax.members) {
        if (member->kind == SyntaxKind::TimeUnitsDeclaration) {
            if (!result->timeScale)
                result->timeScale.emplace();

            SemanticFacts::populateTimeScale(*result->timeScale, scope,
                                             member->as<TimeUnitsDeclarationSyntax>(), unitsRange,
                                             precisionRange, first);
            continue;
        }

        first = false;

        if (member->kind == SyntaxKind::PackageExportAllDeclaration) {
            result->hasExportAll = true;
        }
        else if (member->kind == SyntaxKind::PackageExportDeclaration) {
            for (auto item : member->as<PackageExportDeclarationSyntax>().items)
                exportDecls.push_back(item);
        }

        result->addMembers(*member);
    }

    result->exportDecls = exportDecls.copy(comp);

    SemanticFacts::populateTimeScale(result->timeScale, scope, directiveTimeScale, unitsRange,
                                     precisionRange);
    return *result;
}

const Symbol* PackageSymbol::findForImport(std::string_view lookupName) const {
    auto sym = find(lookupName);
    if (sym)
        return sym;

    if (!hasExportAll && exportDecls.empty())
        return nullptr;

    // We need to force-elaborate the entire package body because any
    // lookups that result in a wildcard import could add to our export list.
    auto& comp = getCompilation();
    if (!hasForceElaborated) {
        hasForceElaborated = true;
        comp.forceElaborate(*this);
    }

    return comp.findPackageExportCandidate(*this, lookupName);
}

void PackageSymbol::noteImport(const Symbol& symbol) const {
    // If we have an export directive for this symbol then add it to the list of export candidates.
    auto& comp = getCompilation();
    if (hasExportAll) {
        comp.notePackageExportCandidate(*this, symbol);
        return;
    }

    if (exportDecls.empty())
        return;

    const Symbol* packageParent;
    auto targetScope = symbol.getParentScope();
    while (true) {
        SLANG_ASSERT(targetScope);
        packageParent = &targetScope->asSymbol();
        if (packageParent->kind == SymbolKind::Package)
            break;

        targetScope = packageParent->getParentScope();
    }

    for (auto decl : exportDecls) {
        if (decl->package.valueText() != packageParent->name)
            continue;

        if (decl->item.kind == TokenKind::Star || decl->item.valueText() == symbol.name) {
            comp.notePackageExportCandidate(*this, symbol);
            return;
        }
    }
}

ConfigBlockSymbol& ConfigBlockSymbol::fromSyntax(const Scope& scope,
                                                 const ConfigDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<ConfigBlockSymbol>(comp, syntax.name.valueText(),
                                                  syntax.name.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    for (auto param : syntax.localparams)
        result->addMembers(*param);

    return *result;
}

void ConfigBlockSymbol::serializeTo(ASTSerializer&) const {
}

} // namespace slang::ast
