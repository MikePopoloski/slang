//------------------------------------------------------------------------------
// CompilationUnitSymbols.cpp
// Contains compilation unit-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/CompilationUnitSymbols.h"

#include "slang/compilation/Compilation.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

CompilationUnitSymbol::CompilationUnitSymbol(Compilation& compilation) :
    Symbol(SymbolKind::CompilationUnit, "", SourceLocation()), Scope(compilation, this) {

    // Default the time scale to the compilation default. If it turns out
    // this scope has a time unit declaration it will overwrite the member.
    timeScale = compilation.getDefaultTimeScale();
}

void CompilationUnitSymbol::addMembers(const SyntaxNode& syntax) {
    if (syntax.kind == SyntaxKind::TimeUnitsDeclaration) {
        timeScale.setFromSyntax(*this, syntax.as<TimeUnitsDeclarationSyntax>(), unitsRange,
                                precisionRange, !anyMembers);
    }
    else {
        anyMembers = true;
        Scope::addMembers(syntax);
    }
}

PackageSymbol::PackageSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                             const NetType& defaultNetType) :
    Symbol(SymbolKind::Package, name, loc),
    Scope(compilation, this), defaultNetType(defaultNetType) {
}

PackageSymbol& PackageSymbol::fromSyntax(Compilation& compilation,
                                         const ModuleDeclarationSyntax& syntax,
                                         const Scope& scope) {
    auto result = compilation.emplace<PackageSymbol>(compilation, syntax.header->name.valueText(),
                                                     syntax.header->name.location(),
                                                     compilation.getDefaultNetType(syntax));
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    bool first = true;
    optional<SourceRange> unitsRange;
    optional<SourceRange> precisionRange;

    for (auto member : syntax.members) {
        if (member->kind == SyntaxKind::TimeUnitsDeclaration) {
            result->timeScale.setFromSyntax(scope, member->as<TimeUnitsDeclarationSyntax>(),
                                            unitsRange, precisionRange, first);
            continue;
        }

        first = false;
        result->addMembers(*member);
    }

    result->timeScale.setDefault(scope, compilation.getDirectiveTimeScale(syntax),
                                 unitsRange.has_value(), precisionRange.has_value());
    return *result;
}

} // namespace slang
