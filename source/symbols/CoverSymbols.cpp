//------------------------------------------------------------------------------
// CoverSymbols.cpp
// Contains coverage-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/CoverSymbols.h"

#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

CovergroupType::CovergroupType(Compilation& compilation, string_view name, SourceLocation loc) :
    Type(SymbolKind::CovergroupType, name, loc), Scope(compilation, this) {
}

const Symbol& CovergroupType::fromSyntax(const Scope& scope,
                                         const CovergroupDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result =
        comp.emplace<CovergroupType>(comp, syntax.name.valueText(), syntax.name.location());

    if (syntax.portList) {
        SmallVectorSized<const FormalArgumentSymbol*, 8> args;
        SubroutineSymbol::buildArguments(*result, *syntax.portList, VariableLifetime::Automatic,
                                         args);
        result->arguments = args.copy(comp);

        for (auto arg : result->arguments) {
            if (arg->direction == ArgumentDirection::Out ||
                arg->direction == ArgumentDirection::InOut) {
                scope.addDiag(diag::CovergroupOutArg, arg->location);
            }
        }
    }

    return *result;
}

ConstantValue CovergroupType::getDefaultValueImpl() const {
    return ConstantValue::NullPlaceholder{};
}

void CovergroupType::serializeTo(ASTSerializer&) const {
    // TODO:
}

} // namespace slang
