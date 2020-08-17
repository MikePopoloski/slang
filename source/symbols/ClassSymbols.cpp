//------------------------------------------------------------------------------
// ClassSymbols.cpp
// Class-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/ClassSymbols.h"

#include "slang/compilation/Compilation.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

ClassType::ClassType(Compilation& compilation, string_view name, SourceLocation loc) :
    Type(SymbolKind::ClassType, name, loc), Scope(compilation, this) {
}

ConstantValue ClassType::getDefaultValueImpl() const {
    return ConstantValue::NullPlaceholder{};
}

const Type& ClassType::fromSyntax(const Scope& scope, const ClassDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    if (syntax.virtualOrInterface) {
        // TODO: support this
        scope.addDiag(diag::NotYetSupported, syntax.virtualOrInterface.range());
        return comp.getErrorType();
    }

    auto result = comp.emplace<ClassType>(comp, syntax.name.valueText(), syntax.name.location());
    result->setSyntax(syntax);
    for (auto member : syntax.items)
        result->addMembers(*member);

    // TODO: parameters
    // TODO: extends
    // TODO: implements
    // TODO: lifetime

    return *result;
}

} // namespace slang
