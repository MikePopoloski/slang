//------------------------------------------------------------------------------
// NetType.cpp
// Type class for nettypes
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/types/NetType.h"

#include "slang/binding/BindContext.h"
#include "slang/compilation/Compilation.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/Scope.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/Type.h"

namespace slang {

NetType::NetType(NetKind netKind, string_view name, const Type& dataType) :
    Symbol(SymbolKind::NetType, name, SourceLocation()), declaredType(*this), netKind(netKind) {
    declaredType.setType(dataType);
}

NetType::NetType(string_view name, SourceLocation location) :
    Symbol(SymbolKind::NetType, name, location),
    declaredType(*this, DeclaredTypeFlags::UserDefinedNetType), netKind(UserDefined) {
}

const SubroutineSymbol* NetType::getResolutionFunction() const {
    if (resolver)
        return *resolver;

    auto syntax = getSyntax();
    auto scope = getParentScope();
    ASSERT(syntax && scope);

    auto& declSyntax = syntax->as<NetTypeDeclarationSyntax>();
    if (declSyntax.withFunction) {
        // TODO: lookup and validate the function here
    }

    resolver = nullptr;
    return *resolver;
}

void NetType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("type", getDataType());
}

NetType& NetType::fromSyntax(const Scope& scope, const NetTypeDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<NetType>(syntax.name.valueText(), syntax.name.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);
    result->declaredType.setTypeSyntax(*syntax.type);

    return *result;
}

} // namespace slang
