//------------------------------------------------------------------------------
// NetType.cpp
// Type class for nettypes
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/NetType.h"

#include "slang/compilation/Compilation.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/Type.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

NetType::NetType(NetKind netKind, string_view name, const Type& dataType) :
    Symbol(SymbolKind::NetType, name, SourceLocation()), netKind(netKind), declaredType(*this),
    isResolved(true) {

    declaredType.setType(dataType);
}

NetType::NetType(string_view name, SourceLocation location) :
    Symbol(SymbolKind::NetType, name, location), netKind(UserDefined),
    declaredType(*this, DeclaredTypeFlags::UserDefinedNetType) {
}

const NetType* NetType::getAliasTarget() const {
    if (!isResolved)
        resolve();
    return alias;
}

const NetType& NetType::getCanonical() const {
    if (auto target = getAliasTarget())
        return target->getCanonical();
    return *this;
}

const Type& NetType::getDataType() const {
    if (!isResolved)
        resolve();
    return declaredType.getType();
}

const SubroutineSymbol* NetType::getResolutionFunction() const {
    if (!isResolved)
        resolve();
    return resolver;
}

void NetType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("type", getDataType());
    if (auto target = getAliasTarget())
        serializer.write("target", *target);
}

NetType& NetType::fromSyntax(const Scope& scope, const NetTypeDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<NetType>(syntax.name.valueText(), syntax.name.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    // If this is an enum, make sure the declared type is set up before we get added to
    // any scope, so that the enum members get picked up correctly.
    if (syntax.type->kind == SyntaxKind::EnumType)
        result->declaredType.setTypeSyntax(*syntax.type);

    return *result;
}

void NetType::resolve() const {
    ASSERT(!isResolved);
    isResolved = true;

    auto syntaxNode = getSyntax();
    ASSERT(syntaxNode);

    auto scope = getParentScope();
    ASSERT(scope);

    auto& declSyntax = syntaxNode->as<NetTypeDeclarationSyntax>();
    if (declSyntax.withFunction) {
        // TODO: lookup and validate the function here
    }

    // If this is an enum, we already set the type earlier.
    if (declSyntax.type->kind == SyntaxKind::EnumType)
        return;

    // Our type syntax is either a link to another net type we are aliasing, or an actual
    // data type that we are using as the basis for a custom net type.
    if (declSyntax.type->kind == SyntaxKind::NamedType) {
        LookupResult result;
        const NameSyntax& nameSyntax = *declSyntax.type->as<NamedTypeSyntax>().name;
        Lookup::name(*scope, nameSyntax, LookupLocation::before(*this), LookupFlags::Type, result);

        if (result.found && result.found->kind == SymbolKind::NetType) {
            if (result.hasError())
                scope->getCompilation().addDiagnostics(result.getDiagnostics());

            alias = &result.found->as<NetType>();
            declaredType.copyTypeFrom(alias->getCanonical().declaredType);
            return;
        }
    }

    declaredType.setTypeSyntax(*declSyntax.type);
}

} // namespace slang
