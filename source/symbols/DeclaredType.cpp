//------------------------------------------------------------------------------
// DeclaredType.h
// Glue logic between symbols and their declared types.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/DeclaredType.h"

#include "slang/compilation/Compilation.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/Symbol.h"

namespace slang {

DeclaredType::DeclaredType(const Symbol& parent, bitmask<DeclaredTypeFlags> flags) :
    parent(parent), flags(flags)
{
    // If this assert fires you need to update Symbol::getDeclaredType
    ASSERT(parent.getDeclaredType() == this);
}

const Scope& DeclaredType::getScope() const {
    const Scope* scope = parent.getScope();
    ASSERT(scope);
    return *scope;
}

void DeclaredType::resolveType() const {
    ASSERT(!evaluating);
    ASSERT(typeSyntax);
    evaluating = true;
    auto guard = finally([this] { evaluating = false; });

    auto& scope = getScope();
    if (typeSyntax->kind == SyntaxKind::ImplicitType) {
        if ((flags & DeclaredTypeFlags::AllowImplicit) == 0 || !initializerSyntax)
            type = &scope.getCompilation().getErrorType();
        else {
            initializer = &Expression::bind(scope.getCompilation(), *initializerSyntax, getBindContext());
            type = initializer->type;
        }
    }
    else {
        type = &scope.getCompilation().getType(*typeSyntax, LookupLocation::after(parent), scope);
        if (dimensions)
            type = &scope.getCompilation().getType(*type, *dimensions, LookupLocation::after(parent), scope);
    }
}

const Expression* DeclaredType::getInitializer() const {
    if (initializer || !initializerSyntax)
        return initializer;

    if (!type) {
        resolveType();
        if (initializer)
            return initializer;
    }

    ASSERT(!evaluating);
    evaluating = true;
    auto guard = finally([this] { evaluating = false; });

    // Enums are special in that their initializers target the base type of the enum
    // instead of the actual enum type (which doesn't allow implicit conversions from
    // normal integral values).
    auto& scope = getScope();
    const Type* targetType = type;
    if (targetType->isEnum() && scope.asSymbol().kind == SymbolKind::EnumType)
        targetType = &targetType->as<EnumType>().baseType;

    initializer = &Expression::bind(scope.getCompilation(), *targetType, *initializerSyntax,
                                    initializerLocation, getBindContext());
    return initializer;
}

void DeclaredType::setFromDeclarator(const VariableDeclaratorSyntax& decl) {
    if (!decl.dimensions.empty())
        setDimensionSyntax(decl.dimensions);
    if (decl.initializer)
        setInitializerSyntax(*decl.initializer->expr, decl.initializer->equals.location());
}

const ConstantValue& DeclaredType::getConstantValue() const {
    auto init = getInitializer();
    if (!init || !init->constant)
        return ConstantValue::Invalid;

    return *init->constant;
}

template<typename T>
T DeclaredType::getBindContext() const {
    bitmask<BindFlags> bindFlags;
    if (flags & DeclaredTypeFlags::RequireConstant)
        bindFlags = BindFlags::Constant;
    if (flags & DeclaredTypeFlags::RequireIntegerConstant)
        bindFlags = BindFlags::IntegralConstant;

    return BindContext(getScope(), LookupLocation::after(parent), bindFlags);
}

}