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
    parent(parent), flags(flags) {
    // If this assert fires you need to update Symbol::getDeclaredType
    ASSERT(parent.getDeclaredType() == this);
}

void DeclaredType::copyTypeFrom(const DeclaredType& source) {
    if (auto ts = source.getTypeSyntax()) {
        setTypeSyntax(*ts);
        if (auto dims = source.getDimensionSyntax())
            setDimensionSyntax(*dims);
    }

    if (source.isTypeResolved())
        setType(source.getType());
}

std::tuple<const Type*, const Expression*> DeclaredType::resolveType(
    const DataTypeSyntax& typeSyntax, const SyntaxList<VariableDimensionSyntax>* dimensions,
    const ExpressionSyntax* initializerSyntax, const BindContext& context,
    bitmask<DeclaredTypeFlags> flags) {

    auto& scope = context.scope;
    auto& comp = scope.getCompilation();

    const Type* type = nullptr;
    const Expression* initializer = nullptr;

    if (typeSyntax.kind == SyntaxKind::ImplicitType &&
        (flags & DeclaredTypeFlags::InferImplicit) != 0) {
        // TODO: handle unpacked dimensions here?
        // TODO: make sure errors are issued elsewhere for when implicit is not allowed
        if (!initializerSyntax)
            type = &comp.getErrorType();
        else {
            initializer = &Expression::bind(*initializerSyntax, context);
            type = initializer->type;
        }
    }
    else {
        type = &comp.getType(typeSyntax, context.lookupLocation, scope,
                             (flags & DeclaredTypeFlags::ForceSigned) != 0);
        if (dimensions)
            type = &comp.getType(*type, *dimensions, context.lookupLocation, scope);
    }

    return { type, initializer };
}

const Expression& DeclaredType::resolveInitializer(const Type& type,
                                                   const ExpressionSyntax& initializerSyntax,
                                                   SourceLocation initializerLocation,
                                                   const BindContext& context) {
    // Enums are special in that their initializers target the base type of the enum
    // instead of the actual enum type (which doesn't allow implicit conversions from
    // normal integral values).
    auto& scope = context.scope;
    bitmask<BindFlags> flags = context.flags;
    const Type* targetType = &type;
    if (targetType->isEnum() && scope.asSymbol().kind == SymbolKind::EnumType) {
        targetType = &targetType->as<EnumType>().baseType;
        flags |= BindFlags::EnumInitializer;
    }

    return Expression::bind(*targetType, initializerSyntax, initializerLocation,
                            context.resetFlags(flags));
}

const Expression& DeclaredType::resolveInitializer(
    const DataTypeSyntax& typeSyntax, const SyntaxList<VariableDimensionSyntax>* dimensions,
    const ExpressionSyntax& initializerSyntax, SourceLocation initializerLocation,
    const BindContext& context, bitmask<DeclaredTypeFlags> flags) {

    auto [type, initializer] =
        resolveType(typeSyntax, dimensions, &initializerSyntax, context, flags);
    if (initializer)
        return *initializer;

    return resolveInitializer(*type, initializerSyntax, initializerLocation, context);
}

const Scope& DeclaredType::getScope() const {
    const Scope* scope = parent.getScope();
    ASSERT(scope);
    return *scope;
}

void DeclaredType::resolveType() const {
    if (!typeSyntax) {
        type = &getScope().getCompilation().getErrorType();
        return;
    }

    ASSERT(!evaluating);
    evaluating = true;
    auto guard = finally([this] { evaluating = false; });

    auto [t, i] = resolveType(*typeSyntax, dimensions, initializerSyntax, getBindContext(), flags);
    type = t;
    initializer = i;
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

    initializer =
        &resolveInitializer(*type, *initializerSyntax, initializerLocation, getBindContext());
    return initializer;
}

void DeclaredType::setFromDeclarator(const DeclaratorSyntax& decl) {
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

    return BindContext(getScope(), LookupLocation::after(parent), bindFlags);
}

} // namespace slang