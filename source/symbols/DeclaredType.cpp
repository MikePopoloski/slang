//------------------------------------------------------------------------------
// DeclaredType.cpp
// Glue logic between symbols and their declared types
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/DeclaredType.h"

#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/symbols/AllTypes.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/Symbol.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/ScopeGuard.h"

namespace slang {

DeclaredType::DeclaredType(const Symbol& parent, bitmask<DeclaredTypeFlags> flags) :
    parent(parent), flags(flags) {
    // If this assert fires you need to update Symbol::getDeclaredType
    ASSERT(parent.getDeclaredType() == this);
}

const Type& DeclaredType::getType() const {
    if (!type)
        resolveType(getBindContext());
    return *type;
}

void DeclaredType::setDimensionSyntax(const SyntaxList<VariableDimensionSyntax>& newDimensions) {
    dimensions = &newDimensions;
    type = nullptr;
}

void DeclaredType::copyTypeFrom(const DeclaredType& source) {
    if (auto ts = source.getTypeSyntax()) {
        setTypeSyntax(*ts);
        if (auto dims = source.getDimensionSyntax())
            setDimensionSyntax(*dims);
    }

    type = source.type;
}

const Scope& DeclaredType::getScope() const {
    const Scope* scope = parent.getParentScope();
    ASSERT(scope);
    return *scope;
}

void DeclaredType::resolveType(const BindContext& initializerContext) const {
    // If this is a foreach variable, we need to look up the array in
    // order to know our type.
    if ((flags & DeclaredTypeFlags::ForeachVar) != 0) {
        type = resolveForeachVar(initializerContext);
        return;
    }

    auto& scope = getScope();
    auto& comp = scope.getCompilation();
    if (!typeSyntax) {
        type = &comp.getErrorType();
        return;
    }

    ASSERT(!evaluating);
    evaluating = true;
    auto guard = ScopeGuard([this] { evaluating = false; });

    if (typeSyntax->kind == SyntaxKind::ImplicitType &&
        (flags & DeclaredTypeFlags::InferImplicit) != 0) {
        if (dimensions) {
            scope.addDiag(diag::UnpackedArrayParamType, dimensions->sourceRange());
            type = &comp.getErrorType();
        }
        else if (!initializerSyntax) {
            type = &comp.getErrorType();
        }
        else {
            initializer = &Expression::bindImplicitParam(*typeSyntax, *initializerSyntax,
                                                         initializerLocation, initializerContext);
            type = initializer->type;
        }
        return;
    }

    BindContext typeContext = getBindContext();
    type = &comp.getType(*typeSyntax, typeContext.lookupLocation, scope,
                         (flags & DeclaredTypeFlags::ForceSigned) != 0);
    if (dimensions)
        type = &comp.getType(*type, *dimensions, typeContext.lookupLocation, scope);
}

const Type* DeclaredType::resolveForeachVar(const BindContext& context) const {
    // This is kind of an unfortunate layering violation.
    auto& comp = context.getCompilation();
    auto& var = parent.as<VariableSymbol>();
    auto syntax = var.getSyntax();
    ASSERT(syntax && syntax->parent);

    // Walk up to the parent foreach loop syntax.
    auto arrayName = syntax->parent->as<ForeachLoopListSyntax>().arrayName;

    // Lookup failures will be diagnosed later, so if we can't find the
    // array here just give up quietly.
    LookupResult result;
    Lookup::name(context.scope, *arrayName, context.lookupLocation, LookupFlags::None, result);
    if (!result.found)
        return &comp.getErrorType();

    auto declType = result.found->getDeclaredType();
    if (!declType)
        return &comp.getErrorType();

    const Type* currType = &declType->getType();
    for (int32_t i = var.foreachIndex - 1; i > 0; i--) {
        if (!currType->isArray())
            return &comp.getErrorType();

        currType = currType->getArrayElementType();
    }

    if (!currType->isArray())
        return &comp.getErrorType();

    // If this is an associative array, we take the type from the index type.
    // Otherwise, for all this work, we just end up with an int index.
    if (currType->isAssociativeArray()) {
        currType = currType->getCanonicalType().as<AssociativeArrayType>().indexType;
        if (!currType) {
            context.addDiag(diag::ForeachWildcardIndex, syntax->sourceRange())
                << arrayName->sourceRange();
            return &comp.getErrorType();
        }

        return currType;
    }

    return &comp.getIntType();
}

void DeclaredType::resolveAt(const BindContext& context) const {
    if (!initializerSyntax)
        return;

    if (!type) {
        resolveType(context);
        if (initializer)
            return;
    }

    ASSERT(!evaluating);
    evaluating = true;
    auto guard = ScopeGuard([this] { evaluating = false; });

    // Enums are special in that their initializers target the base type of the enum
    // instead of the actual enum type (which doesn't allow implicit conversions from
    // normal integral values).
    auto& scope = context.scope;
    bitmask<BindFlags> bindFlags = context.flags;
    const Type* targetType = type;
    if (targetType->isEnum() && scope.asSymbol().kind == SymbolKind::EnumType) {
        targetType = &targetType->as<EnumType>().baseType;
        bindFlags |= BindFlags::EnumInitializer;
    }

    initializer = &Expression::bindRValue(*targetType, *initializerSyntax, initializerLocation,
                                          context.resetFlags(bindFlags));
}

const Expression* DeclaredType::getInitializer() const {
    if (initializer)
        return initializer;

    resolveAt(getBindContext());
    return initializer;
}

void DeclaredType::setFromDeclarator(const DeclaratorSyntax& decl) {
    if (!decl.dimensions.empty())
        setDimensionSyntax(decl.dimensions);
    if (decl.initializer)
        setInitializerSyntax(*decl.initializer->expr, decl.initializer->equals.location());
}

template<typename T>
T DeclaredType::getBindContext() const {
    bitmask<BindFlags> bindFlags;
    if (flags & DeclaredTypeFlags::RequireConstant)
        bindFlags = BindFlags::Constant;
    if (flags & DeclaredTypeFlags::InProceduralContext)
        bindFlags |= BindFlags::ProceduralStatement;
    if ((flags & DeclaredTypeFlags::AutomaticInitializer) == 0)
        bindFlags |= BindFlags::StaticInitializer;

    LookupLocation location;
    if (flags & DeclaredTypeFlags::LookupMax)
        location = LookupLocation::max;
    else
        location = LookupLocation::after(parent);

    return BindContext(getScope(), location, bindFlags);
}

} // namespace slang