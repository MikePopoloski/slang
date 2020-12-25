//------------------------------------------------------------------------------
// DeclaredType.cpp
// Glue logic between symbols and their declared types
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/types/DeclaredType.h"

#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/Symbol.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/AllTypes.h"
#include "slang/types/NetType.h"
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

void DeclaredType::mergeImplicitPort(
    const ImplicitTypeSyntax& implicit, SourceLocation location,
    span<const VariableDimensionSyntax* const> unpackedDimensions) {
    mergePortTypes(getBindContext(), parent.as<ValueSymbol>(), implicit, location,
                   unpackedDimensions);
}

const Scope& DeclaredType::getScope() const {
    const Scope* scope = parent.getParentScope();
    ASSERT(scope);
    return *scope;
}

void DeclaredType::resolveType(const BindContext& initializerContext) const {
    auto& scope = getScope();
    auto& comp = scope.getCompilation();
    if (!typeSyntax) {
        type = &comp.getErrorType();
        return;
    }

    ASSERT(!evaluating);
    evaluating = true;
    auto guard = ScopeGuard([this] { evaluating = false; });

    // If we are configured to infer implicit types, bind the initializer expression
    // first so that we can derive our type from whatever that happens to be.
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
    }
    else {
        const Type* typedefTarget = nullptr;
        if (flags.has(DeclaredTypeFlags::TypedefTarget))
            typedefTarget = &parent.as<Type>();

        BindContext typeContext = getBindContext();
        type = &comp.getType(*typeSyntax, typeContext.lookupLocation, scope, typedefTarget);
        if (dimensions)
            type = &comp.getType(*type, *dimensions, typeContext.lookupLocation, scope);
    }

    if (flags.has(DeclaredTypeFlags::NeedsTypeCheck) && !type->isError())
        checkType(initializerContext);
}

static bool isValidForNet(const Type& type) {
    auto& ct = type.getCanonicalType();
    if (ct.isIntegral())
        return ct.isFourState();

    if (ct.kind == SymbolKind::FixedSizeUnpackedArrayType)
        return isValidForNet(ct.as<FixedSizeUnpackedArrayType>().elementType);

    if (ct.isUnpackedStruct()) {
        for (auto& field : ct.as<UnpackedStructType>().membersOfType<FieldSymbol>()) {
            if (!isValidForNet(field.getType()))
                return false;
        }
        return true;
    }

    return false;
}

static bool isValidForUserDefinedNet(const Type& type) {
    auto& ct = type.getCanonicalType();
    if (ct.isIntegral() || ct.isFloating())
        return true;

    if (ct.kind == SymbolKind::FixedSizeUnpackedArrayType)
        return isValidForUserDefinedNet(ct.as<FixedSizeUnpackedArrayType>().elementType);

    if (ct.isUnpackedStruct()) {
        for (auto& field : ct.as<UnpackedStructType>().membersOfType<FieldSymbol>()) {
            if (!isValidForUserDefinedNet(field.getType()))
                return false;
        }
        return true;
    }

    if (ct.isUnpackedUnion()) {
        for (auto& field : ct.as<UnpackedUnionType>().membersOfType<FieldSymbol>()) {
            if (!isValidForUserDefinedNet(field.getType()))
                return false;
        }
        return true;
    }

    return false;
}

void DeclaredType::checkType(const BindContext& context) const {
    if (flags.has(DeclaredTypeFlags::Port)) {
        // Ports cannot be chandles.
        if (type->isCHandle())
            context.addDiag(diag::InvalidPortType, parent.location) << *type;
    }
    else if (flags.has(DeclaredTypeFlags::NetType)) {
        auto& net = parent.as<NetSymbol>();
        if (net.netType.netKind != NetType::UserDefined && !isValidForNet(*type))
            context.addDiag(diag::InvalidNetType, parent.location) << *type;
        else if (type->getBitWidth() == 1 && net.expansionHint != NetSymbol::None)
            context.addDiag(diag::SingleBitVectored, parent.location);
    }
    else if (flags.has(DeclaredTypeFlags::UserDefinedNetType)) {
        if (!isValidForUserDefinedNet(*type))
            context.addDiag(diag::InvalidUserDefinedNetType, parent.location) << *type;
    }
    else if (flags.has(DeclaredTypeFlags::FormalArgMergeVar)) {
        if (auto var = parent.as<FormalArgumentSymbol>().getMergedVariable()) {
            ASSERT(typeSyntax);
            mergePortTypes(context, *var, typeSyntax->as<ImplicitTypeSyntax>(), parent.location,
                           dimensions ? *dimensions : span<const VariableDimensionSyntax* const>{});
        }
    }
    else if (flags.has(DeclaredTypeFlags::Rand)) {
        RandMode mode = parent.getRandMode();
        if (!type->isValidForRand(mode)) {
            auto& diag = context.addDiag(diag::InvalidRandType, parent.location) << *type;
            if (mode == RandMode::Rand)
                diag << "rand"sv;
            else
                diag << "randc"sv;
        }
    }
}

static const Type* makeSigned(Compilation& compilation, const Type& type) {
    // This deliberately does not look at the canonical type; type aliases
    // are not convertible to a different signedness.
    SmallVectorSized<ConstantRange, 4> dims;
    const Type* curr = &type;
    while (curr->kind == SymbolKind::PackedArrayType) {
        dims.append(curr->getFixedRange());
        curr = curr->getArrayElementType();
    }

    if (curr->kind != SymbolKind::ScalarType)
        return &type;

    auto flags = curr->getIntegralFlags() | IntegralFlags::Signed;
    if (dims.size() == 1)
        return &compilation.getType(type.getBitWidth(), flags);

    curr = &compilation.getScalarType(flags);
    size_t count = dims.size();
    for (size_t i = 0; i < count; i++)
        curr = compilation.emplace<PackedArrayType>(*curr, dims[count - i - 1]);

    return curr;
}

void DeclaredType::mergePortTypes(
    const BindContext& context, const ValueSymbol& sourceSymbol, const ImplicitTypeSyntax& implicit,
    SourceLocation location, span<const VariableDimensionSyntax* const> unpackedDimensions) const {

    // There's this really terrible "feature" where the port declaration can influence the type
    // of the actual symbol somewhere else in the tree. This is ugly but should be safe since
    // nobody else can look at that symbol's type until we've gone through elaboration.
    //
    // In this context, the sourceSymbol is the actual variable declaration with, presumably,
    // a full type declared. The implicit syntax is from the port I/O declaration, which needs
    // to be merged. For example:
    //
    //   input signed [1:0] foo;    // implicit + unpackedDimensions + location
    //   logic foo;                 // sourceSymbol
    const Type* destType = &sourceSymbol.getType();

    if (implicit.signing) {
        // Drill past any unpacked arrays to figure out if this thing is even integral.
        SmallVectorSized<ConstantRange, 4> destDims;
        const Type* sourceType = destType;
        while (sourceType->getCanonicalType().kind == SymbolKind::FixedSizeUnpackedArrayType) {
            destDims.append(sourceType->getFixedRange());
            sourceType = sourceType->getArrayElementType();
        }

        if (sourceType->isError())
            return;

        if (!sourceType->isIntegral()) {
            auto& diag = context.addDiag(diag::CantDeclarePortSigned, location);
            diag << sourceSymbol.name << implicit.signing.valueText() << *destType;
            diag.addNote(diag::NoteDeclarationHere, sourceSymbol.location);
            return;
        }

        auto warnSignedness = [&] {
            auto& diag = context.addDiag(diag::SignednessNoEffect, implicit.signing.range());
            diag << implicit.signing.valueText() << *destType;
            diag.addNote(diag::NoteDeclarationHere, sourceSymbol.location);
        };

        bool shouldBeSigned = implicit.signing.kind == TokenKind::SignedKeyword;
        if (shouldBeSigned && !sourceType->isSigned()) {
            sourceType = makeSigned(context.getCompilation(), *sourceType);
            if (!sourceType->isSigned()) {
                warnSignedness();
            }
            else {
                // Put the unpacked dimensions back on the type now that it
                // has been made signed.
                destType = &FixedSizeUnpackedArrayType::fromDims(context.getCompilation(),
                                                                 *sourceType, destDims);
            }
        }
        else if (!shouldBeSigned && sourceType->isSigned()) {
            warnSignedness();
        }
    }

    // Our declared type takes on the merged type from the variable definition.
    this->type = destType;

    auto errorDims = [&](auto& dims) {
        auto& diag = context.addDiag(diag::PortDeclDimensionsMismatch, dims.sourceRange());
        diag << sourceSymbol.name;
        diag.addNote(diag::NoteDeclarationHere, sourceSymbol.location);
    };

    auto checkDims = [&](auto& dims, SymbolKind arrayKind, bool isPacked) {
        if (!dims.empty()) {
            auto it = dims.begin();
            while (destType->getCanonicalType().kind == arrayKind) {
                if (it == dims.end()) {
                    errorDims(*dims.back());
                    return;
                }

                auto dim = isPacked ? context.evalPackedDimension(**it)
                                    : context.evalUnpackedDimension(**it);
                if (!dim || destType->getFixedRange() != *dim) {
                    errorDims(**it);
                    return;
                }

                destType = destType->getArrayElementType();
                it++;
            }

            if (it != dims.end()) {
                errorDims(**it);
                return;
            }
        }
    };

    // Unpacked dim checks have to come first because it unwraps the destType
    // for the packed one to look at.
    checkDims(unpackedDimensions, SymbolKind::FixedSizeUnpackedArrayType, false);
    checkDims(implicit.dimensions, SymbolKind::PackedArrayType, true);
}

void DeclaredType::resolveAt(const BindContext& context) const {
    if (!initializerSyntax)
        return;

    if (!type) {
        resolveType(context);
        if (initializer)
            return;
    }

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
