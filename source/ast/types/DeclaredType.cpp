//------------------------------------------------------------------------------
// DeclaredType.cpp
// Glue logic between symbols and their declared types
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/types/DeclaredType.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/Expression.h"
#include "slang/ast/Scope.h"
#include "slang/ast/Symbol.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/NetType.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/ScopeGuard.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

static const Expression* NoInitializer = reinterpret_cast<const Expression*>(UINTPTR_MAX);

DeclaredType::DeclaredType(const Symbol& parent, bitmask<DeclaredTypeFlags> flags) :
    parent(parent), flags(flags), overrideIndex(0), evaluating(false), hasLink(false) {
    // If this assert fires you need to update Symbol::getDeclaredType
    SLANG_ASSERT(parent.getDeclaredType() == this);
}

const Type& DeclaredType::getType() const {
    if (!type)
        resolveType(getASTContext<false>(), getASTContext<true>());
    return *type;
}

void DeclaredType::setLink(const DeclaredType& target) {
    SLANG_ASSERT(hasLink || !typeOrLink.typeSyntax);
    SLANG_ASSERT(!type && !dimensions && !initializer);

    hasLink = true;
    typeOrLink.link = &target;
}

void DeclaredType::setDimensionSyntax(const SyntaxList<VariableDimensionSyntax>& newDimensions) {
    SLANG_ASSERT(!type);
    dimensions = &newDimensions;
}

void DeclaredType::mergeImplicitPort(
    const ImplicitTypeSyntax& implicit, SourceLocation location,
    std::span<const VariableDimensionSyntax* const> unpackedDimensions) {
    mergePortTypes(getASTContext<false>(), parent.as<ValueSymbol>(), implicit, location,
                   unpackedDimensions);
}

void DeclaredType::resolveType(const ASTContext& typeContext,
                               const ASTContext& initializerContext) const {
    auto& comp = typeContext.getCompilation();
    if (hasLink) {
        SLANG_ASSERT(typeOrLink.link);
        type = &typeOrLink.link->getType();
        if (dimensions)
            type = &comp.getType(*type, *dimensions, typeContext);
        return;
    }

    auto syntax = typeOrLink.typeSyntax;
    SLANG_ASSERT(syntax);
    if (!syntax) {
        type = &comp.getErrorType();
        return;
    }

    SLANG_ASSERT(!evaluating);
    evaluating = true;
    auto guard = ScopeGuard([this] { evaluating = false; });

    // If we are configured to infer implicit types, bind the initializer expression
    // first so that we can derive our type from whatever that happens to be.
    if (syntax->kind == SyntaxKind::ImplicitType && flags.has(DeclaredTypeFlags::InferImplicit)) {
        if (dimensions) {
            auto& its = syntax->as<ImplicitTypeSyntax>();
            if (its.signing || !its.dimensions.empty()) {
                type = &comp.getType(*syntax, typeContext, nullptr);
                type = &comp.getType(*type, *dimensions, typeContext);
            }
            else {
                typeContext.addDiag(diag::UnpackedArrayParamType, dimensions->sourceRange());
                type = &comp.getErrorType();
            }
        }
        else if (!initializerSyntax) {
            type = &comp.getErrorType();
        }
        else {
            bitmask<ASTFlags> extraFlags;
            if (flags.has(DeclaredTypeFlags::AllowUnboundedLiteral))
                extraFlags = ASTFlags::AllowUnboundedLiteral;

            std::tie(initializer, type) = Expression::bindImplicitParam(
                *syntax, *initializerSyntax, {initializerLocation, initializerLocation + 1},
                initializerContext, typeContext, extraFlags);
            SLANG_ASSERT(initializer);
        }
    }
    else if (flags.has(DeclaredTypeFlags::InterconnectNet)) {
        // An interconnect net is always untyped (or some array of untyped elements).
        type = &comp.getType(SyntaxKind::Untyped);
        if (syntax->kind == SyntaxKind::ImplicitType) {
            // This should always be an implicit type unless there's an
            // error (diagnosed by the parser).
            auto& its = syntax->as<ImplicitTypeSyntax>();
            if (!its.dimensions.empty())
                type = &comp.getType(*type, its.dimensions,
                                     typeContext.resetFlags(ASTFlags::AllowInterconnect));
        }

        if (dimensions) {
            type = &comp.getType(*type, *dimensions,
                                 typeContext.resetFlags(ASTFlags::AllowInterconnect));
        }

        // Return early to skip additional checks for net types.
        return;
    }
    else {
        const Type* typedefTarget = nullptr;
        if (flags.has(DeclaredTypeFlags::TypedefTarget)) {
            if (parent.kind == SymbolKind::TypeParameter)
                typedefTarget = &parent.as<TypeParameterSymbol>().getTypeAlias();
            else
                typedefTarget = &parent.as<Type>();
        }

        type = &comp.getType(*syntax, typeContext, typedefTarget);
        if (dimensions)
            type = &comp.getType(*type, *dimensions, typeContext);

        if (typedefTarget) {
            // When resolving a typedef target we need to force resolution
            // of the canonical type to make sure there are no cycles.
            type->getCanonicalType();
        }
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
        for (auto field : ct.as<UnpackedStructType>().fields) {
            if (!isValidForNet(field->getType()))
                return false;
        }
        return true;
    }

    if (ct.isUnpackedUnion()) {
        for (auto field : ct.as<UnpackedUnionType>().fields) {
            if (!isValidForNet(field->getType()))
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
        for (auto field : ct.as<UnpackedStructType>().fields) {
            if (!isValidForUserDefinedNet(field->getType()))
                return false;
        }
        return true;
    }

    if (ct.isUnpackedUnion()) {
        for (auto field : ct.as<UnpackedUnionType>().fields) {
            if (!isValidForUserDefinedNet(field->getType()))
                return false;
        }
        return true;
    }

    return false;
}

static bool isValidForIfaceVar(const Type& type) {
    auto& ct = type.getCanonicalType();
    if (ct.isVirtualInterface())
        return false;

    if (ct.isUnpackedArray())
        return isValidForIfaceVar(*ct.getArrayElementType());

    if (ct.isUnpackedStruct()) {
        for (auto field : ct.as<UnpackedStructType>().fields) {
            if (!isValidForIfaceVar(field->getType()))
                return false;
        }
    }

    return true;
}

void DeclaredType::checkType(const ASTContext& context) const {
    auto lv = context.getCompilation().languageVersion();
    uint32_t masked = (flags & DeclaredTypeFlags::NeedsTypeCheck).bits();
    SLANG_ASSERT(std::popcount(masked) == 1);

    switch (masked) {
        case uint32_t(DeclaredTypeFlags::NetType): {
            auto& net = parent.as<NetSymbol>();
            if (net.netType.netKind != NetType::UserDefined && !isValidForNet(*type))
                context.addDiag(diag::InvalidNetType, parent.location) << *type;
            else if (type->getBitWidth() == 1 && net.expansionHint != NetSymbol::None)
                context.addDiag(diag::SingleBitVectored, parent.location);
            break;
        }
        case uint32_t(DeclaredTypeFlags::UserDefinedNetType):
            if (!isValidForUserDefinedNet(*type))
                context.addDiag(diag::InvalidUserDefinedNetType, parent.location) << *type;
            break;
        case uint32_t(DeclaredTypeFlags::FormalArgMergeVar):
            if (auto var = parent.as<FormalArgumentSymbol>().getMergedVariable()) {
                SLANG_ASSERT(!hasLink);
                SLANG_ASSERT(typeOrLink.typeSyntax);
                mergePortTypes(context, *var, typeOrLink.typeSyntax->as<ImplicitTypeSyntax>(),
                               parent.location,
                               dimensions ? *dimensions
                                          : std::span<const VariableDimensionSyntax* const>{});
            }
            break;
        case uint32_t(DeclaredTypeFlags::Rand): {
            RandMode mode = parent.getRandMode();
            if (!type->isValidForRand(mode, lv)) {
                auto& diag = context.addDiag(diag::InvalidRandType, parent.location) << *type;
                if (mode == RandMode::Rand)
                    diag << "rand"sv;
                else
                    diag << "randc"sv;
            }
            break;
        }
        case uint32_t(DeclaredTypeFlags::DPIReturnType): {
            if (!type->isValidForDPIReturn())
                context.addDiag(diag::InvalidDPIReturnType, parent.location) << *type;
            else if (parent.as<SubroutineSymbol>().flags.has(MethodFlags::Pure) && type->isVoid())
                context.addDiag(diag::DPIPureReturn, parent.location);
            break;
        }
        case uint32_t(DeclaredTypeFlags::DPIArg):
            if (!type->isValidForDPIArg())
                context.addDiag(diag::InvalidDPIArgType, parent.location) << *type;
            break;
        case uint32_t(DeclaredTypeFlags::RequireSequenceType):
            if (!type->isValidForSequence())
                context.addDiag(diag::AssertionExprType, parent.location) << *type;
            break;
        case uint32_t(DeclaredTypeFlags::CoverageType):
            if (!type->isIntegral() && (lv < LanguageVersion::v1800_2023 || !type->isFloating()))
                context.addDiag(diag::InvalidCoverageExpr, parent.location) << *type;
            break;
        case uint32_t(DeclaredTypeFlags::InterfaceVariable):
            if (!isValidForIfaceVar(*type))
                context.addDiag(diag::VirtualInterfaceIfaceMember, parent.location);
            break;
        default:
            SLANG_UNREACHABLE;
    }
}

void DeclaredType::mergePortTypes(
    const ASTContext& context, const ValueSymbol& sourceSymbol, const ImplicitTypeSyntax& implicit,
    SourceLocation location,
    std::span<const VariableDimensionSyntax* const> unpackedDimensions) const {

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
        SmallVector<ConstantRange, 4> destDims;
        const Type* sourceType = destType;
        while (sourceType->getCanonicalType().kind == SymbolKind::FixedSizeUnpackedArrayType) {
            destDims.push_back(sourceType->getFixedRange());
            sourceType = sourceType->getArrayElementType();
        }

        if (sourceType->isError())
            return;

        if (!sourceType->isIntegral()) {
            if (sourceSymbol.kind == SymbolKind::Net &&
                sourceSymbol.as<NetSymbol>().netType.netKind == NetType::Interconnect) {
                auto& diag = context.addDiag(diag::InterconnectTypeSyntax,
                                             implicit.signing.range());
                diag.addNote(diag::NoteDeclarationHere, sourceSymbol.location);
            }
            else {
                auto& diag = context.addDiag(diag::CantDeclarePortSigned, location);
                diag << sourceSymbol.name << implicit.signing.valueText() << *destType;
                diag.addNote(diag::NoteDeclarationHere, sourceSymbol.location);
            }
            return;
        }

        auto warnSignedness = [&] {
            auto& diag = context.addDiag(diag::SignednessNoEffect, implicit.signing.range());
            diag << implicit.signing.valueText() << *destType;
            diag.addNote(diag::NoteDeclarationHere, sourceSymbol.location);
        };

        bool shouldBeSigned = implicit.signing.kind == TokenKind::SignedKeyword;
        if (shouldBeSigned && !sourceType->isSigned()) {
            sourceType = &sourceType->makeSigned(context.getCompilation());
            if (!sourceType->isSigned()) {
                warnSignedness();
            }
            else {
                // Put the unpacked dimensions back on the type now that it
                // has been made signed.
                destType = &FixedSizeUnpackedArrayType::fromDims(*context.scope, *sourceType,
                                                                 destDims, SourceRange::NoLocation);
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
                if (!dim.isRange() || destType->getFixedRange() != dim.range) {
                    errorDims(**it);
                    return;
                }

                destType = destType->getArrayElementType();
                it++;
            }

            if (it != dims.end() && !destType->isError()) {
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

void DeclaredType::resolveAt(const ASTContext& context) const {
    if (!type) {
        resolveType(getASTContext<false>(), context);
        if (initializer)
            return;
    }

    if (!initializerSyntax) {
        initializer = NoInitializer;
        return;
    }

    // Enums are special in that their initializers target the base type of the enum
    // instead of the actual enum type (which doesn't allow implicit conversions from
    // normal integral values).
    auto& scope = *context.scope;
    bitmask<ASTFlags> extraFlags;
    const Type* targetType = type;
    if (targetType->isEnum() && scope.asSymbol().kind == SymbolKind::EnumType) {
        targetType = &targetType->as<EnumType>().baseType;
        extraFlags = ASTFlags::UnevaluatedBranch;
    }
    else if (flags.has(DeclaredTypeFlags::AllowUnboundedLiteral)) {
        extraFlags = ASTFlags::AllowUnboundedLiteral;
    }

    initializer = &Expression::bindRValue(*targetType, *initializerSyntax,
                                          {initializerLocation, initializerLocation + 1}, context,
                                          extraFlags);
}

void DeclaredType::forceResolveAt(const ASTContext& context) const {
    if (!type)
        resolveType(context, context);

    if (!initializer)
        resolveAt(context);
}

const Expression* DeclaredType::getInitializer() const {
    if (!initializer)
        resolveAt(getASTContext<true>());

    return initializer == NoInitializer ? nullptr : initializer;
}

void DeclaredType::setFromDeclarator(const DeclaratorSyntax& decl) {
    if (!decl.dimensions.empty())
        setDimensionSyntax(decl.dimensions);
    if (decl.initializer)
        setInitializerSyntax(*decl.initializer->expr, decl.initializer->equals.location());
}

template<bool IsInitializer, typename T>
T DeclaredType::getASTContext() const {
    bitmask<ASTFlags> astFlags;
    if (flags.has(DeclaredTypeFlags::NetType))
        astFlags |= ASTFlags::NonProcedural;
    if (!flags.has(DeclaredTypeFlags::AutomaticInitializer))
        astFlags |= ASTFlags::StaticInitializer;
    if (flags.has(DeclaredTypeFlags::CoverageType))
        astFlags |= ASTFlags::AllowCoverageSampleFormal;
    if (flags.has(DeclaredTypeFlags::UserDefinedNetType))
        astFlags |= ASTFlags::AllowNetType;
    if (flags.has(DeclaredTypeFlags::DPIArg))
        astFlags |= ASTFlags::DPIArg;

    const Scope* scope = parent.getParentScope();
    SLANG_ASSERT(scope);

    // Specparams inside of specify blocks have additional constraints so we
    // need to set the AST flag for them.
    if (parent.kind == SymbolKind::Specparam) {
        astFlags |= ASTFlags::SpecparamInitializer;
        if (scope->asSymbol().kind == SymbolKind::SpecifyBlock)
            astFlags |= ASTFlags::SpecifyBlock;
    }

    // If this type/initializer has been overridden by a parameter override,
    // we should use the instantiation scope and not the parameter's scope
    // when resolving.
    if ((IsInitializer && flags.has(DeclaredTypeFlags::InitializerOverridden)) ||
        (!IsInitializer && flags.has(DeclaredTypeFlags::TypeOverridden))) {
        auto& instBody = scope->asSymbol().as<InstanceBodySymbol>();
        auto inst = instBody.parentInstance;
        SLANG_ASSERT(inst);

        scope = inst->getParentScope();
        SLANG_ASSERT(scope);

        if (instBody.flags.has(InstanceFlags::FromBind))
            astFlags |= ASTFlags::BindInstantiation;

        return ASTContext(*scope, LookupLocation::before(*inst), astFlags);
    }

    // The location depends on whether we are creating the initializer or the type.
    // Initializer lookup happens *after* the parent symbol, so that it can reference
    // the symbol itself. Type lookup happens *before*, since it can't yet see the
    // symbol declaration. There is an exception for parameters, which also can't
    // see its own declaration (which would result in infinite recursion).
    LookupLocation location;
    if (overrideIndex) {
        location = LookupLocation(parent.getParentScope(), overrideIndex);
    }
    else if (IsInitializer) {
        if (flags.has(DeclaredTypeFlags::InitializerCantSeeParent))
            location = LookupLocation::before(parent);
        else
            location = LookupLocation::after(parent);
    }
    else {
        location = LookupLocation::before(parent);
    }

    return ASTContext(*scope, location, astFlags);
}

} // namespace slang::ast
