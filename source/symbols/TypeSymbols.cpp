//------------------------------------------------------------------------------
// TypeSymbols.cpp
// Contains type-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "TypeSymbols.h"

#include "binding/ConstantValue.h"
#include "compilation/Compilation.h"

namespace {

using namespace slang;

bitwidth_t getWidth(PredefinedIntegerType::Kind kind) {
    switch (kind) {
        case PredefinedIntegerType::ShortInt: return 16;
        case PredefinedIntegerType::Int: return 32;
        case PredefinedIntegerType::LongInt: return 64;
        case PredefinedIntegerType::Byte: return 8;
        case PredefinedIntegerType::Integer: return 32;
        case PredefinedIntegerType::Time: return 64;
        default: THROW_UNREACHABLE;
    }
}

bool getSigned(PredefinedIntegerType::Kind kind) {
    switch (kind) {
        case PredefinedIntegerType::ShortInt: return true;
        case PredefinedIntegerType::Int: return true;
        case PredefinedIntegerType::LongInt: return true;
        case PredefinedIntegerType::Byte: return true;
        case PredefinedIntegerType::Integer: return true;
        case PredefinedIntegerType::Time: return false;
        default: THROW_UNREACHABLE;
    }
}

bool getFourState(PredefinedIntegerType::Kind kind) {
    switch (kind) {
        case PredefinedIntegerType::ShortInt: return false;
        case PredefinedIntegerType::Int: return false;
        case PredefinedIntegerType::LongInt: return false;
        case PredefinedIntegerType::Byte: return false;
        case PredefinedIntegerType::Integer: return true;
        case PredefinedIntegerType::Time: return true;
        default: THROW_UNREACHABLE;
    }
}

}

namespace slang {

const ErrorType ErrorType::Instance;

bitwidth_t Type::getBitWidth() const {
    if (isIntegral())
        return as<IntegralType>().bitWidth;
    if (isFloating()) {
        switch (as<FloatingType>().floatKind) {
            case FloatingType::Real: return 64;
            case FloatingType::RealTime: return 64;
            case FloatingType::ShortReal: return 32;
            default: THROW_UNREACHABLE;
        }
    }
    return 0;
}

bool Type::isSigned() const {
    return isIntegral() && as<IntegralType>().isSigned;
}

bool Type::isFourState() const {
    return isIntegral() && as<IntegralType>().isFourState;
}

bool Type::isIntegral() const {
    return IntegralType::isKind(kind);
}

bool Type::isAggregate() const {
    switch (kind) {
        case SymbolKind::UnpackedArrayType:
        case SymbolKind::UnpackedStructType:
        case SymbolKind::UnpackedUnionType:
            return true;
        default:
            return false;
    }
}

bool Type::isSimpleBitVector() const {
    if (isPredefinedInteger() || isScalar())
        return true;

    return kind == SymbolKind::PackedArrayType && as<PackedArrayType>().elementType.isScalar();
}

bool Type::isMatching(const Type& rhs) const {
    // See [6.22.1] for Matching Types.
    const Type* l = &getCanonicalType();
    const Type* r = &rhs.getCanonicalType();

    // If the two types have the same address, they are literally the same type.
    // This handles all built-in types, which are allocated once and then shared,
    // and also handles simple bit vector types that share the same range, signedness,
    // and four-stateness because we uniquify them in the compilation cache.
    // This handles checks [6.22.1] (a), (b), (c), (d), (g), and (h).
    if (l == r)
        return true;

    // Handle check (e) and (f): matching predefined integers and matching vector types
    if (l->isSimpleBitVector() && r->isSimpleBitVector()) {
        const auto& li = l->as<IntegralType>();
        const auto& ri = r->as<IntegralType>();
        return li.isSigned == ri.isSigned && li.isFourState && ri.isFourState &&
               li.getBitVectorRange() == ri.getBitVectorRange();
    }

    // Handle check (f): matching packed array types
    if (l->kind == SymbolKind::PackedArrayType && r->kind == SymbolKind::PackedArrayType)
        return l->as<PackedArrayType>().elementType.isMatching(r->as<PackedArrayType>().elementType);

    return false;
}

bool Type::isEquivalent(const Type& rhs) const {
    // See [6.22.2] for Equivalent Types
    const Type* l = &getCanonicalType();
    const Type* r = &rhs.getCanonicalType();
    if (l->isMatching(*r))
        return true;

    if (l->isIntegral() && r->isIntegral() && !l->isEnum() && !r->isEnum()) {
        const auto& li = l->as<IntegralType>();
        const auto& ri = r->as<IntegralType>();
        return li.isSigned == ri.isSigned && li.isFourState && ri.isFourState && li.bitWidth == ri.bitWidth;
    }

    return false;
}

bool Type::isAssignmentCompatible(const Type& rhs) const {
    // See [6.22.3] for Assignment Compatible
    const Type* l = &getCanonicalType();
    const Type* r = &rhs.getCanonicalType();
    if (l->isEquivalent(*r))
        return true;

    // Any integral or floating value can be implicitly converted to a packed integer
    // value or to a floating value.
    if ((l->isIntegral() && !l->isEnum()) || l->isFloating())
        return r->isIntegral() || r->isFloating();

    return false;
}

bool Type::isCastCompatible(const Type& rhs) const {
    // See [6.22.4] for Cast Compatible
    const Type* l = &getCanonicalType();
    const Type* r = &rhs.getCanonicalType();
    if (l->isAssignmentCompatible(*r))
        return true;

    if (l->isEnum())
        return r->isIntegral() || r->isFloating();

    return false;
}

std::string Type::toString() const {
    return "";
}

const Type& Type::fromSyntax(Compilation& compilation, const DataTypeSyntax& node, LookupLocation location,
                             const Scope& parent) {
    switch (node.kind) {
        case SyntaxKind::BitType:
        case SyntaxKind::LogicType:
        case SyntaxKind::RegType:
            return IntegralType::fromSyntax(compilation, node.as<IntegerTypeSyntax>(), location, parent);
        case SyntaxKind::ByteType:
        case SyntaxKind::ShortIntType:
        case SyntaxKind::IntType:
        case SyntaxKind::LongIntType:
        case SyntaxKind::IntegerType:
        case SyntaxKind::TimeType: {
            // TODO: signing
            // TODO: report this error in the parser?
            //auto& its = syntax.as<IntegerTypeSyntax>();
            //if (its.dimensions.count() > 0) {
            //    // Error but don't fail out; just remove the dims and keep trucking
            //    auto& diag = addError(DiagCode::PackedDimsOnPredefinedType, its.dimensions[0]->openBracket.location());
            //    diag << getTokenKindText(its.keyword.kind);
            //}
            return compilation.getType(node.kind);
        }
        case SyntaxKind::RealType:
        case SyntaxKind::RealTimeType:
        case SyntaxKind::ShortRealType:
        case SyntaxKind::StringType:
        case SyntaxKind::CHandleType:
        case SyntaxKind::EventType:
            return compilation.getType(node.kind);
        case SyntaxKind::EnumType:
            return EnumType::fromSyntax(compilation, node.as<EnumTypeSyntax>(), location, parent);
        case SyntaxKind::StructType: {
            const auto& structUnion = node.as<StructUnionTypeSyntax>();
            return structUnion.packed ?
                PackedStructType::fromSyntax(compilation, structUnion, location, parent) :
                UnpackedStructType::fromSyntax(compilation, structUnion, location, parent);
        }
        case SyntaxKind::NamedType:
            return lookupNamedType(compilation, node.as<NamedTypeSyntax>().name, location, parent);
        default:
            THROW_UNREACHABLE;
    }
}

bool Type::isKind(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::PredefinedIntegerType:
        case SymbolKind::ScalarType:
        case SymbolKind::FloatingType:
        case SymbolKind::EnumType:
        case SymbolKind::PackedArrayType:
        case SymbolKind::UnpackedArrayType:
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
        case SymbolKind::PackedUnionType:
        case SymbolKind::UnpackedUnionType:
        case SymbolKind::ClassType:
        case SymbolKind::VoidType:
        case SymbolKind::NullType:
        case SymbolKind::CHandleType:
        case SymbolKind::StringType:
        case SymbolKind::EventType:
        case SymbolKind::TypeAlias:
        case SymbolKind::ErrorType:
            return true;
        default:
            return false;
    }
}

void Type::resolveCanonical() const {
    ASSERT(kind == SymbolKind::TypeAlias);
    canonical = as<TypeAliasType>().targetType.get();
}

const Type& Type::lookupNamedType(Compilation& compilation, const NameSyntax& syntax, LookupLocation location,
                                  const Scope& parent) {
    LookupResult result;
    parent.lookupName(syntax, location, LookupNameKind::Type, result);

    if (result.hasError())
        compilation.addDiagnostics(result.diagnostics);

    const Symbol* symbol = result.found;
    if (!symbol)
        return compilation.getErrorType();

    if (!symbol->isType()) {
        compilation.addError(DiagCode::NotAType, syntax.sourceRange()) << symbol->name;
        return compilation.getErrorType();
    }

    return symbol->as<Type>();
}

IntegralType::IntegralType(SymbolKind kind, string_view name, SourceLocation loc, bitwidth_t bitWidth_,
                           bool isSigned_, bool isFourState_) :
    Type(kind, name, loc),
    bitWidth(bitWidth_), isSigned(isSigned_), isFourState(isFourState_)
{
}

bool IntegralType::isKind(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::PredefinedIntegerType:
        case SymbolKind::ScalarType:
        case SymbolKind::EnumType:
        case SymbolKind::PackedArrayType:
        case SymbolKind::PackedStructType:
        case SymbolKind::PackedUnionType:
            return true;
        default:
            return false;
    }
}

ConstantRange IntegralType::getBitVectorRange() const {
    if (isPredefinedInteger() || isScalar())
        return { int32_t(bitWidth - 1), 0 };

    return as<PackedArrayType>().range;
}

const Type& IntegralType::fromSyntax(Compilation& compilation, const IntegerTypeSyntax& syntax,
                                     LookupLocation location, const Scope& scope) {
    // This is a simple integral vector (possibly of just one element).
    bool isReg = syntax.keyword.kind == TokenKind::RegKeyword;
    bool isSigned = syntax.signing.kind == TokenKind::SignedKeyword;
    bool isFourState = syntax.kind != SyntaxKind::BitType;

    SmallVectorSized<ConstantRange, 4> dims;
    if (!evaluateConstantDims(compilation, syntax.dimensions, dims, location, scope))
        return compilation.getErrorType();

    // TODO: review this whole mess

    if (dims.empty()) {
        // TODO: signing
        return compilation.getType(syntax.kind);
    }
    else if (dims.size() == 1 && dims[0].right == 0) {
        // if we have the common case of only one dimension and lsb == 0
        // then we can use the shared representation
        int width = dims[0].left + 1;
        return compilation.getType(width, isSigned, isFourState, isReg);
    }

    const IntegralType* result = &compilation.getScalarType(isFourState, isReg);
    for (uint32_t i = 0; i < dims.size(); i++)
        result = compilation.emplace<PackedArrayType>(*result, dims[i]);

    return *result;
}

bool IntegralType::evaluateConstantDims(Compilation& compilation,
                                        const SyntaxList<VariableDimensionSyntax>& dimensions,
                                        SmallVector<ConstantRange>& results,
                                        LookupLocation location, const Scope& scope) {
    for (const VariableDimensionSyntax* dim : dimensions) {
        const SelectorSyntax* selector;
        if (!dim->specifier || dim->specifier->kind != SyntaxKind::RangeDimensionSpecifier ||
            (selector = &dim->specifier->as<RangeDimensionSpecifierSyntax>().selector)->kind != SyntaxKind::SimpleRangeSelect) {

            // TODO: errors
            //auto& diag = addError(DiagCode::PackedDimRequiresConstantRange, dim->specifier->getFirstToken().location());
            //diag << dim->specifier->sourceRange();
            return false;
        }

        const RangeSelectSyntax& range = selector->as<RangeSelectSyntax>();

        // §6.9.1 - Implementations may set a limit on the maximum length of a vector,
        // but the limit shall be at least 65536 (2^16) bits.
        const int MaxRangeBits = 16;

        // TODO: errors
        BindContext context(scope, location, BindFlags::RequireConstant);
        const auto& left = compilation.bindExpression(range.left, context);
        const auto& right = compilation.bindExpression(range.right, context);
        if (!left.constant || !right.constant)
            return false;

        auto cl = left.constant->coerceInteger(MaxRangeBits);
        auto cr = right.constant->coerceInteger(MaxRangeBits);
        if (!cl || !cr)
            return false;

        results.emplace(ConstantRange { *cl, *cr });
    }
    return true;
}

PredefinedIntegerType::PredefinedIntegerType(Kind integerKind) :
    PredefinedIntegerType(integerKind, getSigned(integerKind))
{
}

PredefinedIntegerType::PredefinedIntegerType(Kind integerKind, bool isSigned) :
    IntegralType(SymbolKind::PredefinedIntegerType, "", SourceLocation(),
                 getWidth(integerKind), isSigned, getFourState(integerKind)),
    integerKind(integerKind)
{
}

ScalarType::ScalarType(Kind scalarKind) :
    ScalarType(scalarKind, false)
{
}

ScalarType::ScalarType(Kind scalarKind, bool isSigned) :
    IntegralType(SymbolKind::ScalarType, "", SourceLocation(), 1, isSigned, scalarKind != Kind::Bit),
    scalarKind(scalarKind)
{
}

FloatingType::FloatingType(Kind floatKind_) :
    Type(SymbolKind::FloatingType, "", SourceLocation()),
    floatKind(floatKind_)
{
}

EnumType::EnumType(Compilation& compilation, SourceLocation loc, const IntegralType& baseType_,
                   const Scope& scope) :
    IntegralType(SymbolKind::EnumType, "", loc, baseType_.getBitWidth(),
                 baseType_.isSigned, baseType_.isFourState),
    Scope(compilation, this),
    baseType(baseType_)
{
    // Enum types don't live as members of the parent scope (they're "owned" by the declaration containing
    // them) but we hook up the parent pointer so that it can participate in name lookups.
    setParent(scope);
}

const Type& EnumType::fromSyntax(Compilation& compilation, const EnumTypeSyntax& syntax,
                                 LookupLocation location, const Scope& scope) {
    const Type* base;
    if (!syntax.baseType)
        base = &compilation.getIntType();
    else {
        base = &compilation.getType(*syntax.baseType, location, scope);

        const Type& canonicalBase = base->getCanonicalType();
        if (canonicalBase.isError())
            return canonicalBase;

        if (!canonicalBase.isSimpleBitVector()) {
            compilation.addError(DiagCode::InvalidEnumBase,
                                 syntax.baseType->getFirstToken().location()) << *base;
            return compilation.getErrorType();
        }
    }

    const IntegralType& integralBase = base->as<IntegralType>();
    auto resultType = compilation.emplace<EnumType>(compilation, syntax.keyword.location(),
                                                    integralBase, scope);

    SVInt one(integralBase.bitWidth, 1, integralBase.isSigned);
    SVInt current(integralBase.bitWidth, 0, integralBase.isSigned);
    const Symbol* previousMember = nullptr;

    for (auto member : syntax.members) {
        ConstantValue value;
        if (!member->initializer)
            value = current;
        else {
            // TODO: conversion? range / overflow checking? non-constant?
            BindContext context(*resultType,
                                previousMember ? LookupLocation::after(*previousMember) : LookupLocation::min,
                                BindFlags::RequireConstant);

            const auto& init = compilation.bindExpression(member->initializer->expr, context);
            if (!init.constant)
                value = current;
            else
                value = *init.constant;
        }

        auto ev = compilation.emplace<EnumValueSymbol>(compilation, member->name.valueText(),
                                                       member->name.location(), *resultType,
                                                       std::move(value));
        resultType->addMember(*ev);
        current = value.integer() + one;
        previousMember = ev;
    }

    return *resultType;
}

EnumValueSymbol::EnumValueSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                                 const Type& type, ConstantValue value) :
    ValueSymbol(SymbolKind::EnumValue, name, loc),
    type(type), value(*compilation.createConstant(std::move(value)))
{
}

PackedArrayType::PackedArrayType(const Type& elementType, ConstantRange range) :
    IntegralType(SymbolKind::PackedArrayType, "", SourceLocation(), elementType.getBitWidth() * range.width(),
                 elementType.isSigned(), elementType.isFourState()),
    elementType(elementType), range(range)
{
}

PackedStructType::PackedStructType(Compilation& compilation, bitwidth_t bitWidth,
                                   bool isSigned, bool isFourState) :
    IntegralType(SymbolKind::PackedStructType, "", SourceLocation(), bitWidth, isSigned, isFourState),
    Scope(compilation, this)
{
}

const Type& PackedStructType::fromSyntax(Compilation& compilation, const StructUnionTypeSyntax& syntax,
                                         LookupLocation location, const Scope& scope) {
    ASSERT(syntax.packed);
    bool isSigned = syntax.signing.kind == TokenKind::SignedKeyword;
    bool isFourState = false;
    bitwidth_t bitWidth = 0;

    // We have to look at all the members up front to know our width and four-statedness.
    SmallVectorSized<const Symbol*, 8> members;
    for (auto member : syntax.members) {
        const Type& type = compilation.getType(member->type, location, scope);
        if (type.isIntegral()) {
            isFourState |= type.as<IntegralType>().isFourState;
        }
        else if (!type.isError()) {
            auto& diag = compilation.addError(DiagCode::PackedMemberNotIntegral,
                                              member->type.getFirstToken().location());
            diag << type;
            diag << member->type.sourceRange();
        }

        for (auto decl : member->declarators) {
            bitWidth += type.getBitWidth();

            auto variable = compilation.emplace<VariableSymbol>(decl->name.valueText(), decl->name.location());
            members.append(variable);
            variable->type = type;

            if (decl->initializer) {
                auto& diag = compilation.addError(DiagCode::PackedMemberHasInitializer,
                                                  decl->initializer->equals.location());
                diag << decl->initializer->expr.sourceRange();
            }
        }
    }

    auto result = compilation.emplace<PackedStructType>(compilation, bitWidth, isSigned, isFourState);
    for (auto member : members)
        result->addMember(*member);

    return *result;
}

UnpackedStructType::UnpackedStructType(Compilation& compilation) :
    Type(SymbolKind::UnpackedStructType, "", SourceLocation()),
    Scope(compilation, this)
{
}

const Type& UnpackedStructType::fromSyntax(Compilation& compilation, const StructUnionTypeSyntax& syntax,
                                           LookupLocation location, const Scope& scope) {
    ASSERT(!syntax.packed);

    auto result = compilation.emplace<UnpackedStructType>(compilation);
    for (auto member : syntax.members) {
        const Type& type = compilation.getType(member->type, location, scope);
        for (auto decl : member->declarators) {
            auto variable = compilation.emplace<VariableSymbol>(decl->name.valueText(), decl->name.location());
            result->addMember(*variable);

            variable->type = type;
            if (decl->initializer)
                variable->initializer = decl->initializer->expr;
        }
    }

    return *result;
}

const ForwardingTypedefSymbol&
ForwardingTypedefSymbol::fromSyntax(Compilation& compilation, const ForwardTypedefDeclarationSyntax& syntax) {
    Category category;
    switch (syntax.keyword.kind) {
        case TokenKind::EnumKeyword: category = Category::Enum; break;
        case TokenKind::StructKeyword: category = Category::Struct; break;
        case TokenKind::UnionKeyword: category = Category::Union; break;
        case TokenKind::ClassKeyword: category = Category::Class; break;
        default: category = Category::None; break;
    }
    return *compilation.emplace<ForwardingTypedefSymbol>(syntax.name.valueText(),
                                                         syntax.name.location(),
                                                         category);
}

const ForwardingTypedefSymbol&
ForwardingTypedefSymbol::fromSyntax(Compilation& compilation,
                                    const ForwardInterfaceClassTypedefDeclarationSyntax& syntax) {
    return *compilation.emplace<ForwardingTypedefSymbol>(syntax.name.valueText(),
                                                         syntax.name.location(),
                                                         Category::InterfaceClass);
}

void ForwardingTypedefSymbol::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!next)
        next = &decl;
    else
        next->addForwardDecl(decl);
}

const TypeAliasType& TypeAliasType::fromSyntax(Compilation& compilation,
                                               const TypedefDeclarationSyntax& syntax) {
    // TODO: unpacked dimensions
    auto result = compilation.emplace<TypeAliasType>(syntax.name.valueText(), syntax.name.location());
    result->targetType = syntax.type;
    return *result;
}

void TypeAliasType::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!firstForward)
        firstForward = &decl;
    else
        firstForward->addForwardDecl(decl);
}

void TypeAliasType::checkForwardDecls() const {
    ForwardingTypedefSymbol::Category category;
    switch (targetType->kind) {
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
            category = ForwardingTypedefSymbol::Struct;
            break;
        case SymbolKind::EnumType:
            category = ForwardingTypedefSymbol::Enum;
            break;
        default:
            return;
    }

    const ForwardingTypedefSymbol* forward = firstForward;
    while (forward) {
        if (forward->category != ForwardingTypedefSymbol::None && forward->category != category) {
            auto& diag = getScope()->getCompilation().addError(DiagCode::ForwardTypedefDoesNotMatch,
                                                               forward->location);
            switch (forward->category) {
                case ForwardingTypedefSymbol::Enum: diag << "enum"; break;
                case ForwardingTypedefSymbol::Struct: diag << "struct"; break;
                case ForwardingTypedefSymbol::Union: diag << "union"; break;
                case ForwardingTypedefSymbol::Class: diag << "class"; break;
                case ForwardingTypedefSymbol::InterfaceClass: diag << "interface class"; break;
                default: THROW_UNREACHABLE;
            }
            diag.addNote(DiagCode::NoteDeclarationHere, location);
            return;
        }
        forward = forward->getNextForwardDecl();
    }
}

}
