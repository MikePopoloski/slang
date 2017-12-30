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

uint32_t getWidth(BuiltInIntegerType::Kind kind) {
    switch (kind) {
        case BuiltInIntegerType::Bit: return 1;
        case BuiltInIntegerType::Logic: return 1;
        case BuiltInIntegerType::Reg: return 1;
        case BuiltInIntegerType::ShortInt: return 16;
        case BuiltInIntegerType::Int: return 32;
        case BuiltInIntegerType::LongInt: return 64;
        case BuiltInIntegerType::Byte: return 8;
        case BuiltInIntegerType::Integer: return 32;
        case BuiltInIntegerType::Time: return 64;
        default: THROW_UNREACHABLE;
    }
}

bool getSigned(BuiltInIntegerType::Kind kind) {
    switch (kind) {
        case BuiltInIntegerType::Bit: return false;
        case BuiltInIntegerType::Logic: return false;
        case BuiltInIntegerType::Reg: return false;
        case BuiltInIntegerType::ShortInt: return true;
        case BuiltInIntegerType::Int: return true;
        case BuiltInIntegerType::LongInt: return true;
        case BuiltInIntegerType::Byte: return true;
        case BuiltInIntegerType::Integer: return true;
        case BuiltInIntegerType::Time: return false;
        default: THROW_UNREACHABLE;
    }
}

bool getFourState(BuiltInIntegerType::Kind kind) {
    switch (kind) {
        case BuiltInIntegerType::Bit: return false;
        case BuiltInIntegerType::Logic: return true;
        case BuiltInIntegerType::Reg: return true;
        case BuiltInIntegerType::ShortInt: return false;
        case BuiltInIntegerType::Int: return false;
        case BuiltInIntegerType::LongInt: return false;
        case BuiltInIntegerType::Byte: return false;
        case BuiltInIntegerType::Integer: return true;
        case BuiltInIntegerType::Time: return true;
        default: THROW_UNREACHABLE;
    }
}

bool getSigned(const Type& type) {
    return type.isIntegral() && type.as<IntegralType>().isSigned;
}

bool getFourState(const Type& type) {
    return type.isIntegral() && type.as<IntegralType>().isFourState;
}

}

namespace slang {

const ErrorType ErrorType::Instance;

const Type& Type::getCanonicalType() const {
    return *this;
}

uint32_t Type::getBitWidth() const {
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

bool Type::isIntegral() const {
    switch (kind) {
        case SymbolKind::BuiltInIntegerType:
        case SymbolKind::VectorType:
        case SymbolKind::EnumType:
        case SymbolKind::PackedArrayType:
        case SymbolKind::PackedStructType:
        case SymbolKind::PackedUnionType:
            return true;
        default:
            return false;
    }
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
    return kind == SymbolKind::BuiltInIntegerType || kind == SymbolKind::VectorType;
}

bool Type::isMatching(const Type& rhs) const {
    const Type* l = &getCanonicalType();
    const Type* r = &rhs.getCanonicalType();

    // If the two types have the same address, they are literally the same type.
    // This handles all built-in types, which are allocated once and then shared,
    // and also handles simple bit vector types that share the same range, signedness,
    // and four-stateness because we uniquify them in the compilation cache.
    if (l == r)
        return true;

    // TODO: check array types here

    return false;
}

bool Type::isEquivalent(const Type& rhs) const {
    if (isMatching(rhs))
        return true;

    return true;
}

bool Type::isAssignmentCompatible(const Type& rhs) const {
    if (isEquivalent(rhs))
        return true;

    return true;
}

bool Type::isCastCompatible(const Type& rhs) const {
    if (isAssignmentCompatible(rhs))
        return true;

    return true;
}

std::string Type::toString() const {
    return "";
}

const Type& Type::fromSyntax(Compilation& compilation, const DataTypeSyntax& node, const Scope& parent) {
    switch (node.kind) {
        case SyntaxKind::BitType:
        case SyntaxKind::LogicType:
        case SyntaxKind::RegType:
            return IntegralType::fromSyntax(compilation, node.as<IntegerTypeSyntax>(), parent);
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
            return EnumType::fromSyntax(compilation, node.as<EnumTypeSyntax>(), parent);
        case SyntaxKind::StructType: {
            const auto& structUnion = node.as<StructUnionTypeSyntax>();
            return structUnion.packed ? PackedStructType::fromSyntax(compilation, structUnion, parent) :
                                        UnpackedStructType::fromSyntax(compilation, structUnion, parent);
        }
        default:
            THROW_UNREACHABLE;
    }
}

IntegralType::IntegralType(SymbolKind kind, string_view name, SourceLocation loc, uint32_t bitWidth_,
                           bool isSigned_, bool isFourState_) :
    Type(kind, name, loc),
    bitWidth(bitWidth_), isSigned(isSigned_), isFourState(isFourState_)
{
}

ConstantRange IntegralType::getBitVectorRange() const {
    if (isBuiltIn())
        return { (int)bitWidth - 1, 0 };

    ASSERT(kind == SymbolKind::VectorType);
    return as<VectorType>().range;
}

const Type& IntegralType::fromSyntax(Compilation& compilation, const IntegerTypeSyntax& syntax,
                                     const Scope& scope) {
    // This is a simple integral vector (possibly of just one element).
    bool isReg = syntax.keyword.kind == TokenKind::RegKeyword;
    bool isSigned = syntax.signing.kind == TokenKind::SignedKeyword;
    bool isFourState = syntax.kind != SyntaxKind::BitType;

    SmallVectorSized<ConstantRange, 4> dims;
    if (!evaluateConstantDims(compilation, syntax.dimensions, dims, scope))
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
        return compilation.getType((uint16_t)width, isSigned, isFourState, isReg);
    }

    const IntegralType* result = compilation.emplace<VectorType>(VectorType::getScalarType(isFourState, isReg),
                                                                 dims[0], isSigned);
    for (uint32_t i = 1; i < dims.size(); i++)
        result = compilation.emplace<PackedArrayType>(*result, dims[i]);

    return *result;
}

bool IntegralType::evaluateConstantDims(Compilation& compilation,
                                        const SyntaxList<VariableDimensionSyntax>& dimensions,
                                        SmallVector<ConstantRange>& results, const Scope& scope) {
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
        auto left = compilation.evaluateConstant(range.left, scope).coerceInteger(MaxRangeBits);
        auto right = compilation.evaluateConstant(range.right, scope).coerceInteger(MaxRangeBits);

        if (!left || !right)
            return false;

        results.emplace(ConstantRange { *left, *right });
    }
    return true;
}

BuiltInIntegerType::BuiltInIntegerType(Kind builtInKind) :
    BuiltInIntegerType(builtInKind, getSigned(builtInKind))
{
}

BuiltInIntegerType::BuiltInIntegerType(Kind builtInKind, bool isSigned) :
    IntegralType(SymbolKind::BuiltInIntegerType, "", SourceLocation(),
                 getWidth(builtInKind), isSigned, getFourState(builtInKind)),
    integerKind(builtInKind)
{
}

VectorType::VectorType(ScalarType scalarType_, ConstantRange range_, bool isSigned_) :
    IntegralType(SymbolKind::VectorType, "", SourceLocation(), range_.width(),
                 isSigned_, getFourState((BuiltInIntegerType::Kind)scalarType_)),
    range(range_),
    scalarType(scalarType_)
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

const Type& EnumType::fromSyntax(Compilation& compilation, const EnumTypeSyntax& syntax, const Scope& scope) {
    const Type* base;
    if (!syntax.baseType) 
        base = &compilation.getIntType();
    else {
        base = &compilation.getType(*syntax.baseType, scope);

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

    SVInt one((uint16_t)integralBase.bitWidth, 1, integralBase.isSigned);
    SVInt current((uint16_t)integralBase.bitWidth, 0, integralBase.isSigned);
    for (auto member : syntax.members) {
        ConstantValue value;
        if (!member->initializer)
            value = { *resultType, current };
        else {
            // TODO: conversion? range / overflow checking? non-constant?
            value = compilation.evaluateConstant(member->initializer->expr, *resultType);
        }

        auto ev = compilation.emplace<EnumValueSymbol>(compilation, member->name.valueText(),
                                                       member->name.location(), std::move(value));
        resultType->addMember(*ev);
        current = value.integer() + one;
    }

    return *resultType;
}

EnumValueSymbol::EnumValueSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                                 ConstantValue value_) :
    Symbol(SymbolKind::EnumValue, name, loc),
    value(*compilation.createConstant(std::move(value_)))
{
}

PackedArrayType::PackedArrayType(const Type& elementType_, ConstantRange range_) :
    IntegralType(SymbolKind::PackedArrayType, "", SourceLocation(), elementType_.getBitWidth() * range_.width(),
                 getSigned(elementType_), getFourState(elementType_)),
    elementType(elementType_), range(range_)
{
}

PackedStructType::PackedStructType(Compilation& compilation, uint32_t bitWidth,
                                   bool isSigned, bool isFourState) :
    IntegralType(SymbolKind::PackedStructType, "", SourceLocation(), bitWidth, isSigned, isFourState),
    Scope(compilation, this)
{
}

const Type& PackedStructType::fromSyntax(Compilation& compilation, const StructUnionTypeSyntax& syntax,
                                         const Scope& scope) {
    ASSERT(syntax.packed);
    bool isSigned = syntax.signing.kind == TokenKind::SignedKeyword;
    bool isFourState = false;
    uint32_t bitWidth = 0;

    // We have to look at all the members up front to know our width and four-statedness.
    SmallVectorSized<const Symbol*, 8> members;
    for (auto member : syntax.members) {
        const Type& type = compilation.getType(member->type, scope);
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
                                           const Scope& scope) {
    ASSERT(!syntax.packed);

    auto result = compilation.emplace<UnpackedStructType>(compilation);
    for (auto member : syntax.members) {
        const Type& type = compilation.getType(member->type, scope);
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

}
