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

uint32_t getWidth(span<ConstantRange const> dims) {
    uint32_t width = 0;
    for (const auto& dim : dims)
        width += dim.width();
    return width;
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

    const auto& vt = as<VectorType>();
    ASSERT(vt.dimensions.size() == 1);
    return vt.dimensions[0];
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
    else {
        return compilation.getType(isSigned, isFourState, isReg, dims.copy(compilation));
    }
}

bool IntegralType::evaluateConstantDims(Compilation&,
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
        auto left = scope.evaluateConstant(range.left).coerceInteger(MaxRangeBits);
        auto right = scope.evaluateConstant(range.right).coerceInteger(MaxRangeBits);

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

VectorType::VectorType(ScalarType scalarType_, span<ConstantRange const> dimensions_, bool isSigned) :
    IntegralType(SymbolKind::VectorType, "", SourceLocation(),
                 getWidth(dimensions_), isSigned, getFourState((BuiltInIntegerType::Kind)scalarType_)),
    dimensions(dimensions_),
    scalarType(scalarType_)
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
            value = resultType->evaluateConstant(member->initializer->expr);
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

FloatingType::FloatingType(Kind floatKind_) :
    Type(SymbolKind::FloatingType, "", SourceLocation()),
    floatKind(floatKind_)
{
}

}
