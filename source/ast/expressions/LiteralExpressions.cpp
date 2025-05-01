//------------------------------------------------------------------------------
// LiteralExpressions.cpp
// Definitions for literal expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/expressions/LiteralExpressions.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/types/Type.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace syntax;

IntegerLiteral::IntegerLiteral(BumpAllocator& alloc, const Type& type, const SVInt& value,
                               bool isDeclaredUnsized, SourceRange sourceRange) :
    Expression(ExpressionKind::IntegerLiteral, type, sourceRange),
    isDeclaredUnsized(isDeclaredUnsized),
    valueStorage(value.getBitWidth(), value.isSigned(), value.hasUnknown()) {

    if (value.isSingleWord())
        valueStorage.val = *value.getRawPtr();
    else {
        valueStorage.pVal = (uint64_t*)alloc.allocate(sizeof(uint64_t) * value.getNumWords(),
                                                      alignof(uint64_t));
        memcpy(valueStorage.pVal, value.getRawPtr(), sizeof(uint64_t) * value.getNumWords());
    }
}

Expression& IntegerLiteral::fromSyntax(Compilation& comp, const LiteralExpressionSyntax& syntax) {
    SLANG_ASSERT(syntax.kind == SyntaxKind::IntegerLiteralExpression);

    const Type* type;
    SVInt val = syntax.literal.intValue();
    if (val.getBitWidth() < 32 || comp.languageVersion() < LanguageVersion::v1800_2023) {
        // In v2023 the rule changed to not truncate unsized literals.
        // Literals smaller than 32 bits are always sized up to 32.
        val = val.resize(32);
        val.setSigned(true);
        type = &comp.getIntType();
    }
    else {
        if (!val.isSigned()) {
            // Note the +1 here to account for the sign bit we're going to add.
            val = val.resize(val.getBitWidth() + 1);
            val.setSigned(true);
        }
        type = &comp.getType(val.getBitWidth(), IntegralFlags::Signed);
    }

    return *comp.emplace<IntegerLiteral>(comp, *type, std::move(val), true, syntax.sourceRange());
}

Expression& IntegerLiteral::fromSyntax(Compilation& compilation,
                                       const IntegerVectorExpressionSyntax& syntax) {
    const SVInt& value = syntax.value.intValue();

    bitmask<IntegralFlags> flags;
    if (value.isSigned())
        flags |= IntegralFlags::Signed;
    if (value.hasUnknown())
        flags |= IntegralFlags::FourState;

    const Type& type = compilation.getType(value.getBitWidth(), flags);
    return *compilation.emplace<IntegerLiteral>(compilation, type, value, !syntax.size.valid(),
                                                syntax.sourceRange());
}

Expression& IntegerLiteral::fromConstant(Compilation& compilation, const SVInt& value) {
    SVInt val = value.resize(32);
    val.setSigned(true);

    return *compilation.emplace<IntegerLiteral>(compilation, compilation.getIntType(),
                                                std::move(val), true, SourceRange::NoLocation);
}

ConstantValue IntegerLiteral::evalImpl(EvalContext&) const {
    SVInt result = getValue();
    SLANG_ASSERT(result.getBitWidth() == type->getBitWidth());
    return result;
}

std::optional<bitwidth_t> IntegerLiteral::getEffectiveWidthImpl() const {
    return ConstantValue(getValue()).getEffectiveWidth();
}

Expression::EffectiveSign IntegerLiteral::getEffectiveSignImpl(bool isForConversion) const {
    // We will say that this literal could have been signed if doing
    // so would not change its logical value (i.e. it either already
    // was marked signed, or it's a positive value that would remain
    // positive given a cast to a signed type).
    //
    // We will not warn if the value contains unknowns -- the rationale
    // is that signed-related warnings make no sense in those cases, though
    // we should probably warn separately about the unknowns themselves.
    auto&& val = getValue();
    if (isForConversion || (!val.hasUnknown() && val.getActiveBits() == val.getBitWidth())) {
        return val.isSigned() ? EffectiveSign::Signed : EffectiveSign::Unsigned;
    }

    return EffectiveSign::Either;
}

void IntegerLiteral::serializeTo(ASTSerializer& serializer) const {
    serializer.write("value", getValue());
}

Expression& RealLiteral::fromSyntax(Compilation& compilation,
                                    const LiteralExpressionSyntax& syntax) {
    SLANG_ASSERT(syntax.kind == SyntaxKind::RealLiteralExpression);

    return *compilation.emplace<RealLiteral>(compilation.getRealType(), syntax.literal.realValue(),
                                             syntax.sourceRange());
}

ConstantValue RealLiteral::evalImpl(EvalContext&) const {
    return real_t(value);
}

void RealLiteral::serializeTo(ASTSerializer& serializer) const {
    serializer.write("value", getValue());
}

Expression& TimeLiteral::fromSyntax(const ASTContext& context,
                                    const LiteralExpressionSyntax& syntax) {
    SLANG_ASSERT(syntax.kind == SyntaxKind::TimeLiteralExpression);

    // The provided value needs to be scaled to the current scope's time units
    // and then rounded to the current scope's time precision.
    double value = syntax.literal.realValue();
    TimeUnit unit = syntax.literal.numericFlags().unit();
    TimeScale scale = context.scope->getTimeScale().value_or(TimeScale());
    value = scale.apply(value, unit, /* roundToPrecision */ false);

    auto& comp = context.getCompilation();
    return *comp.emplace<TimeLiteral>(comp.getType(SyntaxKind::RealTimeType), value,
                                      syntax.sourceRange());
}

ConstantValue TimeLiteral::evalImpl(EvalContext&) const {
    return real_t(value);
}

void TimeLiteral::serializeTo(ASTSerializer& serializer) const {
    serializer.write("value", getValue());
}

Expression& UnbasedUnsizedIntegerLiteral::fromSyntax(Compilation& compilation,
                                                     const LiteralExpressionSyntax& syntax) {
    SLANG_ASSERT(syntax.kind == SyntaxKind::UnbasedUnsizedLiteralExpression);

    // UnsizedUnbasedLiteralExpressions default to a size of 1 in an undetermined
    // context, but can grow to be wider during propagation.
    logic_t val = syntax.literal.bitValue();
    return *compilation.emplace<UnbasedUnsizedIntegerLiteral>(
        compilation.getType(1,
                            val.isUnknown() ? IntegralFlags::FourState : IntegralFlags::TwoState),
        val, syntax.sourceRange());
}

bool UnbasedUnsizedIntegerLiteral::propagateType(const ASTContext&, const Type& newType,
                                                 SourceRange, ConversionKind) {
    SLANG_ASSERT(newType.isIntegral());
    SLANG_ASSERT(newType.getBitWidth());

    type = &newType;
    return true;
}

SVInt UnbasedUnsizedIntegerLiteral::getValue() const {
    bitwidth_t width = type->getBitWidth();
    bool isSigned = type->isSigned();

    switch (value.value) {
        case 0:
            return SVInt(width, 0, isSigned);
        case 1: {
            SVInt tmp(width, 0, isSigned);
            tmp.setAllOnes();
            return tmp;
        }
        case logic_t::X_VALUE:
            return SVInt::createFillX(width, isSigned);
        case logic_t::Z_VALUE:
            return SVInt::createFillZ(width, isSigned);
        default:
            SLANG_UNREACHABLE;
    }
}

ConstantValue UnbasedUnsizedIntegerLiteral::evalImpl(EvalContext&) const {
    return getValue();
}

std::optional<bitwidth_t> UnbasedUnsizedIntegerLiteral::getEffectiveWidthImpl() const {
    return 1;
}

Expression::EffectiveSign UnbasedUnsizedIntegerLiteral::getEffectiveSignImpl(bool) const {
    // We don't really want warnings for things like this:
    // logic signed [1:0] k = '1;
    // ...so we'll just say this could always be either.
    return EffectiveSign::Either;
}

void UnbasedUnsizedIntegerLiteral::serializeTo(ASTSerializer& serializer) const {
    serializer.write("value", getValue());
}

Expression& NullLiteral::fromSyntax(Compilation& compilation,
                                    const LiteralExpressionSyntax& syntax) {
    SLANG_ASSERT(syntax.kind == SyntaxKind::NullLiteralExpression);
    return *compilation.emplace<NullLiteral>(compilation.getNullType(), syntax.sourceRange());
}

ConstantValue NullLiteral::evalImpl(EvalContext&) const {
    return ConstantValue::NullPlaceholder{};
}

Expression& UnboundedLiteral::fromSyntax(const ASTContext& context,
                                         const LiteralExpressionSyntax& syntax) {
    SLANG_ASSERT(syntax.kind == SyntaxKind::WildcardLiteralExpression);

    auto& comp = context.getCompilation();
    if (!context.flags.has(ASTFlags::AllowUnboundedLiteral) && !context.inUnevaluatedBranch()) {
        context.addDiag(diag::UnboundedNotAllowed, syntax.sourceRange());
        return badExpr(comp, nullptr);
    }

    return *comp.emplace<UnboundedLiteral>(comp.getUnboundedType(), syntax.sourceRange());
}

ConstantValue UnboundedLiteral::evalImpl(EvalContext& context) const {
    // If we're evaluating in a context with a queue target expression, use the
    // max bound of that queue. Otherwise assume we're assigning to a constant (parameter)
    // and use a placeholder value to indicate that.
    auto target = context.getQueueTarget();
    if (!target) {
        if (context.flags.has(EvalFlags::AllowUnboundedPlaceholder))
            return ConstantValue::UnboundedPlaceholder{};
        return nullptr;
    }

    int32_t size = (int32_t)target->queue()->size();
    return SVInt(32, uint64_t(size - 1), true);
}

StringLiteral::StringLiteral(const Type& type, std::string_view value, std::string_view rawValue,
                             ConstantValue& intVal, SourceRange sourceRange) :
    Expression(ExpressionKind::StringLiteral, type, sourceRange), value(value), rawValue(rawValue),
    intStorage(&intVal) {
}

Expression& StringLiteral::fromSyntax(const ASTContext& context,
                                      const LiteralExpressionSyntax& syntax) {
    SLANG_ASSERT(syntax.kind == SyntaxKind::StringLiteralExpression);

    std::string_view value = syntax.literal.valueText();
    bitwidth_t width;
    ConstantValue* intVal;

    auto& comp = context.getCompilation();
    if (value.empty()) {
        // [11.10.3] says that empty string literals take on a value of "\0" (8 zero bits).
        width = 8;
        intVal = comp.allocConstant(SVInt(8, 0, false));
    }
    else {
        width = bitwidth_t(value.size() * 8);
        if (width > (uint32_t)SVInt::MAX_BITS) {
            context.addDiag(diag::PackedTypeTooLarge, syntax.sourceRange())
                << width << (uint32_t)SVInt::MAX_BITS;
            return badExpr(comp, nullptr);
        }

        // String literals represented as integers put the first character on the
        // left, which translates to the msb, so we have to reverse the string.
        SmallVector<byte> bytes;
        for (char c : std::views::reverse(value))
            bytes.push_back((byte)c);

        intVal = comp.allocConstant(SVInt(width, bytes, false));
    }

    auto& type = comp.getType(width, IntegralFlags::Unsigned);
    return *comp.emplace<StringLiteral>(type, value, syntax.literal.rawText(), *intVal,
                                        syntax.sourceRange());
}

const ConstantValue& StringLiteral::getIntValue() const {
    return *intStorage;
}

ConstantValue StringLiteral::evalImpl(EvalContext&) const {
    return *intStorage;
}

void StringLiteral::serializeTo(ASTSerializer& serializer) const {
    serializer.write("literal", value);
}

} // namespace slang::ast
