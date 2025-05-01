//------------------------------------------------------------------------------
//! @file ConversionExpression.h
//! @brief Definitions for conversion expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Expression.h"

namespace slang::ast {

/// Represents a type conversion expression (implicit or explicit).
class SLANG_EXPORT ConversionExpression : public Expression {
public:
    /// The kind of conversion.
    const ConversionKind conversionKind;

    ConversionExpression(const Type& type, ConversionKind conversionKind, Expression& operand,
                         SourceRange sourceRange) :
        Expression(ExpressionKind::Conversion, type, sourceRange), conversionKind(conversionKind),
        operand_(&operand) {}

    /// @returns true if this is an implicit conversion
    bool isImplicit() const { return conversionKind < ConversionKind::StreamingConcat; }

    /// @returns the operand of the conversion
    const Expression& operand() const { return *operand_; }

    /// @returns the operand of the conversion
    Expression& operand() { return *operand_; }

    ConstantValue evalImpl(EvalContext& context) const;
    std::optional<bitwidth_t> getEffectiveWidthImpl() const;
    EffectiveSign getEffectiveSignImpl(bool isForConversion) const;

    ConstantValue applyTo(EvalContext& context, ConstantValue&& value) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::CastExpressionSyntax& syntax,
                                  const ASTContext& context, const Type* assignmentTarget);
    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::SignedCastExpressionSyntax& syntax,
                                  const ASTContext& context);

    static Expression& makeImplicit(const ASTContext& context, const Type& targetType,
                                    ConversionKind conversionKind, Expression& expr,
                                    const Expression* parentExpr, SourceRange opRange);

    static ConstantValue convert(EvalContext& context, const Type& from, const Type& to,
                                 SourceRange sourceRange, ConstantValue&& value,
                                 ConversionKind conversionKind, const Expression* expr = nullptr,
                                 SourceRange implicitOpRange = {});

    static void checkImplicitConversions(const ASTContext& context, const Type& from,
                                         const Type& to, const Expression& expr,
                                         const Expression* parentExpr, SourceRange opRange,
                                         ConversionKind conversionKind);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Conversion; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return operand().visit(visitor);
    }

private:
    Expression* operand_;
    SourceRange implicitOpRange;
};

} // namespace slang::ast
