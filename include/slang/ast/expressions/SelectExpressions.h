//------------------------------------------------------------------------------
//! @file SelectExpressions.h
//! @brief Definitions for selection expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Expression.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

/// Represents a single element selection expression.
class SLANG_EXPORT ElementSelectExpression : public Expression {
public:
    ElementSelectExpression(const Type& type, Expression& value, const Expression& selector,
                            SourceRange sourceRange) :
        Expression(ExpressionKind::ElementSelect, type, sourceRange), value_(&value),
        selector_(&selector) {}

    /// @returns the value being selected from
    const Expression& value() const { return *value_; }

    /// @returns the value being selected from
    Expression& value() { return *value_; }

    /// @returns the selection expression
    const Expression& selector() const { return *selector_; }

    /// @returns true if this is a constant selection
    bool isConstantSelect(EvalContext& context) const;

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;
    bool requireLValueImpl(const ASTContext& context, SourceLocation location,
                           bitmask<AssignFlags> flags, const Expression* longestStaticPrefix) const;

    void getLongestStaticPrefixesImpl(
        SmallVector<std::pair<const ValueSymbol*, const Expression*>>& results,
        EvalContext& evalContext, const Expression* longestStaticPrefix) const;

    std::optional<ConstantRange> evalIndex(EvalContext& context, const ConstantValue& val,
                                           ConstantValue& associativeIndex, bool& softFail) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, Expression& value,
                                  const syntax::ExpressionSyntax& syntax, SourceRange fullRange,
                                  const ASTContext& context);

    static Expression& fromConstant(Compilation& compilation, Expression& value, int32_t index,
                                    const ASTContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::ElementSelect; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        value().visit(visitor);
        selector().visit(visitor);
    }

private:
    Expression* value_;
    const Expression* selector_;
    bool warnedAboutIndex = false;
};

/// Represents a range selection expression.
class SLANG_EXPORT RangeSelectExpression : public Expression {
public:
    RangeSelectExpression(RangeSelectionKind selectionKind, const Type& type, Expression& value,
                          const Expression& left, const Expression& right,
                          SourceRange sourceRange) :
        Expression(ExpressionKind::RangeSelect, type, sourceRange), value_(&value), left_(&left),
        right_(&right), selectionKind(selectionKind) {}

    /// @returns the value being selected from
    const Expression& value() const { return *value_; }

    /// @returns the value being selected from
    Expression& value() { return *value_; }

    /// @returns the left-hand side of the range
    const Expression& left() const { return *left_; }

    /// @returns the right-hand side of the range
    const Expression& right() const { return *right_; }

    /// @returns the kind of selection (simple or indexed).
    RangeSelectionKind getSelectionKind() const { return selectionKind; }

    /// @returns true if this is a constant selection
    bool isConstantSelect(EvalContext& context) const;

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;
    bool requireLValueImpl(const ASTContext& context, SourceLocation location,
                           bitmask<AssignFlags> flags, const Expression* longestStaticPrefix) const;

    void getLongestStaticPrefixesImpl(
        SmallVector<std::pair<const ValueSymbol*, const Expression*>>& results,
        EvalContext& evalContext, const Expression* longestStaticPrefix) const;

    std::optional<ConstantRange> evalRange(EvalContext& context, const ConstantValue& val,
                                           bool enforceBounds) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, Expression& value,
                                  const syntax::RangeSelectSyntax& syntax, SourceRange fullRange,
                                  const ASTContext& context);

    static Expression& fromConstant(Compilation& compilation, Expression& value,
                                    ConstantRange range, const ASTContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::RangeSelect; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        value().visit(visitor);
        left().visit(visitor);
        right().visit(visitor);
    }

private:
    Expression* value_;
    const Expression* left_;
    const Expression* right_;
    RangeSelectionKind selectionKind;
    bool warnedAboutRange = false;
};

/// Represents an access of a structure variable's members.
class SLANG_EXPORT MemberAccessExpression : public Expression {
public:
    /// The member being accessed.
    const Symbol& member;

    MemberAccessExpression(const Type& type, Expression& value, const Symbol& member,
                           SourceRange sourceRange) :
        Expression(ExpressionKind::MemberAccess, type, sourceRange), member(member),
        value_(&value) {}

    /// @returns the value being selected from
    const Expression& value() const { return *value_; }

    /// @returns the value being selected from
    Expression& value() { return *value_; }

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;
    bool requireLValueImpl(const ASTContext& context, SourceLocation location,
                           bitmask<AssignFlags> flags, const Expression* longestStaticPrefix) const;

    void getLongestStaticPrefixesImpl(
        SmallVector<std::pair<const ValueSymbol*, const Expression*>>& results,
        EvalContext& evalContext, const Expression* longestStaticPrefix) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSelector(
        Compilation& compilation, Expression& expr, const LookupResult::MemberSelector& selector,
        const syntax::InvocationExpressionSyntax* invocation,
        const syntax::ArrayOrRandomizeMethodExpressionSyntax* withClause, const ASTContext& context,
        bool isFromLookupChain);

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::MemberAccessExpressionSyntax& syntax,
                                  const syntax::InvocationExpressionSyntax* invocation,
                                  const syntax::ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                  const ASTContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::MemberAccess; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        value().visit(visitor);
    }

private:
    Expression* value_;
};

} // namespace slang::ast
