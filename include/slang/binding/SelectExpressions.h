//------------------------------------------------------------------------------
//! @file SelectExpressions.h
//! @brief Definitions for selection expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"

namespace slang {

/// Represents a single element selection expression.
class ElementSelectExpression : public Expression {
public:
    ElementSelectExpression(const Type& type, Expression& value, const Expression& selector,
                            SourceRange sourceRange) :
        Expression(ExpressionKind::ElementSelect, type, sourceRange),
        value_(&value), selector_(&selector) {}

    const Expression& value() const { return *value_; }
    Expression& value() { return *value_; }

    const Expression& selector() const { return *selector_; }

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, Expression& value,
                                  const ExpressionSyntax& syntax, SourceRange fullRange,
                                  const BindContext& context);

    static Expression& fromConstant(Compilation& compilation, Expression& value, int32_t index,
                                    const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::ElementSelect; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        value().visit(visitor);
        selector().visit(visitor);
    }

private:
    Expression* value_;
    const Expression* selector_;
};

struct RangeSelectSyntax;

/// Represents a range selection expression.
class RangeSelectExpression : public Expression {
public:
    RangeSelectionKind selectionKind;

    RangeSelectExpression(RangeSelectionKind selectionKind, const Type& type, Expression& value,
                          const Expression& left, const Expression& right,
                          SourceRange sourceRange) :
        Expression(ExpressionKind::RangeSelect, type, sourceRange),
        selectionKind(selectionKind), value_(&value), left_(&left), right_(&right) {}

    const Expression& value() const { return *value_; }
    Expression& value() { return *value_; }

    const Expression& left() const { return *left_; }
    const Expression& right() const { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, Expression& value,
                                  const RangeSelectSyntax& syntax, SourceRange fullRange,
                                  const BindContext& context);

    static Expression& fromConstant(Compilation& compilation, Expression& value,
                                    ConstantRange range, const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::RangeSelect; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        value().visit(visitor);
        left().visit(visitor);
        right().visit(visitor);
    }

    static ConstantRange getIndexedRange(RangeSelectionKind kind, int32_t l, int32_t r,
                                         bool littleEndian);

private:
    optional<ConstantRange> getFixedRange(EvalContext& context, const ConstantValue& cl,
                                          const ConstantValue& cr) const;
    optional<ConstantRange> getDynamicRange(EvalContext& context, const ConstantValue& cl,
                                            const ConstantValue& cr, const ConstantValue& cv) const;

    Expression* value_;
    const Expression* left_;
    const Expression* right_;
};

class FieldSymbol;
struct MemberAccessExpressionSyntax;

/// Represents an access of a structure variable's members.
class MemberAccessExpression : public Expression {
public:
    const Symbol& member;
    uint32_t offset;

    MemberAccessExpression(const Type& type, Expression& value, const Symbol& member,
                           uint32_t offset, SourceRange sourceRange) :
        Expression(ExpressionKind::MemberAccess, type, sourceRange),
        member(member), offset(offset), value_(&value) {}

    const Expression& value() const { return *value_; }
    Expression& value() { return *value_; }

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;
    bool verifyAssignableImpl(const BindContext& context, bool isNonBlocking,
                              SourceLocation location) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSelector(Compilation& compilation, Expression& expr,
                                    const LookupResult::MemberSelector& selector,
                                    const InvocationExpressionSyntax* invocation,
                                    const BindContext& context);

    static Expression& fromSyntax(Compilation& compilation,
                                  const MemberAccessExpressionSyntax& syntax,
                                  const InvocationExpressionSyntax* invocation,
                                  const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::MemberAccess; }

private:
    Expression* value_;
};

} // namespace slang
