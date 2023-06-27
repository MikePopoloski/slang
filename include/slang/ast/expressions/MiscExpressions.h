//------------------------------------------------------------------------------
//! @file MiscExpressions.h
//! @brief Definitions for miscellaneous expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Expression.h"
#include "slang/ast/TimingControl.h"
#include "slang/ast/expressions/AssertionExpr.h"
#include "slang/ast/symbols/ValueSymbol.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

class AssertionPortSymbol;
class VariableSymbol;

/// Common base class for both NamedValueExpression and HierarchicalValueExpression.
class SLANG_EXPORT ValueExpressionBase : public Expression {
public:
    const ValueSymbol& symbol;

    bool requireLValueImpl(const ASTContext& context, SourceLocation location,
                           bitmask<AssignFlags> flags, const Expression* longestStaticPrefix) const;
    void getLongestStaticPrefixesImpl(
        SmallVector<std::pair<const ValueSymbol*, const Expression*>>& results,
        const Expression* longestStaticPrefix) const;

    std::optional<bitwidth_t> getEffectiveWidthImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSymbol(const ASTContext& context, const Symbol& symbol,
                                  bool isHierarchical, SourceRange sourceRange,
                                  bool constraintAllowed = false, bool isDottedAccess = false);

    static bool checkVariableAssignment(const ASTContext& context, const VariableSymbol& var,
                                        bitmask<AssignFlags> flags, SourceLocation assignLoc,
                                        SourceRange varRange);

    static bool isKind(ExpressionKind kind) {
        return kind == ExpressionKind::NamedValue || kind == ExpressionKind::HierarchicalValue;
    }

protected:
    ValueExpressionBase(ExpressionKind kind, const ValueSymbol& symbol, SourceRange sourceRange) :
        Expression(kind, symbol.getType(), sourceRange), symbol(symbol) {}

    bool checkConstantBase(EvalContext& context) const;
};

/// Represents an expression that references a named value.
class SLANG_EXPORT NamedValueExpression : public ValueExpressionBase {
public:
    NamedValueExpression(const ValueSymbol& symbol, SourceRange sourceRange) :
        ValueExpressionBase(ExpressionKind::NamedValue, symbol, sourceRange) {}

    ConstantValue evalImpl(EvalContext& context) const;
    LValue evalLValueImpl(EvalContext& context) const;

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::NamedValue; }

private:
    bool checkConstant(EvalContext& context) const;
};

/// Represents an expression that references a named value via hierarchical path.
class SLANG_EXPORT HierarchicalValueExpression : public ValueExpressionBase {
public:
    HierarchicalValueExpression(const ValueSymbol& symbol, SourceRange sourceRange) :
        ValueExpressionBase(ExpressionKind::HierarchicalValue, symbol, sourceRange) {}

    ConstantValue evalImpl(EvalContext& context) const;

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::HierarchicalValue; }
};

/// Adapts a data type for use in an expression tree. This is for cases where both an expression
/// and a data type is valid; for example, as an argument to a $bits() call or as a parameter
/// assignment (because of type parameters).
class SLANG_EXPORT DataTypeExpression : public Expression {
public:
    DataTypeExpression(const Type& type, SourceRange sourceRange) :
        Expression(ExpressionKind::DataType, type, sourceRange) {}

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }

    void serializeTo(ASTSerializer&) const {}

    static Expression& fromSyntax(Compilation& compilation, const syntax::DataTypeSyntax& syntax,
                                  const ASTContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::DataType; }
};

/// An expression that gets the type of a nested expression using the type() operator.
/// The result is only allowed in a few places in the grammar, namely in comparisons
/// with other type reference expressions.
class SLANG_EXPORT TypeReferenceExpression : public Expression {
public:
    const Type& targetType;

    TypeReferenceExpression(const Type& typeRefType, const Type& targetType,
                            SourceRange sourceRange) :
        Expression(ExpressionKind::TypeReference, typeRefType, sourceRange),
        targetType(targetType) {}

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::TypeReference; }
};

/// Adapts an arbitrary symbol reference for use in an expression tree. This is for cases
/// like the $printtimescale system function that require a module name to be passed.
/// This is not a NamedValueExpression because the symbol in question is not a value
/// and is not normally usable in an expression.
class SLANG_EXPORT ArbitrarySymbolExpression : public Expression {
public:
    not_null<const Symbol*> symbol;

    ArbitrarySymbolExpression(const Symbol& symbol, const Type& type, SourceRange sourceRange) :
        Expression(ExpressionKind::ArbitrarySymbol, type, sourceRange), symbol(&symbol) {}

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const syntax::NameSyntax& syntax,
                                  const ASTContext& context,
                                  bitmask<LookupFlags> extraLookupFlags = {});

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::ArbitrarySymbol; }
};

/// A placeholder expression that is generated to take the place of one side of
/// a compound assignment expression's binary operator. It indicates to the constant
/// evaluator that it should look on the lvalue stack for the value to use.
class SLANG_EXPORT LValueReferenceExpression : public Expression {
public:
    LValueReferenceExpression(const Type& type, SourceRange sourceRange) :
        Expression(ExpressionKind::LValueReference, type, sourceRange) {}

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::LValueReference; }
};

/// Represents an empty argument. There's no actual syntax to go along with this,
/// but we use this as a placeholder to hold the fact that the argument is empty.
class SLANG_EXPORT EmptyArgumentExpression : public Expression {
public:
    EmptyArgumentExpression(const Type& type, SourceRange sourceRange) :
        Expression(ExpressionKind::EmptyArgument, type, sourceRange) {}

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::EmptyArgument; }
};

/// Represents a clocking event expression. This is a special kind of expression that is only
/// allowed with the sampled value system functions and assertion instance arguments.
class SLANG_EXPORT ClockingEventExpression : public Expression {
public:
    const TimingControl& timingControl;

    ClockingEventExpression(const Type& type, const TimingControl& timingControl,
                            SourceRange sourceRange) :
        Expression(ExpressionKind::ClockingEvent, type, sourceRange),
        timingControl(timingControl) {}

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }

    static Expression& fromSyntax(const syntax::ClockingPropertyExprSyntax& syntax,
                                  const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::ClockingEvent; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return timingControl.visit(visitor);
    }
};

/// Represents an instance of an assertion item, either a sequence, a property,
/// or a formal argument that is being referenced and expanded.
class SLANG_EXPORT AssertionInstanceExpression : public Expression {
public:
    using ActualArg = std::variant<const Expression*, const AssertionExpr*, const TimingControl*>;

    const Symbol& symbol;
    const AssertionExpr& body;
    std::span<std::tuple<const Symbol*, ActualArg> const> arguments;
    std::span<const Symbol* const> localVars;
    bool isRecursiveProperty;

    AssertionInstanceExpression(const Type& type, const Symbol& symbol, const AssertionExpr& body,
                                bool isRecursiveProperty, SourceRange sourceRange) :
        Expression(ExpressionKind::AssertionInstance, type, sourceRange),
        symbol(symbol), body(body), isRecursiveProperty(isRecursiveProperty) {}

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }

    static Expression& fromLookup(const Symbol& symbol,
                                  const syntax::InvocationExpressionSyntax* syntax,
                                  SourceRange range, const ASTContext& context);

    static Expression& makeDefault(const Symbol& symbol);

    static Expression& bindPort(const Symbol& symbol, SourceRange range, const ASTContext& context);

    static bool checkAssertionArg(const syntax::PropertyExprSyntax& propExpr,
                                  const AssertionPortSymbol& formal, const ASTContext& context,
                                  ActualArg& result, bool isRecursiveProp);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::AssertionInstance; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        body.visit(visitor);
        for (auto sym : localVars) {
            auto dt = sym->getDeclaredType();
            SLANG_ASSERT(dt);
            if (auto init = dt->getInitializer())
                init->visit(visitor);
        }
    }
};

/// Represents a min:typ:max expression.
class SLANG_EXPORT MinTypMaxExpression : public Expression {
public:
    MinTypMaxExpression(const Type& type, Expression& min, Expression& typ, Expression& max,
                        Expression* selected, SourceRange sourceRange) :
        Expression(ExpressionKind::MinTypMax, type, sourceRange),
        selected_(selected), min_(&min), typ_(&typ), max_(&max) {}

    const Expression& min() const { return *min_; }
    Expression& min() { return *min_; }

    const Expression& typ() const { return *typ_; }
    Expression& typ() { return *typ_; }

    const Expression& max() const { return *max_; }
    Expression& max() { return *max_; }

    const Expression& selected() const { return *selected_; }
    Expression& selected() { return *selected_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool propagateType(const ASTContext& context, const Type& newType);
    std::optional<bitwidth_t> getEffectiveWidthImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::MinTypMaxExpressionSyntax& syntax,
                                  const ASTContext& context, const Type* assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::MinTypMax; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        min().visit(visitor);
        typ().visit(visitor);
        max().visit(visitor);
    }

private:
    Expression* selected_;
    Expression* min_;
    Expression* typ_;
    Expression* max_;
};

/// Represents a `new` expression that copies a class instance.
class SLANG_EXPORT CopyClassExpression : public Expression {
public:
    CopyClassExpression(const Type& type, const Expression& sourceExpr, SourceRange sourceRange) :
        Expression(ExpressionKind::CopyClass, type, sourceRange), sourceExpr_(sourceExpr) {}

    const Expression& sourceExpr() const { return sourceExpr_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::CopyClassExpressionSyntax& syntax,
                                  const ASTContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::CopyClass; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return sourceExpr().visit(visitor);
    }

private:
    const Expression& sourceExpr_;
};

/// Denotes an expression along with a distribution of probabilities for that
/// expression. This can't occur in normal expression code; it's used as part
/// of constraints and properties (and always has the type 'void').
class SLANG_EXPORT DistExpression : public Expression {
public:
    struct DistWeight {
        enum Kind { PerValue, PerRange } kind;
        const Expression& expr;
    };

    struct DistItem {
        const Expression& value;
        std::optional<DistWeight> weight;
    };

    DistExpression(const Type& type, const Expression& left, std::span<DistItem> items,
                   SourceRange sourceRange) :
        Expression(ExpressionKind::Dist, type, sourceRange),
        left_(&left), items_(items) {}

    const Expression& left() const { return *left_; }
    std::span<DistItem const> items() const { return items_; }

    ConstantValue evalImpl(EvalContext&) const { return nullptr; }

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& comp, const syntax::ExpressionOrDistSyntax& syntax,
                                  const ASTContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Dist; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        left().visit(visitor);
        for (auto& item : items_) {
            item.value.visit(visitor);
            if (item.weight)
                item.weight->expr.visit(visitor);
        }
    }

private:
    const Expression* left_;
    std::span<DistItem> items_;
};

/// Represents a tagged union member setter expression.
class SLANG_EXPORT TaggedUnionExpression : public Expression {
public:
    const Symbol& member;
    const Expression* valueExpr;

    TaggedUnionExpression(const Type& type, const Symbol& member, const Expression* valueExpr,
                          SourceRange sourceRange) :
        Expression(ExpressionKind::TaggedUnion, type, sourceRange),
        member(member), valueExpr(valueExpr) {}

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::TaggedUnionExpressionSyntax& syntax,
                                  const ASTContext& context, const Type* assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::TaggedUnion; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        if (valueExpr)
            valueExpr->visit(visitor);
    }
};

} // namespace slang::ast
