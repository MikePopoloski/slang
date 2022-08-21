//------------------------------------------------------------------------------
//! @file AssignmentExpressions.h
//! @brief Definitions for assignment-related expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"

namespace slang {

class TimingControl;
struct BinaryExpressionSyntax;

/// Represents an assignment expression.
class AssignmentExpression : public Expression {
public:
    optional<BinaryOperator> op;
    const TimingControl* timingControl;

    AssignmentExpression(optional<BinaryOperator> op, bool nonBlocking, const Type& type,
                         Expression& left, Expression& right, const TimingControl* timingControl,
                         SourceRange sourceRange) :
        Expression(ExpressionKind::Assignment, type, sourceRange),
        op(op), timingControl(timingControl), left_(&left), right_(&right),
        nonBlocking(nonBlocking) {}

    bool isCompound() const { return op.has_value(); }
    bool isNonBlocking() const { return nonBlocking; }
    bool isLValueArg() const;

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const BinaryExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& fromComponents(Compilation& compilation, optional<BinaryOperator> op,
                                      bitmask<AssignFlags> flags, Expression& lhs, Expression& rhs,
                                      SourceLocation assignLoc, const TimingControl* timingControl,
                                      SourceRange sourceRange, const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Assignment; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        left().visit(visitor);
        right().visit(visitor);
    }

private:
    Expression* left_;
    Expression* right_;
    bool nonBlocking;
};

struct CastExpressionSyntax;
struct SignedCastExpressionSyntax;

// clang-format off
#define CK(x) \
    x(Implicit) \
    x(Propagated) \
    x(StreamingConcat) \
    x(Explicit) \
    x(BitstreamCast)
// clang-format on
ENUM(ConversionKind, CK)
#undef CK

/// Represents a type conversion expression (implicit or explicit).
class ConversionExpression : public Expression {
public:
    const ConversionKind conversionKind;

    ConversionExpression(const Type& type, ConversionKind conversionKind, Expression& operand,
                         SourceRange sourceRange) :
        Expression(ExpressionKind::Conversion, type, sourceRange),
        conversionKind(conversionKind), operand_(&operand) {}

    bool isImplicit() const { return conversionKind < ConversionKind::Explicit; }

    const Expression& operand() const { return *operand_; }
    Expression& operand() { return *operand_; }

    ConstantValue evalImpl(EvalContext& context) const;
    optional<bitwidth_t> getEffectiveWidthImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const CastExpressionSyntax& syntax,
                                  const BindContext& context);
    static Expression& fromSyntax(Compilation& compilation,
                                  const SignedCastExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& makeImplicit(const BindContext& context, const Type& targetType,
                                    ConversionKind conversionKind, Expression& expr,
                                    SourceLocation loc);

    static ConstantValue convert(EvalContext& context, const Type& from, const Type& to,
                                 SourceRange sourceRange, ConstantValue&& value,
                                 ConversionKind conversionKind);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Conversion; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        operand().visit(visitor);
    }

private:
    Expression* operand_;
};

struct NewArrayExpressionSyntax;

/// Represents a new[] expression that creates a dynamic array.
class NewArrayExpression : public Expression {
public:
    NewArrayExpression(const Type& type, const Expression& sizeExpr, const Expression* initializer,
                       SourceRange sourceRange) :
        Expression(ExpressionKind::NewArray, type, sourceRange),
        sizeExpr_(&sizeExpr), initializer_(initializer) {}

    const Expression& sizeExpr() const { return *sizeExpr_; }
    const Expression* initExpr() const { return initializer_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const NewArrayExpressionSyntax& syntax,
                                  const BindContext& context, const Type* assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::NewArray; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        sizeExpr().visit(visitor);
        if (initExpr())
            initExpr()->visit(visitor);
    }

private:
    const Expression* sizeExpr_;
    const Expression* initializer_;
};

struct NewClassExpressionSyntax;

/// Represents a `new` expression that creates a class instance.
class NewClassExpression : public Expression {
public:
    /// Set to true if this is invoking a super class's constructor.
    bool isSuperClass = false;

    NewClassExpression(const Type& type, const Expression* constructorCall, bool isSuperClass,
                       SourceRange sourceRange) :
        Expression(ExpressionKind::NewClass, type, sourceRange),
        isSuperClass(isSuperClass), constructorCall_(constructorCall) {}

    const Expression* constructorCall() const { return constructorCall_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const NewClassExpressionSyntax& syntax,
                                  const BindContext& context, const Type* assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::NewClass; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        if (constructorCall())
            constructorCall()->visit(visitor);
    }

private:
    const Expression* constructorCall_;
};

/// Represents a `new` expression that creates a covergroup instance.
class NewCovergroupExpression : public Expression {
public:
    span<const Expression* const> arguments;

    NewCovergroupExpression(const Type& type, span<const Expression* const> arguments,
                            SourceRange sourceRange) :
        Expression(ExpressionKind::NewCovergroup, type, sourceRange),
        arguments(arguments) {}

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const NewClassExpressionSyntax& syntax,
                                  const BindContext& context, const Type& assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::NewCovergroup; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto arg : arguments)
            arg->visit(visitor);
    }
};

/// Base class for assignment pattern expressions.
class AssignmentPatternExpressionBase : public Expression {
public:
    span<const Expression* const> elements() const { return elements_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto elem : elements())
            elem->visit(visitor);
    }

protected:
    AssignmentPatternExpressionBase(ExpressionKind kind, const Type& type,
                                    span<const Expression* const> elements,
                                    SourceRange sourceRange) :
        Expression(kind, type, sourceRange),
        elements_(elements) {}

private:
    span<const Expression* const> elements_;
};

struct SimpleAssignmentPatternSyntax;

/// Represents an assignment pattern expression.
class SimpleAssignmentPatternExpression : public AssignmentPatternExpressionBase {
public:
    SimpleAssignmentPatternExpression(const Type& type, span<const Expression* const> elements,
                                      SourceRange sourceRange) :
        AssignmentPatternExpressionBase(ExpressionKind::SimpleAssignmentPattern, type, elements,
                                        sourceRange) {}

    static Expression& forStruct(Compilation& compilation,
                                 const SimpleAssignmentPatternSyntax& syntax,
                                 const BindContext& context, const Type& type,
                                 const Scope& structScope, SourceRange sourceRange);

    static Expression& forFixedArray(Compilation& compilation,
                                     const SimpleAssignmentPatternSyntax& syntax,
                                     const BindContext& context, const Type& type,
                                     const Type& elementType, bitwidth_t numElements,
                                     SourceRange sourceRange);

    static Expression& forDynamicArray(Compilation& compilation,
                                       const SimpleAssignmentPatternSyntax& syntax,
                                       const BindContext& context, const Type& type,
                                       const Type& elementType, SourceRange sourceRange);

    static bool isKind(ExpressionKind kind) {
        return kind == ExpressionKind::SimpleAssignmentPattern;
    }
};

struct StructuredAssignmentPatternSyntax;

/// Represents an assignment pattern expression.
class StructuredAssignmentPatternExpression : public AssignmentPatternExpressionBase {
public:
    struct MemberSetter {
        not_null<const Symbol*> member;
        not_null<const Expression*> expr;
    };

    struct TypeSetter {
        not_null<const Type*> type;
        not_null<const Expression*> expr;
    };

    struct IndexSetter {
        not_null<const Expression*> index;
        not_null<const Expression*> expr;
    };

    span<const MemberSetter> memberSetters;
    span<const TypeSetter> typeSetters;
    span<const IndexSetter> indexSetters;
    const Expression* defaultSetter;

    StructuredAssignmentPatternExpression(const Type& type, span<const MemberSetter> memberSetters,
                                          span<const TypeSetter> typeSetters,
                                          span<const IndexSetter> indexSetters,
                                          const Expression* defaultSetter,
                                          span<const Expression* const> elements,
                                          SourceRange sourceRange) :
        AssignmentPatternExpressionBase(ExpressionKind::StructuredAssignmentPattern, type, elements,
                                        sourceRange),
        memberSetters(memberSetters), typeSetters(typeSetters), indexSetters(indexSetters),
        defaultSetter(defaultSetter) {}

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& forStruct(Compilation& compilation,
                                 const StructuredAssignmentPatternSyntax& syntax,
                                 const BindContext& context, const Type& type,
                                 const Scope& structScope, SourceRange sourceRange);

    static Expression& forFixedArray(Compilation& compilation,
                                     const StructuredAssignmentPatternSyntax& syntax,
                                     const BindContext& context, const Type& type,
                                     const Type& elementType, SourceRange sourceRange);

    static Expression& forDynamicArray(Compilation& compilation,
                                       const StructuredAssignmentPatternSyntax& syntax,
                                       const BindContext& context, const Type& type,
                                       const Type& elementType, SourceRange sourceRange);

    static Expression& forAssociativeArray(Compilation& compilation,
                                           const StructuredAssignmentPatternSyntax& syntax,
                                           const BindContext& context, const Type& type,
                                           const Type& elementType, SourceRange sourceRange);

    static bool isKind(ExpressionKind kind) {
        return kind == ExpressionKind::StructuredAssignmentPattern;
    }
};

struct ReplicatedAssignmentPatternSyntax;

/// Represents a replicated assignment pattern expression.
class ReplicatedAssignmentPatternExpression : public AssignmentPatternExpressionBase {
public:
    ReplicatedAssignmentPatternExpression(const Type& type, const Expression& count,
                                          span<const Expression* const> elements,
                                          SourceRange sourceRange) :
        AssignmentPatternExpressionBase(ExpressionKind::ReplicatedAssignmentPattern, type, elements,
                                        sourceRange),
        count_(&count) {}

    const Expression& count() const { return *count_; }

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& forStruct(Compilation& compilation,
                                 const ReplicatedAssignmentPatternSyntax& syntax,
                                 const BindContext& context, const Type& type,
                                 const Scope& structScope, SourceRange sourceRange);

    static Expression& forFixedArray(Compilation& compilation,
                                     const ReplicatedAssignmentPatternSyntax& syntax,
                                     const BindContext& context, const Type& type,
                                     const Type& elementType, bitwidth_t numElements,
                                     SourceRange sourceRange);

    static Expression& forDynamicArray(Compilation& compilation,
                                       const ReplicatedAssignmentPatternSyntax& syntax,
                                       const BindContext& context, const Type& type,
                                       const Type& elementType, SourceRange sourceRange);

    static bool isKind(ExpressionKind kind) {
        return kind == ExpressionKind::ReplicatedAssignmentPattern;
    }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        count().visit(visitor);
        AssignmentPatternExpressionBase::visitExprs(visitor);
    }

private:
    static const Expression& bindReplCount(Compilation& comp, const ExpressionSyntax& syntax,
                                           const BindContext& context, size_t& count);

    const Expression* count_;
};

} // namespace slang
