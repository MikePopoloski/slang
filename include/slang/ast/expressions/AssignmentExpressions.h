//------------------------------------------------------------------------------
//! @file AssignmentExpressions.h
//! @brief Definitions for assignment-related expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Expression.h"
#include "slang/ast/TimingControl.h"
#include "slang/ast/expressions/Operator.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::ast {

class TimingControl;

/// Represents an assignment expression.
class SLANG_EXPORT AssignmentExpression : public Expression {
public:
    /// An optional operator that applies to the assignment
    /// (i.e. a compound assignment expression).
    std::optional<BinaryOperator> op;

    /// An optional timing control that applies to the assignment.
    const TimingControl* timingControl;

    AssignmentExpression(std::optional<BinaryOperator> op, bool nonBlocking, const Type& type,
                         Expression& left, Expression& right, const TimingControl* timingControl,
                         SourceRange sourceRange) :
        Expression(ExpressionKind::Assignment, type, sourceRange), op(op),
        timingControl(timingControl), left_(&left), right_(&right), nonBlocking(nonBlocking) {}

    /// @returns true if this is a compound assignment
    bool isCompound() const { return op.has_value(); }

    /// @returns true if this is a non-blocking assignment
    bool isNonBlocking() const { return nonBlocking; }

    /// @returns true if this is a blocking assignment
    bool isBlocking() const { return !nonBlocking; }

    /// @returns true if this assignment has been implied by the lhs being the target
    /// of an lvalue argument or port connection (i.e. there is no explicit assignment
    /// operator or rhs here).
    bool isLValueArg() const;

    /// @returns the left-hand side of the assignment
    const Expression& left() const { return *left_; }

    /// @returns the left-hand side of the assignment
    Expression& left() { return *left_; }

    /// @returns the right-hand side of the assignment
    const Expression& right() const { return *right_; }

    /// @returns the right-hand side of the assignment
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::BinaryExpressionSyntax& syntax,
                                  const ASTContext& context);

    static Expression& fromComponents(Compilation& compilation, std::optional<BinaryOperator> op,
                                      bitmask<AssignFlags> flags, Expression& lhs, Expression& rhs,
                                      SourceRange opRange, const TimingControl* timingControl,
                                      SourceRange sourceRange, const ASTContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Assignment; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        if (timingControl)
            timingControl->visit(visitor);
        left().visit(visitor);
        right().visit(visitor);
    }

private:
    Expression* left_;
    Expression* right_;
    bool nonBlocking;
};

/// Represents a new[] expression that creates a dynamic array.
class SLANG_EXPORT NewArrayExpression : public Expression {
public:
    NewArrayExpression(const Type& type, const Expression& sizeExpr, const Expression* initializer,
                       SourceRange sourceRange) :
        Expression(ExpressionKind::NewArray, type, sourceRange), sizeExpr_(&sizeExpr),
        initializer_(initializer) {}

    /// @returns the expression indicating the size of the array to create
    const Expression& sizeExpr() const { return *sizeExpr_; }

    /// @returns an optional expression that initializes the array
    const Expression* initExpr() const { return initializer_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::NewArrayExpressionSyntax& syntax,
                                  const ASTContext& context, const Type* assignmentTarget);

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

/// Represents a `new` expression that creates a class instance.
class SLANG_EXPORT NewClassExpression : public Expression {
public:
    /// Set to true if this is invoking a super class's constructor.
    bool isSuperClass = false;

    NewClassExpression(const Type& type, const Expression* constructorCall, bool isSuperClass,
                       SourceRange sourceRange) :
        Expression(ExpressionKind::NewClass, type, sourceRange), isSuperClass(isSuperClass),
        constructorCall_(constructorCall) {}

    /// @returns an optional expression that calls the class's constructor
    const Expression* constructorCall() const { return constructorCall_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::NewClassExpressionSyntax& syntax,
                                  const ASTContext& context, const Type* assignmentTarget);

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::SuperNewDefaultedArgsExpressionSyntax& syntax,
                                  const ASTContext& context, const Type* assignmentTarget);

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
class SLANG_EXPORT NewCovergroupExpression : public Expression {
public:
    /// A list of arguments to the new expression.
    std::span<const Expression* const> arguments;

    NewCovergroupExpression(const Type& type, std::span<const Expression* const> arguments,
                            SourceRange sourceRange) :
        Expression(ExpressionKind::NewCovergroup, type, sourceRange), arguments(arguments) {}

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation,
                                  const syntax::NewClassExpressionSyntax& syntax,
                                  const ASTContext& context, const Type& assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::NewCovergroup; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto arg : arguments)
            arg->visit(visitor);
    }
};

/// Base class for assignment pattern expressions.
class SLANG_EXPORT AssignmentPatternExpressionBase : public Expression {
public:
    /// @returns the list of elements in the assignment pattern
    std::span<const Expression* const> elements() const { return elements_; }

    ConstantValue evalImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto elem : elements())
            elem->visit(visitor);
    }

protected:
    AssignmentPatternExpressionBase(ExpressionKind kind, const Type& type,
                                    std::span<const Expression* const> elements,
                                    SourceRange sourceRange) :
        Expression(kind, type, sourceRange), elements_(elements) {}

private:
    std::span<const Expression* const> elements_;
};

/// Represents a simple assignment pattern expression.
class SLANG_EXPORT SimpleAssignmentPatternExpression : public AssignmentPatternExpressionBase {
public:
    /// True if this assignment pattern is an lvalue, and false otherwise.
    bool isLValue;

    SimpleAssignmentPatternExpression(const Type& type, bool isLValue,
                                      std::span<const Expression* const> elements,
                                      SourceRange sourceRange) :
        AssignmentPatternExpressionBase(ExpressionKind::SimpleAssignmentPattern, type, elements,
                                        sourceRange),
        isLValue(isLValue) {}

    LValue evalLValueImpl(EvalContext& context) const;

    ConstantValue applyConversions(EvalContext& context, const ConstantValue& rval) const;

    static Expression& forStruct(Compilation& compilation,
                                 const syntax::SimpleAssignmentPatternSyntax& syntax,
                                 const ASTContext& context, const Type& type,
                                 const Scope& structScope, SourceRange sourceRange);

    static Expression& forFixedArray(Compilation& compilation,
                                     const syntax::SimpleAssignmentPatternSyntax& syntax,
                                     const ASTContext& context, const Type& type,
                                     const Type& elementType, bitwidth_t numElements,
                                     SourceRange sourceRange);

    static Expression& forDynamicArray(Compilation& compilation,
                                       const syntax::SimpleAssignmentPatternSyntax& syntax,
                                       const ASTContext& context, const Type& type,
                                       const Type& elementType, SourceRange sourceRange);

    static bool isKind(ExpressionKind kind) {
        return kind == ExpressionKind::SimpleAssignmentPattern;
    }
};

/// Represents a structured assignment pattern expression.
class SLANG_EXPORT StructuredAssignmentPatternExpression : public AssignmentPatternExpressionBase {
public:
    /// A setter for a specific type member.
    struct MemberSetter {
        /// The member to which this setter applies.
        not_null<const Symbol*> member;

        /// An expression for the value to set.
        not_null<const Expression*> expr;
    };

    /// A setter for a specific type.
    struct TypeSetter {
        /// The type to which this setter applies.
        not_null<const Type*> type;

        /// An expression for the value to set.
        not_null<const Expression*> expr;
    };

    /// A setter for a specific array index.
    struct IndexSetter {
        /// The array index expression.
        not_null<const Expression*> index;

        /// An expression for the value to set.
        not_null<const Expression*> expr;
    };

    /// A list of members to set.
    std::span<const MemberSetter> memberSetters;

    /// A list of types to match against and set.
    std::span<const TypeSetter> typeSetters;

    /// A list of specific array elements to set.
    std::span<const IndexSetter> indexSetters;

    /// An optional default setter to apply for elements
    /// that don't match a more specific setter.
    const Expression* defaultSetter;

    StructuredAssignmentPatternExpression(const Type& type,
                                          std::span<const MemberSetter> memberSetters,
                                          std::span<const TypeSetter> typeSetters,
                                          std::span<const IndexSetter> indexSetters,
                                          const Expression* defaultSetter,
                                          std::span<const Expression* const> elements,
                                          SourceRange sourceRange) :
        AssignmentPatternExpressionBase(ExpressionKind::StructuredAssignmentPattern, type, elements,
                                        sourceRange),
        memberSetters(memberSetters), typeSetters(typeSetters), indexSetters(indexSetters),
        defaultSetter(defaultSetter) {}

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& forStruct(Compilation& compilation,
                                 const syntax::StructuredAssignmentPatternSyntax& syntax,
                                 const ASTContext& context, const Type& type,
                                 const Scope& structScope, SourceRange sourceRange);

    static Expression& forFixedArray(Compilation& compilation,
                                     const syntax::StructuredAssignmentPatternSyntax& syntax,
                                     const ASTContext& context, const Type& type,
                                     const Type& elementType, SourceRange sourceRange);

    static Expression& forDynamicArray(Compilation& compilation,
                                       const syntax::StructuredAssignmentPatternSyntax& syntax,
                                       const ASTContext& context, const Type& type,
                                       const Type& elementType, SourceRange sourceRange);

    static Expression& forAssociativeArray(Compilation& compilation,
                                           const syntax::StructuredAssignmentPatternSyntax& syntax,
                                           const ASTContext& context, const Type& type,
                                           const Type& elementType, SourceRange sourceRange);

    static bool isKind(ExpressionKind kind) {
        return kind == ExpressionKind::StructuredAssignmentPattern;
    }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto& setter : memberSetters)
            setter.expr->visit(visitor);
        for (auto& setter : typeSetters)
            setter.expr->visit(visitor);
        for (auto& setter : indexSetters) {
            setter.index->visit(visitor);
            setter.expr->visit(visitor);
        }
        if (defaultSetter)
            defaultSetter->visit(visitor);
    }
};

/// Represents a replicated assignment pattern expression.
class SLANG_EXPORT ReplicatedAssignmentPatternExpression : public AssignmentPatternExpressionBase {
public:
    ReplicatedAssignmentPatternExpression(const Type& type, const Expression& count,
                                          std::span<const Expression* const> elements,
                                          SourceRange sourceRange) :
        AssignmentPatternExpressionBase(ExpressionKind::ReplicatedAssignmentPattern, type, elements,
                                        sourceRange),
        count_(&count) {}

    /// @returns an expression indicating the number of times to replicate the pattern.
    const Expression& count() const { return *count_; }

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& forStruct(Compilation& compilation,
                                 const syntax::ReplicatedAssignmentPatternSyntax& syntax,
                                 const ASTContext& context, const Type& type,
                                 const Scope& structScope, SourceRange sourceRange);

    static Expression& forFixedArray(Compilation& compilation,
                                     const syntax::ReplicatedAssignmentPatternSyntax& syntax,
                                     const ASTContext& context, const Type& type,
                                     const Type& elementType, bitwidth_t numElements,
                                     SourceRange sourceRange);

    static Expression& forDynamicArray(Compilation& compilation,
                                       const syntax::ReplicatedAssignmentPatternSyntax& syntax,
                                       const ASTContext& context, const Type& type,
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
    static const Expression& bindReplCount(Compilation& comp,
                                           const syntax::ExpressionSyntax& syntax,
                                           const ASTContext& context, size_t& count);

    const Expression* count_;
};

} // namespace slang::ast
