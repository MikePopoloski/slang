//------------------------------------------------------------------------------
//! @file PatternExpressions.h
//! @brief Definitions for pattern expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"

namespace slang {

/// Base class for assignment pattern expressions.
class AssignmentPatternExpressionBase : public Expression {
public:
    span<const Expression* const> elements() const { return elements_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext&) const;

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
