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

    void toJson(json& j) const;

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

    static Expression& forArray(Compilation& compilation,
                                const SimpleAssignmentPatternSyntax& syntax,
                                const BindContext& context, const Type& type,
                                const Type& elementType, bitwidth_t numElements,
                                SourceRange sourceRange);

    static bool isKind(ExpressionKind kind) {
        return kind == ExpressionKind::SimpleAssignmentPattern;
    }
};

struct StructuredAssignmentPatternSyntax;

/// Represents an assignment pattern expression.
class StructuredAssignmentPatternExpression : public AssignmentPatternExpressionBase {
public:
    struct MemberSetter {
        const Symbol* member = nullptr;
        const Expression* expr = nullptr;
    };

    struct TypeSetter {
        const Type* type = nullptr;
        const Expression* expr = nullptr;
    };

    struct IndexSetter {
        const Expression* index = nullptr;
        const Expression* expr = nullptr;
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

    void toJson(json& j) const;

    static Expression& forStruct(Compilation& compilation,
                                 const StructuredAssignmentPatternSyntax& syntax,
                                 const BindContext& context, const Type& type,
                                 const Scope& structScope, SourceRange sourceRange);

    static Expression& forArray(Compilation& compilation,
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

    void toJson(json& j) const;

    static Expression& forStruct(Compilation& compilation,
                                 const ReplicatedAssignmentPatternSyntax& syntax,
                                 const BindContext& context, const Type& type,
                                 const Scope& structScope, SourceRange sourceRange);

    static Expression& forArray(Compilation& compilation,
                                const ReplicatedAssignmentPatternSyntax& syntax,
                                const BindContext& context, const Type& type,
                                const Type& elementType, bitwidth_t numElements,
                                SourceRange sourceRange);

    static bool isKind(ExpressionKind kind) {
        return kind == ExpressionKind::ReplicatedAssignmentPattern;
    }

private:
    static const Expression& bindReplCount(Compilation& comp, const ExpressionSyntax& syntax,
                                           const BindContext& context, size_t& count);

    const Expression* count_;
};

} // namespace slang