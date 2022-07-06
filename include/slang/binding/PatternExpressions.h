//------------------------------------------------------------------------------
//! @file PatternExpressions.h
//! @brief Definitions for pattern expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"
#include "slang/util/Enum.h"
#include "slang/util/StackContainer.h"

namespace slang {

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

class PatternVarSymbol;

// clang-format off
#define PATTERN(x) \
    x(Invalid) \
    x(Wildcard) \
    x(Constant) \
    x(Variable) \
    x(Tagged) \
    x(Ordered) \
    x(Structured)
ENUM(PatternKind, PATTERN)
#undef PATTERN
// clang-format on

struct PatternSyntax;

/// Base class for "patterns", as used in pattern matching conditional
/// statements and expressions.
class Pattern {
public:
    /// The kind of pattern represented by this instance.
    PatternKind kind;

    /// The syntax node used to create the pattern, if it came from source code.
    const SyntaxNode* syntax = nullptr;

    /// The source range where this pattern occurs, if it came from source code.
    SourceRange sourceRange;

    /// Returns true if the pattern had an error and is therefore invalid.
    bool bad() const { return kind == PatternKind::Invalid; }

    using VarMap = SmallMap<string_view, const PatternVarSymbol*, 4>;

    static Pattern& bind(const PatternSyntax& syntax, const Type& targetType, VarMap& varMap,
                         BindContext& context);

    template<typename T>
    T& as() {
        ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    template<typename T>
    const T& as() const {
        ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

protected:
    Pattern(PatternKind kind, SourceRange sourceRange) : kind(kind), sourceRange(sourceRange) {}

    static Pattern& badPattern(Compilation& compilation, const Pattern* child);
};

class InvalidPattern : public Pattern {
public:
    const Pattern* child;

    explicit InvalidPattern(const Pattern* child) :
        Pattern(PatternKind::Invalid, SourceRange()), child(child) {}

    static bool isKind(PatternKind kind) { return kind == PatternKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;
};

struct WildcardPatternSyntax;

class WildcardPattern : public Pattern {
public:
    explicit WildcardPattern(SourceRange sourceRange) :
        Pattern(PatternKind::Wildcard, sourceRange) {}

    static Pattern& fromSyntax(const WildcardPatternSyntax& syntax, const BindContext& context);

    static bool isKind(PatternKind kind) { return kind == PatternKind::Wildcard; }

    void serializeTo(ASTSerializer&) const {}
};

struct ExpressionPatternSyntax;

class ConstantPattern : public Pattern {
public:
    const Expression& expr;

    ConstantPattern(const Expression& expr, SourceRange sourceRange) :
        Pattern(PatternKind::Constant, sourceRange), expr(expr) {}

    static Pattern& fromSyntax(const ExpressionPatternSyntax& syntax, const Type& targetType,
                               const BindContext& context);

    static bool isKind(PatternKind kind) { return kind == PatternKind::Constant; }

    void serializeTo(ASTSerializer& serializer) const;
};

struct VariablePatternSyntax;

class VariablePattern : public Pattern {
public:
    const PatternVarSymbol& variable;

    VariablePattern(const PatternVarSymbol& variable, SourceRange sourceRange) :
        Pattern(PatternKind::Variable, sourceRange), variable(variable) {}

    static Pattern& fromSyntax(const VariablePatternSyntax& syntax, const Type& targetType,
                               VarMap& varMap, BindContext& context);

    static bool isKind(PatternKind kind) { return kind == PatternKind::Variable; }

    void serializeTo(ASTSerializer& serializer) const;
};

} // namespace slang
