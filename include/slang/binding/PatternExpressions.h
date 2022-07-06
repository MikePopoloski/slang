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
