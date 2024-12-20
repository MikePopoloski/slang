//------------------------------------------------------------------------------
//! @file Patterns.h
//! @brief AST definitions for pattern matching
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Expression.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Enum.h"

namespace slang::ast {

class FieldSymbol;
class PatternVarSymbol;
enum class CaseStatementCondition;

// clang-format off
#define PATTERN(x) \
    x(Invalid) \
    x(Wildcard) \
    x(Constant) \
    x(Variable) \
    x(Tagged) \
    x(Structure)
SLANG_ENUM(PatternKind, PATTERN)
#undef PATTERN
// clang-format on

/// Base class for "patterns", as used in pattern matching conditional
/// statements and expressions.
class SLANG_EXPORT Pattern {
public:
    /// The kind of pattern represented by this instance.
    PatternKind kind;

    /// The syntax node used to create the pattern, if it came from source code.
    const syntax::SyntaxNode* syntax = nullptr;

    /// The source range where this pattern occurs, if it came from source code.
    SourceRange sourceRange;

    Pattern(const Pattern&) = delete;
    Pattern& operator=(const Pattern&) = delete;

    /// Returns true if the pattern had an error and is therefore invalid.
    bool bad() const { return kind == PatternKind::Invalid; }

    static bool createPatternVars(const ASTContext& context,
                                  const syntax::PatternSyntax& patternSyntax,
                                  const syntax::ExpressionSyntax& condSyntax,
                                  SmallVector<const PatternVarSymbol*>& results);

    static bool createPatternVars(const ASTContext& context, const syntax::PatternSyntax& syntax,
                                  const Type& targetType,
                                  SmallVector<const PatternVarSymbol*>& results);

    static Pattern& bind(const ASTContext& context, const syntax::PatternSyntax& syntax,
                         const Type& targetType);

    /// Evaluates the pattern under the given evaluation context. Any errors that occur
    /// will be stored in the evaluation context instead of issued to the compilation.
    ConstantValue eval(EvalContext& context, const ConstantValue& value,
                       CaseStatementCondition conditionKind) const;

    /// @brief Casts this pattern to the given concrete derived type.
    ///
    /// Asserts that the type is appropriate given this pattern's kind.
    template<typename T>
    T& as() {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    /// @brief Casts this pattern to the given concrete derived type.
    ///
    /// Asserts that the type is appropriate given this pattern's kind.
    template<typename T>
    const T& as() const {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    /// @brief Tries to cast this pattern to the given concrete derived type.
    ///
    /// If the type is not appropriate given this pattern's kind, returns nullptr.
    template<typename T>
    T* as_if() {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<T*>(this);
    }

    /// @brief Tries to cast this pattern to the given concrete derived type.
    ///
    /// If the type is not appropriate given this pattern's kind, returns nullptr.
    template<typename T>
    const T* as_if() const {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<const T*>(this);
    }

    /// Visits this pattern's concrete derived type via the provided visitor object.
    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

protected:
    Pattern(PatternKind kind, SourceRange sourceRange) : kind(kind), sourceRange(sourceRange) {}

    static Pattern& badPattern(Compilation& compilation, const Pattern* child);

    static void createPlaceholderVars(const ASTContext& context,
                                      const syntax::PatternSyntax& syntax,
                                      SmallVector<const PatternVarSymbol*>& results);
};

/// @brief Represents an invalid pattern
///
/// Usually generated and inserted into an pattern tree due
/// to violation of language semantics or type checking.
class SLANG_EXPORT InvalidPattern : public Pattern {
public:
    /// A wrapped child pattern that is considered invalid.
    const Pattern* child;

    explicit InvalidPattern(const Pattern* child) :
        Pattern(PatternKind::Invalid, SourceRange()), child(child) {}

    ConstantValue evalImpl(EvalContext&, const ConstantValue&, CaseStatementCondition) const {
        return nullptr;
    }

    static bool isKind(PatternKind kind) { return kind == PatternKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;
};

/// Represents a wildcard pattern that matches anything.
class SLANG_EXPORT WildcardPattern : public Pattern {
public:
    explicit WildcardPattern(SourceRange sourceRange) :
        Pattern(PatternKind::Wildcard, sourceRange) {}

    static Pattern& fromSyntax(const syntax::WildcardPatternSyntax& syntax,
                               const ASTContext& context);

    ConstantValue evalImpl(EvalContext& context, const ConstantValue& value,
                           CaseStatementCondition conditionKind) const;

    static bool isKind(PatternKind kind) { return kind == PatternKind::Wildcard; }

    void serializeTo(ASTSerializer&) const {}
};

/// Reresents a pattern that matches a given constant expression.
class SLANG_EXPORT ConstantPattern : public Pattern {
public:
    /// The constant expression to match against.
    const Expression& expr;

    ConstantPattern(const Expression& expr, SourceRange sourceRange) :
        Pattern(PatternKind::Constant, sourceRange), expr(expr) {}

    static Pattern& fromSyntax(const syntax::ExpressionPatternSyntax& syntax,
                               const Type& targetType, const ASTContext& context);

    ConstantValue evalImpl(EvalContext& context, const ConstantValue& value,
                           CaseStatementCondition conditionKind) const;

    static bool isKind(PatternKind kind) { return kind == PatternKind::Constant; }

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
    }
};

/// Represents a pattern that stores its match in a pattern variable.
class SLANG_EXPORT VariablePattern : public Pattern {
public:
    /// The pattern variable that receives the result of the match.
    const PatternVarSymbol& variable;

    VariablePattern(const PatternVarSymbol& variable, SourceRange sourceRange) :
        Pattern(PatternKind::Variable, sourceRange), variable(variable) {}

    static Pattern& fromSyntax(const syntax::VariablePatternSyntax& syntax,
                               const ASTContext& context);

    ConstantValue evalImpl(EvalContext& context, const ConstantValue& value,
                           CaseStatementCondition conditionKind) const;

    static bool isKind(PatternKind kind) { return kind == PatternKind::Variable; }

    void serializeTo(ASTSerializer& serializer) const;
};

/// Represents a pattern that matches a member of a tagged union.
class SLANG_EXPORT TaggedPattern : public Pattern {
public:
    /// The union member to match.
    const FieldSymbol& member;

    /// The value to match against, or nullptr for void members.
    const Pattern* valuePattern;

    TaggedPattern(const FieldSymbol& member, const Pattern* valuePattern, SourceRange sourceRange) :
        Pattern(PatternKind::Tagged, sourceRange), member(member), valuePattern(valuePattern) {}

    static bool createVars(const ASTContext& context, const syntax::TaggedPatternSyntax& syntax,
                           const Type& targetType, SmallVector<const PatternVarSymbol*>& results);

    static Pattern& fromSyntax(const syntax::TaggedPatternSyntax& syntax, const Type& targetType,
                               const ASTContext& context);

    ConstantValue evalImpl(EvalContext& context, const ConstantValue& value,
                           CaseStatementCondition conditionKind) const;

    static bool isKind(PatternKind kind) { return kind == PatternKind::Tagged; }

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        if (valuePattern)
            valuePattern->visit(visitor);
    }
};

/// Represents a pattern that matches a structure.
class SLANG_EXPORT StructurePattern : public Pattern {
public:
    /// A pattern over a struct field.
    struct FieldPattern {
        /// The field symbol to match against.
        not_null<const FieldSymbol*> field;

        /// The pattern that applies to the field.
        not_null<const Pattern*> pattern;
    };

    /// The list of patterns to match against the struct.
    std::span<const FieldPattern> patterns;

    StructurePattern(std::span<const FieldPattern> patterns, SourceRange sourceRange) :
        Pattern(PatternKind::Structure, sourceRange), patterns(patterns) {}

    static bool createVars(const ASTContext& context, const syntax::StructurePatternSyntax& syntax,
                           const Type& targetType, SmallVector<const PatternVarSymbol*>& results);

    static Pattern& fromSyntax(const syntax::StructurePatternSyntax& syntax, const Type& targetType,
                               const ASTContext& context);

    ConstantValue evalImpl(EvalContext& context, const ConstantValue& value,
                           CaseStatementCondition conditionKind) const;

    static bool isKind(PatternKind kind) { return kind == PatternKind::Structure; }

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto& pattern : patterns)
            pattern.pattern->visit(visitor);
    }
};

} // namespace slang::ast
