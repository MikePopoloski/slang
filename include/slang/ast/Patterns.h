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

    using VarMap = SmallMap<std::string_view, const PatternVarSymbol*, 4>;

    static Pattern& bind(const syntax::PatternSyntax& syntax, const Type& targetType,
                         VarMap& varMap, ASTContext& context);

    /// Evaluates the pattern under the given evaluation context. Any errors that occur
    /// will be stored in the evaluation context instead of issued to the compilation.
    ConstantValue eval(EvalContext& context, const ConstantValue& value,
                       CaseStatementCondition conditionKind) const;

    template<typename T>
    T& as() {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    template<typename T>
    const T& as() const {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    template<typename T>
    T* as_if() {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<T*>(this);
    }

    template<typename T>
    const T* as_if() const {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<const T*>(this);
    }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

protected:
    Pattern(PatternKind kind, SourceRange sourceRange) : kind(kind), sourceRange(sourceRange) {}

    static Pattern& badPattern(Compilation& compilation, const Pattern* child);
    static void createPlaceholderVars(const syntax::PatternSyntax& syntax, VarMap& varMap,
                                      ASTContext& context);
};

class SLANG_EXPORT InvalidPattern : public Pattern {
public:
    const Pattern* child;

    explicit InvalidPattern(const Pattern* child) :
        Pattern(PatternKind::Invalid, SourceRange()), child(child) {}

    ConstantValue evalImpl(EvalContext&, const ConstantValue&, CaseStatementCondition) const {
        return nullptr;
    }

    static bool isKind(PatternKind kind) { return kind == PatternKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;
};

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

class SLANG_EXPORT ConstantPattern : public Pattern {
public:
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

class SLANG_EXPORT VariablePattern : public Pattern {
public:
    const PatternVarSymbol& variable;

    VariablePattern(const PatternVarSymbol& variable, SourceRange sourceRange) :
        Pattern(PatternKind::Variable, sourceRange), variable(variable) {}

    static Pattern& fromSyntax(const syntax::VariablePatternSyntax& syntax, const Type& targetType,
                               VarMap& varMap, ASTContext& context);

    ConstantValue evalImpl(EvalContext& context, const ConstantValue& value,
                           CaseStatementCondition conditionKind) const;

    static bool isKind(PatternKind kind) { return kind == PatternKind::Variable; }

    void serializeTo(ASTSerializer& serializer) const;
};

class SLANG_EXPORT TaggedPattern : public Pattern {
public:
    const FieldSymbol& member;
    const Pattern* valuePattern;

    TaggedPattern(const FieldSymbol& member, const Pattern* valuePattern, SourceRange sourceRange) :
        Pattern(PatternKind::Tagged, sourceRange), member(member), valuePattern(valuePattern) {}

    static Pattern& fromSyntax(const syntax::TaggedPatternSyntax& syntax, const Type& targetType,
                               VarMap& varMap, ASTContext& context);

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

class SLANG_EXPORT StructurePattern : public Pattern {
public:
    struct FieldPattern {
        not_null<const FieldSymbol*> field;
        not_null<const Pattern*> pattern;
    };

    std::span<const FieldPattern> patterns;

    StructurePattern(std::span<const FieldPattern> patterns, SourceRange sourceRange) :
        Pattern(PatternKind::Structure, sourceRange), patterns(patterns) {}

    static Pattern& fromSyntax(const syntax::StructurePatternSyntax& syntax, const Type& targetType,
                               VarMap& varMap, ASTContext& context);

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
