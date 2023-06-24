//------------------------------------------------------------------------------
//! @file Constraints.h
//! @brief Constraint creation and analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Statements.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Util.h"

namespace slang::ast {

class ASTSerializer;

// clang-format off
#define CONSTRAINT(x) \
    x(Invalid) \
    x(List) \
    x(Expression) \
    x(Implication) \
    x(Conditional) \
    x(Uniqueness) \
    x(DisableSoft) \
    x(SolveBefore) \
    x(Foreach)
SLANG_ENUM(ConstraintKind, CONSTRAINT)
#undef CONSTRAINT
// clang-format on

class ASTContext;

class SLANG_EXPORT Constraint {
public:
    ConstraintKind kind;

    const syntax::ConstraintItemSyntax* syntax = nullptr;

    Constraint(const Constraint&) = delete;
    Constraint& operator=(const Constraint&) = delete;

    bool bad() const { return kind == ConstraintKind::Invalid; }

    static const Constraint& bind(const syntax::ConstraintItemSyntax& syntax,
                                  const ASTContext& context);

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
    explicit Constraint(ConstraintKind kind) : kind(kind) {}

    static Constraint& badConstraint(Compilation& compilation, const Constraint* ctrl);
};

class SLANG_EXPORT InvalidConstraint : public Constraint {
public:
    const Constraint* child;

    explicit InvalidConstraint(const Constraint* child) :
        Constraint(ConstraintKind::Invalid), child(child) {}

    static bool isKind(ConstraintKind kind) { return kind == ConstraintKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;
};

/// Represents a list of constraints.
class SLANG_EXPORT ConstraintList : public Constraint {
public:
    std::span<const Constraint* const> list;

    explicit ConstraintList(std::span<const Constraint* const> list) :
        Constraint(ConstraintKind::List), list(list) {}

    static Constraint& fromSyntax(const syntax::ConstraintBlockSyntax& syntax,
                                  const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ConstraintKind kind) { return kind == ConstraintKind::List; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto item : list)
            item->visit(visitor);
    }
};

/// Represents a constraint defined by a logical expression.
class SLANG_EXPORT ExpressionConstraint : public Constraint {
public:
    const Expression& expr;
    bool isSoft;

    ExpressionConstraint(const Expression& expr, bool isSoft) :
        Constraint(ConstraintKind::Expression), expr(expr), isSoft(isSoft) {}

    static Constraint& fromSyntax(const syntax::ExpressionConstraintSyntax& syntax,
                                  const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ConstraintKind kind) { return kind == ConstraintKind::Expression; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return expr.visit(visitor);
    }
};

/// Represents a constraint defined by an implication.
class SLANG_EXPORT ImplicationConstraint : public Constraint {
public:
    const Expression& predicate;
    const Constraint& body;

    ImplicationConstraint(const Expression& predicate, const Constraint& body) :
        Constraint(ConstraintKind::Implication), predicate(predicate), body(body) {}

    static Constraint& fromSyntax(const syntax::ImplicationConstraintSyntax& syntax,
                                  const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ConstraintKind kind) { return kind == ConstraintKind::Implication; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        predicate.visit(visitor);
        body.visit(visitor);
    }
};

/// Represents a constraint defined by an if-else condition.
class SLANG_EXPORT ConditionalConstraint : public Constraint {
public:
    const Expression& predicate;
    const Constraint& ifBody;
    const Constraint* elseBody;

    ConditionalConstraint(const Expression& predicate, const Constraint& ifBody,
                          const Constraint* elseBody) :
        Constraint(ConstraintKind::Conditional),
        predicate(predicate), ifBody(ifBody), elseBody(elseBody) {}

    static Constraint& fromSyntax(const syntax::ConditionalConstraintSyntax& syntax,
                                  const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ConstraintKind kind) { return kind == ConstraintKind::Conditional; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        predicate.visit(visitor);
        ifBody.visit(visitor);
        if (elseBody)
            elseBody->visit(visitor);
    }
};

/// Represents a constraint that enforces uniqueness of variables.
class SLANG_EXPORT UniquenessConstraint : public Constraint {
public:
    std::span<const Expression* const> items;

    explicit UniquenessConstraint(std::span<const Expression* const> items) :
        Constraint(ConstraintKind::Uniqueness), items(items) {}

    static Constraint& fromSyntax(const syntax::UniquenessConstraintSyntax& syntax,
                                  const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ConstraintKind kind) { return kind == ConstraintKind::Uniqueness; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto item : items)
            item->visit(visitor);
    }
};

/// Represents a constraint that disables a soft random variable.
class SLANG_EXPORT DisableSoftConstraint : public Constraint {
public:
    const Expression& target;

    explicit DisableSoftConstraint(const Expression& target) :
        Constraint(ConstraintKind::DisableSoft), target(target) {}

    static Constraint& fromSyntax(const syntax::DisableConstraintSyntax& syntax,
                                  const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ConstraintKind kind) { return kind == ConstraintKind::DisableSoft; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return target.visit(visitor);
    }
};

/// Represents a constraint that enforces ordering of solving variables.
class SLANG_EXPORT SolveBeforeConstraint : public Constraint {
public:
    std::span<const Expression* const> solve;
    std::span<const Expression* const> before;

    SolveBeforeConstraint(std::span<const Expression* const> solve,
                          std::span<const Expression* const> before) :
        Constraint(ConstraintKind::SolveBefore),
        solve(solve), before(before) {}

    static Constraint& fromSyntax(const syntax::SolveBeforeConstraintSyntax& syntax,
                                  const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ConstraintKind kind) { return kind == ConstraintKind::SolveBefore; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto item : solve)
            item->visit(visitor);
        for (auto item : before)
            item->visit(visitor);
    }
};

/// Represents a constraint that iterates over the elements of an array.
class SLANG_EXPORT ForeachConstraint : public Constraint {
public:
    const Expression& arrayRef;
    std::span<const ForeachLoopStatement::LoopDim> loopDims;
    const Constraint& body;

    ForeachConstraint(const Expression& arrayRef,
                      std::span<const ForeachLoopStatement::LoopDim> loopDims,
                      const Constraint& body) :
        Constraint(ConstraintKind::Foreach),
        arrayRef(arrayRef), loopDims(loopDims), body(body) {}

    static Constraint& fromSyntax(const syntax::LoopConstraintSyntax& syntax,
                                  const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ConstraintKind kind) { return kind == ConstraintKind::Foreach; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        arrayRef.visit(visitor);
        body.visit(visitor);
    }
};

} // namespace slang::ast
