//------------------------------------------------------------------------------
//! @file AssertionExpr.h
//! @brief Assertion expression creation and analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Expression.h"
#include "slang/ast/TimingControl.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Util.h"

namespace slang::ast {

// clang-format off
#define EXPR(x) \
    x(Invalid) \
    x(Simple) \
    x(SequenceConcat) \
    x(SequenceWithMatch) \
    x(Unary) \
    x(Binary) \
    x(FirstMatch) \
    x(Clocking) \
    x(StrongWeak) \
    x(Abort) \
    x(Conditional) \
    x(Case) \
    x(DisableIff)
SLANG_ENUM(AssertionExprKind, EXPR)
#undef EXPR

#define OP(x) \
    x(Not) \
    x(NextTime) \
    x(SNextTime) \
    x(Always) \
    x(SAlways) \
    x(Eventually) \
    x(SEventually)
SLANG_ENUM(UnaryAssertionOperator, OP)
#undef OP

#define OP(x) \
    x(And) \
    x(Or) \
    x(Intersect) \
    x(Throughout) \
    x(Within) \
    x(Iff) \
    x(Until) \
    x(SUntil) \
    x(UntilWith) \
    x(SUntilWith) \
    x(Implies) \
    x(OverlappedImplication) \
    x(NonOverlappedImplication) \
    x(OverlappedFollowedBy) \
    x(NonOverlappedFollowedBy)
SLANG_ENUM(BinaryAssertionOperator, OP)
#undef OP
// clang-format on

class ASTContext;
class CallExpression;

class SLANG_EXPORT AssertionExpr {
public:
    AssertionExprKind kind;

    const syntax::SyntaxNode* syntax = nullptr;

    void requireSequence(const ASTContext& context) const;
    void requireSequence(const ASTContext& context, DiagCode code) const;
    bool bad() const { return kind == AssertionExprKind::Invalid; }

    /// Returns true if this is a sequence expression that admits an empty match,
    /// and false otherwise.
    bool admitsEmpty() const;

    static const AssertionExpr& bind(const syntax::SequenceExprSyntax& syntax,
                                     const ASTContext& context, bool allowDisable = false);

    static const AssertionExpr& bind(const syntax::PropertyExprSyntax& syntax,
                                     const ASTContext& context, bool allowDisable = false,
                                     bool allowSeqAdmitEmpty = false);

    static const AssertionExpr& bind(const syntax::PropertySpecSyntax& syntax,
                                     const ASTContext& context);

    static bool checkAssertionCall(const CallExpression& call, const ASTContext& context,
                                   DiagCode outArgCode, DiagCode refArgCode,
                                   std::optional<DiagCode> sysTaskCode, SourceRange range);

    static void checkSampledValueExpr(const Expression& expr, const ASTContext& context,
                                      bool isFutureGlobal, DiagCode localVarCode,
                                      DiagCode matchedCode);

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
    explicit AssertionExpr(AssertionExprKind kind) : kind(kind) {}

    static AssertionExpr& badExpr(Compilation& compilation, const AssertionExpr* expr);
};

class SLANG_EXPORT InvalidAssertionExpr : public AssertionExpr {
public:
    const AssertionExpr* child;

    explicit InvalidAssertionExpr(const AssertionExpr* child) :
        AssertionExpr(AssertionExprKind::Invalid), child(child) {}

    bool admitsEmptyImpl() const { return false; }

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;
};

/// Represents a range of potential sequence matches.
struct SequenceRange {
    /// The minimum length of the range.
    uint32_t min = 1;

    /// The maximum length of the range. If unset, the maximum is unbounded.
    std::optional<uint32_t> max;

    static SequenceRange fromSyntax(const syntax::SelectorSyntax& syntax, const ASTContext& context,
                                    bool allowUnbounded);
    static SequenceRange fromSyntax(const syntax::RangeSelectSyntax& syntax,
                                    const ASTContext& context, bool allowUnbounded);

    void serializeTo(ASTSerializer& serializer) const;
};

/// Encodes a repetition of some sub-sequence.
struct SequenceRepetition {
    /// The kind of repetition.
    enum Kind {
        /// A repetition with a match on each consecutive cycle.
        Consecutive,

        /// A nonconsecutive repetition that does not necessarily end
        /// at the last iterative match.
        Nonconsecutive,

        /// A nonconsecutive repetition which ends at the last iterative match.
        GoTo
    } kind = Consecutive;

    /// The range of cycles over which to repeat.
    SequenceRange range;

    SequenceRepetition(const syntax::SequenceRepetitionSyntax& syntax, const ASTContext& context);

    enum class AdmitsEmpty { Yes, No, Depends };
    AdmitsEmpty admitsEmpty() const;

    void serializeTo(ASTSerializer& serializer) const;
};

/// Represents an assertion expression defined as a simple regular expression.
class SLANG_EXPORT SimpleAssertionExpr : public AssertionExpr {
public:
    const Expression& expr;
    std::optional<SequenceRepetition> repetition;

    SimpleAssertionExpr(const Expression& expr, std::optional<SequenceRepetition> repetition) :
        AssertionExpr(AssertionExprKind::Simple), expr(expr), repetition(repetition) {}

    void requireSequence(const ASTContext& context, DiagCode code) const;
    bool admitsEmptyImpl() const;

    static AssertionExpr& fromSyntax(const syntax::SimpleSequenceExprSyntax& syntax,
                                     const ASTContext& context, bool allowDisable);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Simple; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return expr.visit(visitor);
    }
};

/// Represents an assertion expression defined as a delayed concatenation of other expressions.
class SLANG_EXPORT SequenceConcatExpr : public AssertionExpr {
public:
    struct Element {
        SequenceRange delay;
        not_null<const AssertionExpr*> sequence;
    };

    std::span<const Element> elements;

    explicit SequenceConcatExpr(std::span<const Element> elements) :
        AssertionExpr(AssertionExprKind::SequenceConcat), elements(elements) {}

    bool admitsEmptyImpl() const;

    static AssertionExpr& fromSyntax(const syntax::DelayedSequenceExprSyntax& syntax,
                                     const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::SequenceConcat; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto& elem : elements)
            elem.sequence->visit(visitor);
    }
};

/// Represents a sequence expression along with a list of actions to perform upon matching
/// and/or instructions for repetition.
class SLANG_EXPORT SequenceWithMatchExpr : public AssertionExpr {
public:
    const AssertionExpr& expr;
    std::optional<SequenceRepetition> repetition;
    std::span<const Expression* const> matchItems;

    SequenceWithMatchExpr(const AssertionExpr& expr, std::optional<SequenceRepetition> repetition,
                          std::span<const Expression* const> matchItems) :
        AssertionExpr(AssertionExprKind::SequenceWithMatch),
        expr(expr), repetition(repetition), matchItems(matchItems) {}

    bool admitsEmptyImpl() const;

    static AssertionExpr& fromSyntax(const syntax::ParenthesizedSequenceExprSyntax& syntax,
                                     const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) {
        return kind == AssertionExprKind::SequenceWithMatch;
    }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
        for (auto item : matchItems)
            item->visit(visitor);
    }
};

/// Represents a unary operator in a property expression.
class SLANG_EXPORT UnaryAssertionExpr : public AssertionExpr {
public:
    UnaryAssertionOperator op;
    const AssertionExpr& expr;
    std::optional<SequenceRange> range;

    UnaryAssertionExpr(UnaryAssertionOperator op, const AssertionExpr& expr,
                       std::optional<SequenceRange> range) :
        AssertionExpr(AssertionExprKind::Unary),
        op(op), expr(expr), range(range) {}

    bool admitsEmptyImpl() const { return false; }

    static AssertionExpr& fromSyntax(const syntax::UnaryPropertyExprSyntax& syntax,
                                     const ASTContext& context);

    static AssertionExpr& fromSyntax(const syntax::UnarySelectPropertyExprSyntax& syntax,
                                     const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Unary; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return expr.visit(visitor);
    }
};

/// Represents a binary operator in a sequence or property expression.
class SLANG_EXPORT BinaryAssertionExpr : public AssertionExpr {
public:
    BinaryAssertionOperator op;
    const AssertionExpr& left;
    const AssertionExpr& right;

    BinaryAssertionExpr(BinaryAssertionOperator op, const AssertionExpr& left,
                        const AssertionExpr& right) :
        AssertionExpr(AssertionExprKind::Binary),
        op(op), left(left), right(right) {}

    void requireSequence(const ASTContext& context, DiagCode code) const;
    bool admitsEmptyImpl() const;

    static AssertionExpr& fromSyntax(const syntax::BinarySequenceExprSyntax& syntax,
                                     const ASTContext& context);

    static AssertionExpr& fromSyntax(const syntax::BinaryPropertyExprSyntax& syntax,
                                     const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Binary; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        left.visit(visitor);
        right.visit(visitor);
    }
};

/// Represents a first_match operator in a sequence expression.
class SLANG_EXPORT FirstMatchAssertionExpr : public AssertionExpr {
public:
    const AssertionExpr& seq;
    std::span<const Expression* const> matchItems;

    FirstMatchAssertionExpr(const AssertionExpr& seq,
                            std::span<const Expression* const> matchItems) :
        AssertionExpr(AssertionExprKind::FirstMatch),
        seq(seq), matchItems(matchItems) {}

    bool admitsEmptyImpl() const;

    static AssertionExpr& fromSyntax(const syntax::FirstMatchSequenceExprSyntax& syntax,
                                     const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::FirstMatch; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        seq.visit(visitor);
        for (auto item : matchItems)
            item->visit(visitor);
    }
};

/// Represents an assertion expression with attached clocking control.
class SLANG_EXPORT ClockingAssertionExpr : public AssertionExpr {
public:
    const TimingControl& clocking;
    const AssertionExpr& expr;

    ClockingAssertionExpr(const TimingControl& clocking, const AssertionExpr& expr) :
        AssertionExpr(AssertionExprKind::Clocking), clocking(clocking), expr(expr) {}

    bool admitsEmptyImpl() const;

    static AssertionExpr& fromSyntax(const syntax::ClockingSequenceExprSyntax& syntax,
                                     const ASTContext& context);

    static AssertionExpr& fromSyntax(const syntax::ClockingPropertyExprSyntax& syntax,
                                     const ASTContext& context);

    static AssertionExpr& fromSyntax(const syntax::SignalEventExpressionSyntax& syntax,
                                     const ASTContext& context);

    static AssertionExpr& fromSyntax(const syntax::TimingControlSyntax& syntax,
                                     const AssertionExpr& expr, const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Clocking; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        clocking.visit(visitor);
        expr.visit(visitor);
    }
};

/// Represents a strong or weak operator in a property expression.
class SLANG_EXPORT StrongWeakAssertionExpr : public AssertionExpr {
public:
    const AssertionExpr& expr;
    enum Strength { Strong, Weak } strength;

    StrongWeakAssertionExpr(const AssertionExpr& expr, Strength strength) :
        AssertionExpr(AssertionExprKind::StrongWeak), expr(expr), strength(strength) {}

    bool admitsEmptyImpl() const { return false; }

    static AssertionExpr& fromSyntax(const syntax::StrongWeakPropertyExprSyntax& syntax,
                                     const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::StrongWeak; }

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return expr.visit(visitor);
    }
};

/// Represents an abort (accept_on / reject_on) property expression.
class SLANG_EXPORT AbortAssertionExpr : public AssertionExpr {
public:
    const Expression& condition;
    const AssertionExpr& expr;
    enum Action { Accept, Reject } action;
    bool isSync;

    AbortAssertionExpr(const Expression& condition, const AssertionExpr& expr, Action action,
                       bool isSync) :
        AssertionExpr(AssertionExprKind::Abort),
        condition(condition), expr(expr), action(action), isSync(isSync) {}

    bool admitsEmptyImpl() const { return false; }

    static AssertionExpr& fromSyntax(const syntax::AcceptOnPropertyExprSyntax& syntax,
                                     const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Abort; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        condition.visit(visitor);
        expr.visit(visitor);
    }
};

/// Represents a conditional operator in a property expression.
class SLANG_EXPORT ConditionalAssertionExpr : public AssertionExpr {
public:
    const Expression& condition;
    const AssertionExpr& ifExpr;
    const AssertionExpr* elseExpr;

    ConditionalAssertionExpr(const Expression& condition, const AssertionExpr& ifExpr,
                             const AssertionExpr* elseExpr) :
        AssertionExpr(AssertionExprKind::Conditional),
        condition(condition), ifExpr(ifExpr), elseExpr(elseExpr) {}

    bool admitsEmptyImpl() const { return false; }

    static AssertionExpr& fromSyntax(const syntax::ConditionalPropertyExprSyntax& syntax,
                                     const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Conditional; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        condition.visit(visitor);
        ifExpr.visit(visitor);
        if (elseExpr)
            elseExpr->visit(visitor);
    }
};

/// Represents a case operator in a property expression.
class SLANG_EXPORT CaseAssertionExpr : public AssertionExpr {
public:
    struct ItemGroup {
        std::span<const Expression* const> expressions;
        not_null<const AssertionExpr*> body;
    };

    const Expression& expr;
    std::span<const ItemGroup> items;
    const AssertionExpr* defaultCase = nullptr;

    CaseAssertionExpr(const Expression& expr, std::span<const ItemGroup> items,
                      const AssertionExpr* defaultCase) :
        AssertionExpr(AssertionExprKind::Case),
        expr(expr), items(items), defaultCase(defaultCase) {}

    bool admitsEmptyImpl() const { return false; }

    static AssertionExpr& fromSyntax(const syntax::CasePropertyExprSyntax& syntax,
                                     const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Case; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
        for (auto& item : items) {
            for (auto e : item.expressions)
                e->visit(visitor);
            item.body->visit(visitor);
        }

        if (defaultCase)
            defaultCase->visit(visitor);
    }
};

/// Represents a disable iff condition in a property spec.
class SLANG_EXPORT DisableIffAssertionExpr : public AssertionExpr {
public:
    const Expression& condition;
    const AssertionExpr& expr;

    DisableIffAssertionExpr(const Expression& condition, const AssertionExpr& expr) :
        AssertionExpr(AssertionExprKind::DisableIff), condition(condition), expr(expr) {}

    bool admitsEmptyImpl() const { return false; }

    static AssertionExpr& fromSyntax(const syntax::DisableIffSyntax& syntax,
                                     const AssertionExpr& expr, const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::DisableIff; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        condition.visit(visitor);
        expr.visit(visitor);
    }
};

} // namespace slang::ast
