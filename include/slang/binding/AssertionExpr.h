//------------------------------------------------------------------------------
//! @file AssertionExpr.h
//! @brief Assertion expression creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/ASTSerializer.h"
#include "slang/util/Util.h"

namespace slang {

// clang-format off
#define EXPR(x) \
    x(Invalid) \
    x(Simple) \
    x(SequenceConcat) \
    x(Unary) \
    x(Binary) \
    x(FirstMatch) \
    x(Clocking) \
    x(StrongWeak) \
    x(Abort) \
    x(Conditional) \
    x(Case) \
    x(Instance)
ENUM(AssertionExprKind, EXPR);
#undef EXPR

#define OP(x) \
    x(Not) \
    x(NextTime) \
    x(SNextTime) \
    x(Always) \
    x(SAlways) \
    x(Eventually) \
    x(SEventually)
ENUM(UnaryAssertionOperator, OP);
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
ENUM(BinaryAssertionOperator, OP);
#undef OP
// clang-format on

class BindContext;
class Compilation;
class SyntaxNode;
class TimingControl;
struct PropertyExprSyntax;
struct SequenceExprSyntax;

class AssertionExpr {
public:
    AssertionExprKind kind;

    const SyntaxNode* syntax = nullptr;

    bool bad() const { return kind == AssertionExprKind::Invalid; }

    static const AssertionExpr& bind(const SequenceExprSyntax& syntax, const BindContext& context);
    static const AssertionExpr& bind(const PropertyExprSyntax& syntax, const BindContext& context);

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
    explicit AssertionExpr(AssertionExprKind kind) : kind(kind) {}

    static AssertionExpr& badExpr(Compilation& compilation, const AssertionExpr* expr);
};

class InvalidAssertionExpr : public AssertionExpr {
public:
    const AssertionExpr* child;

    explicit InvalidAssertionExpr(const AssertionExpr* child) :
        AssertionExpr(AssertionExprKind::Invalid), child(child) {}

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;
};

struct RangeSelectSyntax;
struct SelectorSyntax;
struct SequenceRepetitionSyntax;

/// Represents a range of potential sequence matches.
struct SequenceRange {
    /// The minimum length of the range.
    uint32_t min = 0;

    /// The maximum length of the range. If unset, the maximum is unbounded.
    optional<uint32_t> max;

    static SequenceRange fromSyntax(const SelectorSyntax& syntax, const BindContext& context,
                                    bool allowUnbounded);
    static SequenceRange fromSyntax(const RangeSelectSyntax& syntax, const BindContext& context,
                                    bool allowUnbounded);

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

    SequenceRepetition(const SequenceRepetitionSyntax& syntax, const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;
};

struct SimpleSequenceExprSyntax;

/// Represents an assertion expression defined as a simple regular expression.
class SimpleAssertionExpr : public AssertionExpr {
public:
    const Expression& expr;
    optional<SequenceRepetition> repetition;

    SimpleAssertionExpr(const Expression& expr, optional<SequenceRepetition> repetition) :
        AssertionExpr(AssertionExprKind::Simple), expr(expr), repetition(repetition) {}

    static AssertionExpr& fromSyntax(const SimpleSequenceExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Simple; }
};

struct DelayedSequenceExprSyntax;

/// Represents an assertion expression defined as a delayed concatenation of other expressions.
class SequenceConcatExpr : public AssertionExpr {
public:
    struct Element {
        SequenceRange delay;
        not_null<const AssertionExpr*> sequence;
    };

    span<const Element> elements;

    explicit SequenceConcatExpr(span<const Element> elements) :
        AssertionExpr(AssertionExprKind::SequenceConcat), elements(elements) {}

    static AssertionExpr& fromSyntax(const DelayedSequenceExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::SequenceConcat; }
};

struct UnaryPropertyExprSyntax;
struct UnarySelectPropertyExprSyntax;

/// Represents a unary operator in a property expression.
class UnaryAssertionExpr : public AssertionExpr {
public:
    UnaryAssertionOperator op;
    const AssertionExpr& expr;
    optional<SequenceRange> range;

    UnaryAssertionExpr(UnaryAssertionOperator op, const AssertionExpr& expr,
                       optional<SequenceRange> range) :
        AssertionExpr(AssertionExprKind::Unary),
        op(op), expr(expr), range(range) {}

    static AssertionExpr& fromSyntax(const UnaryPropertyExprSyntax& syntax,
                                     const BindContext& context);

    static AssertionExpr& fromSyntax(const UnarySelectPropertyExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Unary; }
};

struct BinarySequenceExprSyntax;
struct BinaryPropertyExprSyntax;

/// Represents a binary operator in a sequence or property expression.
class BinaryAssertionExpr : public AssertionExpr {
public:
    BinaryAssertionOperator op;
    const AssertionExpr& left;
    const AssertionExpr& right;

    BinaryAssertionExpr(BinaryAssertionOperator op, const AssertionExpr& left,
                        const AssertionExpr& right) :
        AssertionExpr(AssertionExprKind::Binary),
        op(op), left(left), right(right) {}

    static AssertionExpr& fromSyntax(const BinarySequenceExprSyntax& syntax,
                                     const BindContext& context);

    static AssertionExpr& fromSyntax(const BinaryPropertyExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Binary; }
};

struct FirstMatchSequenceExprSyntax;

/// Represents a first_match operator in a sequence expression.
class FirstMatchAssertionExpr : public AssertionExpr {
public:
    const AssertionExpr& seq;

    FirstMatchAssertionExpr(const AssertionExpr& seq) :
        AssertionExpr(AssertionExprKind::FirstMatch), seq(seq) {}

    static AssertionExpr& fromSyntax(const FirstMatchSequenceExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::FirstMatch; }
};

struct ClockingSequenceExprSyntax;
struct ClockingPropertyExprSyntax;

/// Represents an assertion expression with attached clocking control.
class ClockingAssertionExpr : public AssertionExpr {
public:
    const TimingControl& clocking;
    const AssertionExpr& expr;

    ClockingAssertionExpr(const TimingControl& clocking, const AssertionExpr& expr) :
        AssertionExpr(AssertionExprKind::Clocking), clocking(clocking), expr(expr) {}

    static AssertionExpr& fromSyntax(const ClockingSequenceExprSyntax& syntax,
                                     const BindContext& context);

    static AssertionExpr& fromSyntax(const ClockingPropertyExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Clocking; }
};

struct StrongWeakPropertyExprSyntax;

/// Represents a strong or weak operator in a property expression.
class StrongWeakAssertionExpr : public AssertionExpr {
public:
    const AssertionExpr& expr;
    enum Strength { Strong, Weak } strength;

    StrongWeakAssertionExpr(const AssertionExpr& expr, Strength strength) :
        AssertionExpr(AssertionExprKind::StrongWeak), expr(expr), strength(strength) {}

    static AssertionExpr& fromSyntax(const StrongWeakPropertyExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::StrongWeak; }
};

struct AcceptOnPropertyExprSyntax;

/// Represents an abort (accept_on / reject_on) property expression.
class AbortAssertionExpr : public AssertionExpr {
public:
    const Expression& condition;
    const AssertionExpr& expr;
    enum Action { Accept, Reject } action;
    bool isSync;

    AbortAssertionExpr(const Expression& condition, const AssertionExpr& expr, Action action,
                       bool isSync) :
        AssertionExpr(AssertionExprKind::Abort),
        condition(condition), expr(expr), action(action), isSync(isSync) {}

    static AssertionExpr& fromSyntax(const AcceptOnPropertyExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Abort; }
};

struct ConditionalPropertyExprSyntax;

/// Represents a conditional operator in a property expression.
class ConditionalAssertionExpr : public AssertionExpr {
public:
    const Expression& condition;
    const AssertionExpr& ifExpr;
    const AssertionExpr* elseExpr;

    ConditionalAssertionExpr(const Expression& condition, const AssertionExpr& ifExpr,
                             const AssertionExpr* elseExpr) :
        AssertionExpr(AssertionExprKind::Conditional),
        condition(condition), ifExpr(ifExpr), elseExpr(elseExpr) {}

    static AssertionExpr& fromSyntax(const ConditionalPropertyExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Conditional; }
};

struct CasePropertyExprSyntax;

/// Represents a case operator in a property expression.
class CaseAssertionExpr : public AssertionExpr {
public:
    struct ItemGroup {
        span<const Expression* const> expressions;
        not_null<const AssertionExpr*> body;
    };

    const Expression& expr;
    span<const ItemGroup> items;
    const AssertionExpr* defaultCase = nullptr;

    CaseAssertionExpr(const Expression& expr, span<const ItemGroup> items,
                      const AssertionExpr* defaultCase) :
        AssertionExpr(AssertionExprKind::Case),
        expr(expr), items(items), defaultCase(defaultCase) {}

    static AssertionExpr& fromSyntax(const CasePropertyExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Case; }
};

struct InvocationExpressionSyntax;

/// Represents an instance of a named sequence or property within an assertion expression.
class InstanceAssertionExpr : public AssertionExpr {
public:
    const Symbol& symbol;
    const AssertionExpr& expanded;

    InstanceAssertionExpr(const Symbol& symbol, const AssertionExpr& expanded) :
        AssertionExpr(AssertionExprKind::Instance), symbol(symbol), expanded(expanded) {}

    static AssertionExpr& fromSyntax(const Symbol& symbol, const InvocationExpressionSyntax* invoc,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Instance; }
};

} // namespace slang
