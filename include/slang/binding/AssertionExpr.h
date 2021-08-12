//------------------------------------------------------------------------------
//! @file AssertionExpr.h
//! @brief Assertion expression creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"
#include "slang/binding/TimingControl.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/util/Util.h"

namespace slang {

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
class CallExpression;
class Compilation;
class SyntaxNode;
struct PropertyExprSyntax;
struct PropertySpecSyntax;
struct SequenceExprSyntax;

class AssertionExpr {
public:
    AssertionExprKind kind;

    const SyntaxNode* syntax = nullptr;

    void requireSequence(const BindContext& context) const;
    void requireSequence(const BindContext& context, DiagCode code) const;
    bool bad() const { return kind == AssertionExprKind::Invalid; }

    /// Returns true if this is a sequence expression that admits an empty match,
    /// and false otherwise.
    bool admitsEmpty() const;

    static const AssertionExpr& bind(const SequenceExprSyntax& syntax, const BindContext& context,
                                     bool allowDisable = false);

    static const AssertionExpr& bind(const PropertyExprSyntax& syntax, const BindContext& context,
                                     bool allowDisable = false, bool allowSeqAdmitEmpty = false);

    static const AssertionExpr& bind(const PropertySpecSyntax& syntax, const BindContext& context);

    static bool checkAssertionCall(const CallExpression& call, const BindContext& context,
                                   DiagCode outArgCode, DiagCode refArgCode,
                                   optional<DiagCode> sysTaskCode, SourceRange range);

    static void checkSampledValueExpr(const Expression& expr, const BindContext& context,
                                      bool isFutureGlobal, DiagCode localVarCode,
                                      DiagCode matchedCode);

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
    uint32_t min = 1;

    /// The maximum length of the range. If unset, the maximum is unbounded.
    optional<uint32_t> max;

    static SequenceRange fromSyntax(const SelectorSyntax& syntax, const BindContext& context,
                                    bool allowUnbounded);
    static SequenceRange fromSyntax(const RangeSelectSyntax& syntax, const BindContext& context,
                                    bool allowUnbounded);

    bool admitsEmpty() const;

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

    enum class AdmitsEmpty { Yes, No, Depends };
    AdmitsEmpty admitsEmpty() const;

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

    void requireSequence(const BindContext& context, DiagCode code) const;
    bool admitsEmptyImpl() const;

    static AssertionExpr& fromSyntax(const SimpleSequenceExprSyntax& syntax,
                                     const BindContext& context, bool allowDisable);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Simple; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
    }
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

    bool admitsEmptyImpl() const;

    static AssertionExpr& fromSyntax(const DelayedSequenceExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::SequenceConcat; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto& elem : elements)
            elem.sequence->visit(visitor);
    }
};

struct ParenthesizedSequenceExprSyntax;

/// Represents a sequence expression along with a list of actions to perform upon matching
/// and/or instructions for repetition.
class SequenceWithMatchExpr : public AssertionExpr {
public:
    const AssertionExpr& expr;
    optional<SequenceRepetition> repetition;
    span<const Expression* const> matchItems;

    SequenceWithMatchExpr(const AssertionExpr& expr, optional<SequenceRepetition> repetition,
                          span<const Expression* const> matchItems) :
        AssertionExpr(AssertionExprKind::SequenceWithMatch),
        expr(expr), repetition(repetition), matchItems(matchItems) {}

    bool admitsEmptyImpl() const;

    static AssertionExpr& fromSyntax(const ParenthesizedSequenceExprSyntax& syntax,
                                     const BindContext& context);

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

    bool admitsEmptyImpl() const { return false; }

    static AssertionExpr& fromSyntax(const UnaryPropertyExprSyntax& syntax,
                                     const BindContext& context);

    static AssertionExpr& fromSyntax(const UnarySelectPropertyExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Unary; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
    }
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

    void requireSequence(const BindContext& context, DiagCode code) const;
    bool admitsEmptyImpl() const;

    static AssertionExpr& fromSyntax(const BinarySequenceExprSyntax& syntax,
                                     const BindContext& context);

    static AssertionExpr& fromSyntax(const BinaryPropertyExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Binary; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        left.visit(visitor);
        right.visit(visitor);
    }
};

struct FirstMatchSequenceExprSyntax;

/// Represents a first_match operator in a sequence expression.
class FirstMatchAssertionExpr : public AssertionExpr {
public:
    const AssertionExpr& seq;
    span<const Expression* const> matchItems;

    FirstMatchAssertionExpr(const AssertionExpr& seq, span<const Expression* const> matchItems) :
        AssertionExpr(AssertionExprKind::FirstMatch), seq(seq), matchItems(matchItems) {}

    bool admitsEmptyImpl() const;

    static AssertionExpr& fromSyntax(const FirstMatchSequenceExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::FirstMatch; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        seq.visit(visitor);
        for (auto item : matchItems)
            item->visit(visitor);
    }
};

struct ClockingSequenceExprSyntax;
struct ClockingPropertyExprSyntax;
struct SignalEventExpressionSyntax;

/// Represents an assertion expression with attached clocking control.
class ClockingAssertionExpr : public AssertionExpr {
public:
    const TimingControl& clocking;
    const AssertionExpr& expr;

    ClockingAssertionExpr(const TimingControl& clocking, const AssertionExpr& expr) :
        AssertionExpr(AssertionExprKind::Clocking), clocking(clocking), expr(expr) {}

    bool admitsEmptyImpl() const;

    static AssertionExpr& fromSyntax(const ClockingSequenceExprSyntax& syntax,
                                     const BindContext& context);

    static AssertionExpr& fromSyntax(const ClockingPropertyExprSyntax& syntax,
                                     const BindContext& context);

    static AssertionExpr& fromSyntax(const SignalEventExpressionSyntax& syntax,
                                     const BindContext& context);

    static AssertionExpr& fromSyntax(const TimingControlSyntax& syntax, const AssertionExpr& expr,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Clocking; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        clocking.visit(visitor);
        expr.visit(visitor);
    }
};

struct StrongWeakPropertyExprSyntax;

/// Represents a strong or weak operator in a property expression.
class StrongWeakAssertionExpr : public AssertionExpr {
public:
    const AssertionExpr& expr;
    enum Strength { Strong, Weak } strength;

    StrongWeakAssertionExpr(const AssertionExpr& expr, Strength strength) :
        AssertionExpr(AssertionExprKind::StrongWeak), expr(expr), strength(strength) {}

    bool admitsEmptyImpl() const { return false; }

    static AssertionExpr& fromSyntax(const StrongWeakPropertyExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::StrongWeak; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
    }
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

    bool admitsEmptyImpl() const { return false; }

    static AssertionExpr& fromSyntax(const AcceptOnPropertyExprSyntax& syntax,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Abort; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        condition.visit(visitor);
        expr.visit(visitor);
    }
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

    bool admitsEmptyImpl() const { return false; }

    static AssertionExpr& fromSyntax(const ConditionalPropertyExprSyntax& syntax,
                                     const BindContext& context);

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

    bool admitsEmptyImpl() const { return false; }

    static AssertionExpr& fromSyntax(const CasePropertyExprSyntax& syntax,
                                     const BindContext& context);

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

struct DisableIffSyntax;

/// Represents a disable iff condition in a property spec.
class DisableIffAssertionExpr : public AssertionExpr {
public:
    const Expression& condition;
    const AssertionExpr& expr;

    DisableIffAssertionExpr(const Expression& condition, const AssertionExpr& expr) :
        AssertionExpr(AssertionExprKind::DisableIff), condition(condition), expr(expr) {}

    bool admitsEmptyImpl() const { return false; }

    static AssertionExpr& fromSyntax(const DisableIffSyntax& syntax, const AssertionExpr& expr,
                                     const BindContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::DisableIff; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        condition.visit(visitor);
        expr.visit(visitor);
    }
};

} // namespace slang
