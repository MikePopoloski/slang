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

/// Specifies possible classifications of assertion expressions
/// as they relate to "nondegeneracy", as described in the LRM.
enum class NondegeneracyStatus {
    /// No factors related to nondegeneracy (i.e. the expression
    /// is nondegenerate).
    None = 0,

    /// The sequence admits empty matches.
    AdmitsEmpty = 1 << 0,

    /// The sequence accepts only empty matches.
    AcceptsOnlyEmpty = 1 << 1,

    /// The sequence definitely admits no match.
    AdmitsNoMatch = 1 << 2
};
SLANG_BITMASK(NondegeneracyStatus, AdmitsNoMatch);

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

    /// Determines whether this range can intersect with @a other.
    bool canIntersect(const SequenceRange& other) const;

    /// Determines whether this range can be fully contained within @a other.
    bool canBeWithin(const SequenceRange& other) const;
};

/// The base class for assertion expressions (sequences and properties).
class SLANG_EXPORT AssertionExpr {
public:
    /// The kind of expression; indicates the type of derived class.
    AssertionExprKind kind;

    /// The syntax used to create the expression, if any. An expression tree can
    /// be created manually in which case it may not have a syntax representation.
    const syntax::SyntaxNode* syntax = nullptr;

    /// Reports an error if the assertion expression is not valid in a sequence.
    void requireSequence(const ASTContext& context) const;

    /// Reports an error if the assertion expression is not valid in a sequence.
    void requireSequence(const ASTContext& context, DiagCode code) const;

    /// Indicates whether the expression is invalid.
    bool bad() const { return kind == AssertionExprKind::Invalid; }

    /// Specifies binding behavior of property expressions as
    /// it pertains to nondegeneracy checking.
    enum class NondegeneracyRequirement {
        /// Any sequence that is used as a property shall be nondegenerate
        // and shall not admit any empty match.
        Default,

        /// Any sequence that is used as the antecedent of an overlapping implication
        /// or followed-by operator shall be nondegenerate.
        OverlapOp,

        /// Any sequence that is used as the antecedent of a nonoverlapping implication
        /// or followed-by operator shall admit at least one match. Such a sequence can
        /// admit only empty matches.
        NonOverlapOp,
    };

    /// A result structure for checking nondegeneracy.
    struct NondegeneracyCheckResult {
        /// The nondegeneracy status of the expression.
        bitmask<NondegeneracyStatus> status;

        /// The range of the expression that caused status
        /// to contain NondegeneracyStatus::AdmitsNoMatch.
        SourceRange noMatchRange;

        /// Set to true if the expression is known to be always false.
        bool isAlwaysFalse = false;

        NondegeneracyCheckResult& operator|=(const NondegeneracyCheckResult& rhs) {
            status |= rhs.status;
            if (!noMatchRange.start()) {
                noMatchRange = rhs.noMatchRange;
                isAlwaysFalse = rhs.isAlwaysFalse;
            }
            return *this;
        }

        NondegeneracyCheckResult operator|(const NondegeneracyCheckResult& rhs) const {
            auto result = *this;
            result |= rhs;
            return result;
        }
    };

    /// Checks whether this assertion expression is nondegenerate or whether it has
    /// properties of degeneracy (admitting empty matches or no matches at all).
    NondegeneracyCheckResult checkNondegeneracy() const;

    /// Computes possible clock ticks (delay) length of sequence under assertion expression.
    std::optional<SequenceRange> computeSequenceLength() const;

    static const AssertionExpr& bind(const syntax::SequenceExprSyntax& syntax,
                                     const ASTContext& context, bool allowDisable = false);

    static const AssertionExpr& bind(
        const syntax::PropertyExprSyntax& syntax, const ASTContext& context,
        bool allowDisable = false,
        NondegeneracyRequirement nondegRequirement = NondegeneracyRequirement::Default);

    static const AssertionExpr& bind(const syntax::PropertySpecSyntax& syntax,
                                     const ASTContext& context);

    static bool checkAssertionCall(const CallExpression& call, const ASTContext& context,
                                   DiagCode outArgCode, DiagCode refArgCode, DiagCode nonVoidCode,
                                   SourceRange range, bool isInsideSequence);

    static void checkSampledValueExpr(const Expression& expr, const ASTContext& context,
                                      bool isFutureGlobal, DiagCode localVarCode,
                                      DiagCode matchedCode);

    /// @brief Casts this expression to the given concrete derived type.
    ///
    /// Asserts that the type is appropriate given this expression's kind.
    template<typename T>
    T& as() {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    /// @brief Casts this expression to the given concrete derived type.
    ///
    /// Asserts that the type is appropriate given this expression's kind.
    template<typename T>
    const T& as() const {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    /// @brief Tries to cast this expression to the given concrete derived type.
    ///
    /// If the type is not appropriate given this expression's kind, returns nullptr.
    template<typename T>
    T* as_if() {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<T*>(this);
    }

    /// @brief Tries to cast this expression to the given concrete derived type.
    ///
    /// If the type is not appropriate given this expression's kind, returns nullptr.
    template<typename T>
    const T* as_if() const {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<const T*>(this);
    }

    /// Visits this expression's concrete derived type via the provided visitor object.
    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

protected:
    explicit AssertionExpr(AssertionExprKind kind) : kind(kind) {}

    static AssertionExpr& badExpr(Compilation& compilation, const AssertionExpr* expr);
};

/// @brief Represents an invalid expression
///
/// Usually generated and inserted into an expression tree due
/// to violation of language semantics or type checking.
class SLANG_EXPORT InvalidAssertionExpr : public AssertionExpr {
public:
    /// A wrapped sub-expression that is considered invalid.
    const AssertionExpr* child;

    explicit InvalidAssertionExpr(const AssertionExpr* child) :
        AssertionExpr(AssertionExprKind::Invalid), child(child) {}

    NondegeneracyCheckResult checkNondegeneracyImpl() const { return {}; }

    std::optional<SequenceRange> computeSequenceLengthImpl() const { return {}; }

    static bool isKind(AssertionExprKind kind) { return kind == AssertionExprKind::Invalid; }

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

    /// Checks whether this assertion expression is nondegenerate or whether it has
    /// properties of degeneracy (admitting empty matches or no matches at all).
    AssertionExpr::NondegeneracyCheckResult checkNondegeneracy() const;

    /// Applies the repetition to the given range, scaling it and returning the result.
    SequenceRange applyTo(SequenceRange other) const;

    void serializeTo(ASTSerializer& serializer) const;
};

/// Represents an assertion expression defined as a simple regular expression.
class SLANG_EXPORT SimpleAssertionExpr : public AssertionExpr {
public:
    /// The expression that constitutes the sequence.
    const Expression& expr;

    /// An optional repetition of the sequence.
    std::optional<SequenceRepetition> repetition;

    /// Set to true if the sequence expression is a known `false` constant value.
    bool isNullExpr;

    SimpleAssertionExpr(const Expression& expr, std::optional<SequenceRepetition> repetition,
                        bool isNullExpr = false) :
        AssertionExpr(AssertionExprKind::Simple), expr(expr), repetition(repetition),
        isNullExpr(isNullExpr) {}

    void requireSequence(const ASTContext& context, DiagCode code) const;
    NondegeneracyCheckResult checkNondegeneracyImpl() const;
    std::optional<SequenceRange> computeSequenceLengthImpl() const;

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
    /// An element of a sequence concatenation.
    struct Element {
        /// A delay that applies to the element.
        SequenceRange delay;

        /// The element expression.
        not_null<const AssertionExpr*> sequence;
    };

    /// The elements of the concatenation.
    std::span<const Element> elements;

    explicit SequenceConcatExpr(std::span<const Element> elements) :
        AssertionExpr(AssertionExprKind::SequenceConcat), elements(elements) {}

    NondegeneracyCheckResult checkNondegeneracyImpl() const;
    std::optional<SequenceRange> computeSequenceLengthImpl() const;

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
    /// The sequence expression.
    const AssertionExpr& expr;

    /// An optional repetition to apply to the expression.
    std::optional<SequenceRepetition> repetition;

    /// Match items to apply upon matching the sequence.
    std::span<const Expression* const> matchItems;

    SequenceWithMatchExpr(const AssertionExpr& expr, std::optional<SequenceRepetition> repetition,
                          std::span<const Expression* const> matchItems) :
        AssertionExpr(AssertionExprKind::SequenceWithMatch), expr(expr), repetition(repetition),
        matchItems(matchItems) {}

    NondegeneracyCheckResult checkNondegeneracyImpl() const;
    std::optional<SequenceRange> computeSequenceLengthImpl() const;

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
    /// The operator.
    UnaryAssertionOperator op;

    /// The operand.
    const AssertionExpr& expr;

    /// An optional sequence range.
    std::optional<SequenceRange> range;

    UnaryAssertionExpr(UnaryAssertionOperator op, const AssertionExpr& expr,
                       std::optional<SequenceRange> range) :
        AssertionExpr(AssertionExprKind::Unary), op(op), expr(expr), range(range) {}

    NondegeneracyCheckResult checkNondegeneracyImpl() const { return {}; }
    std::optional<SequenceRange> computeSequenceLengthImpl() const { return {}; }

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
    /// The operator.
    BinaryAssertionOperator op;

    /// The left operand.
    const AssertionExpr& left;

    /// The right operand.
    const AssertionExpr& right;

    BinaryAssertionExpr(BinaryAssertionOperator op, const AssertionExpr& left,
                        const AssertionExpr& right) :
        AssertionExpr(AssertionExprKind::Binary), op(op), left(left), right(right) {}

    void requireSequence(const ASTContext& context, DiagCode code) const;

    NondegeneracyCheckResult checkNondegeneracyImpl() const;
    std::optional<SequenceRange> computeSequenceLengthImpl() const;

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
    /// The operand.
    const AssertionExpr& seq;

    /// Match items that apply upon matching the sequence.
    std::span<const Expression* const> matchItems;

    FirstMatchAssertionExpr(const AssertionExpr& seq,
                            std::span<const Expression* const> matchItems) :
        AssertionExpr(AssertionExprKind::FirstMatch), seq(seq), matchItems(matchItems) {}

    NondegeneracyCheckResult checkNondegeneracyImpl() const;

    std::optional<SequenceRange> computeSequenceLengthImpl() const {
        return seq.computeSequenceLength();
    }

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
    /// The clocking control.
    const TimingControl& clocking;

    /// The expression controlled by the clocking.
    const AssertionExpr& expr;

    ClockingAssertionExpr(const TimingControl& clocking, const AssertionExpr& expr) :
        AssertionExpr(AssertionExprKind::Clocking), clocking(clocking), expr(expr) {}

    NondegeneracyCheckResult checkNondegeneracyImpl() const { return expr.checkNondegeneracy(); }

    std::optional<SequenceRange> computeSequenceLengthImpl() const {
        return expr.computeSequenceLength();
    }

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
    /// The expression that is being modified.
    const AssertionExpr& expr;

    /// The kind of expression -- strong or weak.
    enum Strength { Strong, Weak } strength;

    StrongWeakAssertionExpr(const AssertionExpr& expr, Strength strength) :
        AssertionExpr(AssertionExprKind::StrongWeak), expr(expr), strength(strength) {}

    NondegeneracyCheckResult checkNondegeneracyImpl() const { return {}; }
    std::optional<SequenceRange> computeSequenceLengthImpl() const { return {}; }

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
    /// The condition of the abort.
    const Expression& condition;

    /// The expression being controlled.
    const AssertionExpr& expr;

    /// The action to take upon condition success (accept or reject).
    enum Action { Accept, Reject } action;

    /// True if this is a "synchronized" variant of the operator.
    bool isSync;

    AbortAssertionExpr(const Expression& condition, const AssertionExpr& expr, Action action,
                       bool isSync) :
        AssertionExpr(AssertionExprKind::Abort), condition(condition), expr(expr), action(action),
        isSync(isSync) {}

    NondegeneracyCheckResult checkNondegeneracyImpl() const { return {}; }
    std::optional<SequenceRange> computeSequenceLengthImpl() const { return {}; }

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
    /// The condition expression.
    const Expression& condition;

    /// The expression that applies if the condition is true.
    const AssertionExpr& ifExpr;

    /// An optional expression that applies if the condition is false.
    const AssertionExpr* elseExpr;

    ConditionalAssertionExpr(const Expression& condition, const AssertionExpr& ifExpr,
                             const AssertionExpr* elseExpr) :
        AssertionExpr(AssertionExprKind::Conditional), condition(condition), ifExpr(ifExpr),
        elseExpr(elseExpr) {}

    NondegeneracyCheckResult checkNondegeneracyImpl() const { return {}; }
    std::optional<SequenceRange> computeSequenceLengthImpl() const { return {}; }

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
    /// A group of items that match one case item.
    struct ItemGroup {
        /// The expressions that are checked for matching.
        std::span<const Expression* const> expressions;

        /// The expression that applies if an item matches.
        not_null<const AssertionExpr*> body;
    };

    /// The controlling case expression.
    const Expression& expr;

    /// The list of case items that get checked for a match.
    std::span<const ItemGroup> items;

    /// An optional default case that applies if no items match.
    const AssertionExpr* defaultCase = nullptr;

    CaseAssertionExpr(const Expression& expr, std::span<const ItemGroup> items,
                      const AssertionExpr* defaultCase) :
        AssertionExpr(AssertionExprKind::Case), expr(expr), items(items), defaultCase(defaultCase) {
    }

    NondegeneracyCheckResult checkNondegeneracyImpl() const { return {}; }
    std::optional<SequenceRange> computeSequenceLengthImpl() const { return {}; }

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
    /// The disable condition expression.
    const Expression& condition;

    /// The assertion expression being disabled.
    const AssertionExpr& expr;

    DisableIffAssertionExpr(const Expression& condition, const AssertionExpr& expr) :
        AssertionExpr(AssertionExprKind::DisableIff), condition(condition), expr(expr) {}

    NondegeneracyCheckResult checkNondegeneracyImpl() const { return {}; }
    std::optional<SequenceRange> computeSequenceLengthImpl() const { return {}; }

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
