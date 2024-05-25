//------------------------------------------------------------------------------
// AssertionExpr.cpp
// Assertion expression creation and analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/expressions/AssertionExpr.h"

#include "slang/ast/ASTContext.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/Expression.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/TimingControl.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace {

using namespace slang::ast;

struct NondegeneracyCheckVisitor {
    template<typename T>
    slang::bitmask<NondegeneracyStatus> visit(const T& expr) {
        if (expr.bad())
            return NondegeneracyStatus::None;

        return expr.checkNondegeneracyImpl();
    }
};

struct SequenceLengthVisitor {
    template<typename T>
    std::optional<SequenceRange> visit(const T& expr) {
        if (expr.bad())
            return std::nullopt;

        return expr.computeSequenceLengthImpl();
    }
};

} // namespace

namespace slang::ast {

using namespace parsing;
using namespace syntax;

static const Expression& bindExpr(const ExpressionSyntax& syntax, const ASTContext& context,
                                  bool allowInstances = false) {
    auto& expr = Expression::bind(syntax, context, ASTFlags::AssertionExpr);
    if (expr.bad())
        return expr;

    if (allowInstances && (expr.type->isSequenceType() || expr.type->isPropertyType()))
        return expr;

    if (!expr.type->isValidForSequence() && expr.kind != ExpressionKind::Dist) {
        auto& comp = context.getCompilation();
        context.addDiag(diag::AssertionExprType, expr.sourceRange) << *expr.type;
        return *comp.emplace<InvalidExpression>(&expr, comp.getErrorType());
    }

    return expr;
}

const AssertionExpr& AssertionExpr::bind(const SequenceExprSyntax& syntax,
                                         const ASTContext& context, bool allowDisable) {
    ASTContext ctx(context);
    ctx.flags |= ASTFlags::AssignmentDisallowed;

    AssertionExpr* result;
    switch (syntax.kind) {
        case SyntaxKind::SimpleSequenceExpr:
            result = &SimpleAssertionExpr::fromSyntax(syntax.as<SimpleSequenceExprSyntax>(), ctx,
                                                      allowDisable);
            break;
        case SyntaxKind::DelayedSequenceExpr:
            result = &SequenceConcatExpr::fromSyntax(syntax.as<DelayedSequenceExprSyntax>(), ctx);
            break;
        case SyntaxKind::AndSequenceExpr:
        case SyntaxKind::OrSequenceExpr:
        case SyntaxKind::IntersectSequenceExpr:
        case SyntaxKind::ThroughoutSequenceExpr:
        case SyntaxKind::WithinSequenceExpr:
            result = &BinaryAssertionExpr::fromSyntax(syntax.as<BinarySequenceExprSyntax>(), ctx);
            break;
        case SyntaxKind::ParenthesizedSequenceExpr: {
            auto& pse = syntax.as<ParenthesizedSequenceExprSyntax>();
            if (pse.matchList || pse.repetition)
                return SequenceWithMatchExpr::fromSyntax(pse, ctx);

            return bind(*pse.expr, context);
        }
        case SyntaxKind::FirstMatchSequenceExpr:
            result = &FirstMatchAssertionExpr::fromSyntax(syntax.as<FirstMatchSequenceExprSyntax>(),
                                                          ctx);
            break;
        case SyntaxKind::ClockingSequenceExpr:
            result = &ClockingAssertionExpr::fromSyntax(syntax.as<ClockingSequenceExprSyntax>(),
                                                        ctx);
            break;
        case SyntaxKind::SignalEventExpression:
            result = &ClockingAssertionExpr::fromSyntax(syntax.as<SignalEventExpressionSyntax>(),
                                                        ctx);
            break;
        default:
            SLANG_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

const AssertionExpr& AssertionExpr::bind(const PropertyExprSyntax& syntax,
                                         const ASTContext& context, bool allowDisable,
                                         NondegeneracyFlags nondegFlags) {
    ASTContext ctx(context);
    ctx.flags |= ASTFlags::AssignmentDisallowed;

    AssertionExpr* result;
    switch (syntax.kind) {
        case SyntaxKind::SimplePropertyExpr: {
            // Just a simple passthrough to creating the sequence expression
            // contained within.
            auto& seq = bind(*syntax.as<SimplePropertyExprSyntax>().expr, ctx, allowDisable);
            const auto seqNondegenSt = seq.checkNondegeneracy();
            bool isSeqAdmitsEmpty = seqNondegenSt.has(NondegeneracyStatus::AdmitsEmpty);
            bool isSeqAcceptsOnlyEmpty = seqNondegenSt.has(NondegeneracyStatus::AcceptsOnlyEmpty);
            bool isSeqAdmitsNoMatch = seqNondegenSt.has(NondegeneracyStatus::AdmitsNoMatch);

            // See 16.12.22 section at SystemVerilog LRM for details.
            // Any sequence that is used as the antecedent of an overlapping implication (|->) shall
            // be nondegenerate.
            if (nondegFlags == NondegeneracyFlags::IsOverlapImplOrHashMinus) {
                if (isSeqAcceptsOnlyEmpty || isSeqAdmitsNoMatch) {
                    auto& diag = context.addDiag(diag::OverlapImplNondegenerate,
                                                 syntax.sourceRange());
                    diag.addNote((isSeqAcceptsOnlyEmpty) ? diag::SeqAcceptsOnlyEmptyMatches
                                                         : diag::SeqAdmitsNoMatches,
                                 syntax.sourceRange());
                }
            }
            // Any sequence that is used as the antecedent of a nonoverlapping implication (|=>)
            // shall admit at least one match. Such a sequence can admit only empty matches.
            else if (nondegFlags == NondegeneracyFlags::IsNonOverlapImplOrHashEq) {
                if (isSeqAdmitsNoMatch) {
                    auto& diag = context.addDiag(diag::NonOverlapImplNondegenerate,
                                                 syntax.sourceRange());
                    diag.addNote(diag::SeqAdmitsNoMatches, syntax.sourceRange());
                }
            }
            // Any sequence that is used as a property shall be nondegenerate and shall not admit
            // any empty match.
            else if (isSeqAdmitsEmpty || isSeqAdmitsNoMatch) {
                auto& diag = context.addDiag(diag::SeqPropNondegenerate, syntax.sourceRange());
                diag.addNote((isSeqAdmitsEmpty) ? diag::SeqAdmitsEmptyMatches
                                                : diag::SeqAdmitsNoMatches,
                             syntax.sourceRange());
            }

            return seq;
        }
        case SyntaxKind::AndPropertyExpr:
        case SyntaxKind::OrPropertyExpr:
        case SyntaxKind::IffPropertyExpr:
        case SyntaxKind::UntilPropertyExpr:
        case SyntaxKind::SUntilPropertyExpr:
        case SyntaxKind::UntilWithPropertyExpr:
        case SyntaxKind::SUntilWithPropertyExpr:
        case SyntaxKind::ImpliesPropertyExpr:
        case SyntaxKind::ImplicationPropertyExpr:
        case SyntaxKind::FollowedByPropertyExpr:
            result = &BinaryAssertionExpr::fromSyntax(syntax.as<BinaryPropertyExprSyntax>(), ctx);
            break;
        case SyntaxKind::ParenthesizedPropertyExpr: {
            auto& ppe = syntax.as<ParenthesizedPropertyExprSyntax>();
            if (ppe.matchList) {
                // Similarly to the match list in a parenthesized sequence expression, during
                // argument checking this can be part of an event expression instead.
                if (ctx.flags.has(ASTFlags::AssertionInstanceArgCheck)) {
                    for (auto item : ppe.matchList->items)
                        AssertionExpr::bind(*item, ctx);
                }
                else {
                    ctx.addDiag(diag::InvalidCommaInPropExpr, ppe.matchList->sourceRange());
                    return badExpr(ctx.getCompilation(), nullptr);
                }
            }
            return bind(*ppe.expr, context);
        }
        case SyntaxKind::ClockingPropertyExpr:
            result = &ClockingAssertionExpr::fromSyntax(syntax.as<ClockingPropertyExprSyntax>(),
                                                        ctx);
            break;
        case SyntaxKind::StrongWeakPropertyExpr:
            result = &StrongWeakAssertionExpr::fromSyntax(syntax.as<StrongWeakPropertyExprSyntax>(),
                                                          ctx);
            break;
        case SyntaxKind::UnaryPropertyExpr:
            result = &UnaryAssertionExpr::fromSyntax(syntax.as<UnaryPropertyExprSyntax>(), ctx);
            break;
        case SyntaxKind::UnarySelectPropertyExpr:
            result = &UnaryAssertionExpr::fromSyntax(syntax.as<UnarySelectPropertyExprSyntax>(),
                                                     ctx);
            break;
        case SyntaxKind::AcceptOnPropertyExpr:
            result = &AbortAssertionExpr::fromSyntax(syntax.as<AcceptOnPropertyExprSyntax>(), ctx);
            break;
        case SyntaxKind::ConditionalPropertyExpr:
            result = &ConditionalAssertionExpr::fromSyntax(
                syntax.as<ConditionalPropertyExprSyntax>(), ctx);
            break;
        case SyntaxKind::CasePropertyExpr:
            result = &CaseAssertionExpr::fromSyntax(syntax.as<CasePropertyExprSyntax>(), ctx);
            break;
        default:
            SLANG_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

const AssertionExpr& AssertionExpr::bind(const PropertySpecSyntax& syntax,
                                         const ASTContext& context) {
    ASTContext ctx(context);
    ctx.flags |= ASTFlags::AssignmentDisallowed;

    bool allowDisable = syntax.disable == nullptr;
    auto result = &bind(*syntax.expr, context, allowDisable);

    if (syntax.disable) {
        auto& disable = DisableIffAssertionExpr::fromSyntax(*syntax.disable, *result, context);
        disable.syntax = syntax.disable;
        result = &disable;
    }

    if (syntax.clocking) {
        auto& clocking = ClockingAssertionExpr::fromSyntax(*syntax.clocking, *result, context);
        clocking.syntax = syntax.clocking;
        result = &clocking;
    }

    return *result;
}

void AssertionExpr::requireSequence(const ASTContext& context) const {
    requireSequence(context, diag::PropExprInSequence);
}

void AssertionExpr::requireSequence(const ASTContext& context, DiagCode code) const {
    switch (kind) {
        case AssertionExprKind::Simple:
            as<SimpleAssertionExpr>().requireSequence(context, code);
            return;
        case AssertionExprKind::Binary:
            as<BinaryAssertionExpr>().requireSequence(context, code);
            return;
        case AssertionExprKind::Clocking:
            as<ClockingAssertionExpr>().expr.requireSequence(context, code);
            return;
        case AssertionExprKind::Unary:
        case AssertionExprKind::StrongWeak:
        case AssertionExprKind::Abort:
        case AssertionExprKind::Conditional:
        case AssertionExprKind::Case:
        case AssertionExprKind::DisableIff:
            SLANG_ASSERT(syntax);
            context.addDiag(code, syntax->sourceRange());
            return;
        case AssertionExprKind::SequenceConcat:
        case AssertionExprKind::SequenceWithMatch:
        case AssertionExprKind::FirstMatch:
        case AssertionExprKind::Invalid:
            return;
    }
    SLANG_UNREACHABLE;
}

bitmask<NondegeneracyStatus> AssertionExpr::checkNondegeneracy() const {
    NondegeneracyCheckVisitor visitor;
    return visit(visitor);
}

std::optional<SequenceRange> AssertionExpr::computeSequenceLength() const {
    SequenceLengthVisitor visitor;
    return visit(visitor);
}

AssertionExpr& AssertionExpr::badExpr(Compilation& compilation, const AssertionExpr* expr) {
    return *compilation.emplace<InvalidAssertionExpr>(expr);
}

bool AssertionExpr::checkAssertionCall(const CallExpression& call, const ASTContext& context,
                                       DiagCode outArgCode, DiagCode refArgCode,
                                       DiagCode nonVoidCode, SourceRange range) {
    if (call.getSubroutineKind() == SubroutineKind::Function && !call.type->isVoid() &&
        !call.type->isError()) {
        context.addDiag(nonVoidCode, range) << call.getSubroutineName();
    }

    if (call.isSystemCall()) {
        auto& sub = *std::get<1>(call.subroutine).subroutine;
        if (sub.hasOutputArgs) {
            context.addDiag(outArgCode, range);
            return false;
        }
    }
    else {
        auto& sub = *std::get<0>(call.subroutine);
        auto args = call.arguments();
        size_t index = 0;
        for (auto& formal : sub.getArguments()) {
            if (formal->direction == ArgumentDirection::Out ||
                formal->direction == ArgumentDirection::InOut) {
                auto& diag = context.addDiag(outArgCode, range);
                diag.addNote(diag::NoteDeclarationHere, formal->location);
                return false;
            }

            if (formal->direction == ArgumentDirection::Ref) {
                SLANG_ASSERT(index < args.size());
                if (auto sym = args[index]->getSymbolReference()) {
                    if (VariableSymbol::isKind(sym->kind) &&
                        sym->as<VariableSymbol>().lifetime == VariableLifetime::Automatic) {
                        auto& diag = context.addDiag(refArgCode, args[index]->sourceRange);
                        diag << sym->name << formal->name;
                        diag.addNote(diag::NoteDeclarationHere, sym->location);
                        return false;
                    }
                }
            }

            index++;
        }
    }

    return true;
}

struct SampledValueExprVisitor {
    const ASTContext& context;
    bool isFutureGlobal;
    DiagCode localVarCode;
    DiagCode matchedCode;

    SampledValueExprVisitor(const ASTContext& context, bool isFutureGlobal, DiagCode localVarCode,
                            DiagCode matchedCode) :
        context(context), isFutureGlobal(isFutureGlobal), localVarCode(localVarCode),
        matchedCode(matchedCode) {}

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_base_of_v<Expression, T>) {
            switch (expr.kind) {
                case ExpressionKind::NamedValue:
                    if (auto sym = expr.getSymbolReference()) {
                        if (sym->kind == SymbolKind::LocalAssertionVar ||
                            (sym->kind == SymbolKind::AssertionPort &&
                             sym->template as<AssertionPortSymbol>().isLocalVar())) {
                            context.addDiag(localVarCode, expr.sourceRange);
                        }
                    }
                    break;
                case ExpressionKind::Call: {
                    auto& call = expr.template as<CallExpression>();
                    if (call.isSystemCall()) {
                        if (call.getSubroutineName() == "matched"sv && !call.arguments().empty() &&
                            call.arguments()[0]->type->isSequenceType()) {
                            context.addDiag(matchedCode, expr.sourceRange);
                        }

                        if (isFutureGlobal && FutureGlobalNames.count(call.getSubroutineName())) {
                            context.addDiag(diag::GlobalSampledValueNested, expr.sourceRange);
                        }
                    }
                    break;
                }
                default:
                    if constexpr (HasVisitExprs<T, SampledValueExprVisitor>)
                        expr.visitExprs(*this);
                    break;
            }
        }
    }

    static inline const flat_hash_set<std::string_view> FutureGlobalNames = {
        "$future_gclk"sv, "$rising_gclk"sv, "$falling_gclk"sv, "$steady_gclk"sv,
        "$changing_gclk"sv};
};

void AssertionExpr::checkSampledValueExpr(const Expression& expr, const ASTContext& context,
                                          bool isFutureGlobal, DiagCode localVarCode,
                                          DiagCode matchedCode) {
    SampledValueExprVisitor visitor(context, isFutureGlobal, localVarCode, matchedCode);
    expr.visit(visitor);
}

std::optional<SequenceRange> InvalidAssertionExpr::computeSequenceLengthImpl() const {
    return std::nullopt;
}

void InvalidAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    if (child)
        serializer.write("child", *child);
}

SequenceRange SequenceRange::fromSyntax(const SelectorSyntax& syntax, const ASTContext& context,
                                        bool allowUnbounded) {
    if (syntax.kind == SyntaxKind::BitSelect) {
        auto val = context.evalInteger(*syntax.as<BitSelectSyntax>().expr,
                                       ASTFlags::AssertionDelayOrRepetition);

        SequenceRange range;
        if (context.requirePositive(val, syntax.sourceRange()))
            range.max = range.min = uint32_t(*val);

        return range;
    }
    else {
        auto& rs = syntax.as<RangeSelectSyntax>();
        return fromSyntax(rs, context, allowUnbounded);
    }
}

SequenceRange SequenceRange::fromSyntax(const RangeSelectSyntax& syntax, const ASTContext& context,
                                        bool allowUnbounded) {
    SequenceRange range;
    auto l = context.evalInteger(*syntax.left, ASTFlags::AssertionDelayOrRepetition);
    if (context.requirePositive(l, syntax.left->sourceRange()))
        range.min = uint32_t(*l);

    // The rhs can be an unbounded '$' so we need extra AST flags.
    bitmask<ASTFlags> flags = ASTFlags::AssertionExpr | ASTFlags::AssertionDelayOrRepetition;
    if (allowUnbounded)
        flags |= ASTFlags::AllowUnboundedLiteral;

    auto& re = Expression::bind(*syntax.right, context, flags);
    if (re.type->isUnbounded())
        return range;

    auto r = context.evalInteger(re);
    if (context.requirePositive(r, syntax.right->sourceRange())) {
        range.max = uint32_t(*r);
        if (*l > *r) {
            auto& diag = context.addDiag(diag::SeqRangeMinMax, syntax.left->sourceRange());
            diag << syntax.right->sourceRange();
            diag << *l << *r;
        }
    }

    return range;
}

void SequenceRange::serializeTo(ASTSerializer& serializer) const {
    serializer.write("min", min);
    if (max)
        serializer.write("max", *max);
    else
        serializer.write("max", "$"sv);
}

bool SequenceRange::operator<(const SequenceRange& right) const {
    // if both sequences are unbounded then check min's
    if (!max.has_value() && !right.max.has_value())
        return min < right.min;

    // if both sequences are bounded then compare it's diff's
    if (max.has_value() && right.max.has_value()) {
        uint32_t maxVal = max.value();
        uint32_t rightMaxVal = right.max.value();
        return ((maxVal - min) < (rightMaxVal - right.min)) && (min < right.min);
    }

    // if only left is bounded than return `true` because right sequence is potentially
    // have an infinite number of matches
    if (max.has_value())
        return true;

    // return `false` otherwise (in case is right sequence if bounded)
    return false;
}

bool SequenceRange::isIntersect(const SequenceRange& other) const {
    if (!max.has_value())
        return (other.max.has_value()) ? (min >= other.min && min <= other.max.value())
                                       : min == other.min;

    if (!other.max.has_value())
        return (max.has_value()) ? (other.min >= min && other.min <= max.value())
                                 : other.min == min;

    return !(max.value() < other.min || other.max.value() < min);
}

bool SequenceRange::isWithin(const SequenceRange& other) const {
    if (!other.max.has_value())
        return (max.has_value()) ? (min == other.min && max == other.min) : min == other.min;

    return (max.has_value()) ? (min >= other.min && max <= other.max)
                             : (min >= other.min && min <= other.max);
}

SequenceRepetition::SequenceRepetition(const SequenceRepetitionSyntax& syntax,
                                       const ASTContext& context) {
    switch (syntax.op.kind) {
        case TokenKind::Equals:
            kind = Nonconsecutive;
            break;
        case TokenKind::MinusArrow:
            kind = GoTo;
            break;
        case TokenKind::Plus:
            // No expressions allowed for plus.
            kind = Consecutive;
            range.min = 1;
            return;
        default:
            kind = Consecutive;
            break;
    }

    if (syntax.selector)
        range = SequenceRange::fromSyntax(*syntax.selector, context, /* allowUnbounded */ true);
}

SequenceRepetition::AdmitsEmpty SequenceRepetition::admitsEmpty() const {
    // If and only if min and max delays are both zero, then the sequence accepts only empty
    // matches.
    if (range.min == 0 && range.max.has_value() && range.max.value() == 0)
        return AdmitsEmpty::Only;

    switch (kind) {
        case Consecutive:
            if (range.min == 0)
                return AdmitsEmpty::Yes;
            return AdmitsEmpty::Depends;
        case GoTo:
        case Nonconsecutive:
            if (range.min == 0)
                return AdmitsEmpty::Yes;
            return AdmitsEmpty::No;
    }
    SLANG_UNREACHABLE;
}

void SequenceRepetition::serializeTo(ASTSerializer& serializer) const {
    serializer.startObject();

    switch (kind) {
        case Consecutive:
            serializer.write("kind", "Consecutive"sv);
            break;
        case Nonconsecutive:
            serializer.write("kind", "Nonconsecutive"sv);
            break;
        case GoTo:
            serializer.write("kind", "GoTo"sv);
            break;
    }

    range.serializeTo(serializer);
    serializer.endObject();
}

AssertionExpr& SimpleAssertionExpr::fromSyntax(const SimpleSequenceExprSyntax& syntax,
                                               const ASTContext& context, bool allowDisable) {
    auto& comp = context.getCompilation();
    auto& expr = bindExpr(*syntax.expr, context, /* allowInstances */ true);

    std::optional<SequenceRepetition> repetition;
    if (syntax.repetition) {
        repetition.emplace(*syntax.repetition, context);

        if (expr.kind == ExpressionKind::AssertionInstance) {
            if (expr.type->isPropertyType())
                context.addDiag(diag::PropInstanceRepetition, syntax.repetition->sourceRange());
            else if (repetition->kind != SequenceRepetition::Consecutive)
                context.addDiag(diag::SeqInstanceRepetition, syntax.repetition->sourceRange());
        }
    }
    else if (expr.kind == ExpressionKind::AssertionInstance && !allowDisable) {
        auto& aie = expr.as<AssertionInstanceExpression>();
        auto targetExpr = &aie.body;
        if (targetExpr->kind == AssertionExprKind::Clocking)
            targetExpr = &targetExpr->as<ClockingAssertionExpr>().expr;

        if (targetExpr->kind == AssertionExprKind::DisableIff) {
            auto& diag = context.addDiag(diag::NestedDisableIff, syntax.sourceRange());
            diag << aie.symbol.name;

            if (targetExpr->syntax) {
                diag.addNote(diag::NoteDeclarationHere,
                             targetExpr->syntax->getFirstToken().location());
            }
        }
    }

    const auto evaluatedValue = context.tryEval(expr);
    return *comp.emplace<SimpleAssertionExpr>(
        expr, repetition, (evaluatedValue.isInteger() && !evaluatedValue.isTrue()));
}

void SimpleAssertionExpr::requireSequence(const ASTContext& context, DiagCode code) const {
    if (expr.kind == ExpressionKind::AssertionInstance) {
        auto& aie = expr.as<AssertionInstanceExpression>();
        if (aie.type->isPropertyType()) {
            SLANG_ASSERT(syntax);
            context.addDiag(code, syntax->sourceRange());
            return;
        }

        aie.body.requireSequence(context, code);
    }
}

bitmask<NondegeneracyStatus> SimpleAssertionExpr::checkNondegeneracyImpl() const {
    bitmask<NondegeneracyStatus> res = NondegeneracyStatus::None;

    // If simple sequence expression can be evaluated to `false` (`0`)
    // manually then it should be reported as sequence
    // with no possible match
    res = (isNullExpr) ? res | NondegeneracyStatus::AdmitsNoMatch : res;

    if (repetition) {
        auto repEmptyStatus = repetition->admitsEmpty();
        if (repEmptyStatus == SequenceRepetition::AdmitsEmpty::Yes)
            res |= NondegeneracyStatus::AdmitsEmpty;
        if (repEmptyStatus == SequenceRepetition::AdmitsEmpty::Only)
            res |= (NondegeneracyStatus::AcceptsOnlyEmpty | NondegeneracyStatus::AdmitsEmpty);
    }

    if (expr.kind == ExpressionKind::AssertionInstance) {
        auto& aie = expr.as<AssertionInstanceExpression>();
        if (aie.type->isSequenceType())
            res |= aie.body.checkNondegeneracy();
    }
    return res;
}

std::optional<SequenceRange> SimpleAssertionExpr::computeSequenceLengthImpl() const {
    SequenceRange res;
    // If there is only empty match sequence then it's have a zero delay length
    res.min = (checkNondegeneracy().has(NondegeneracyStatus::AcceptsOnlyEmpty)) ? 0 : 1;
    res.max = res.min;

    if (expr.kind == ExpressionKind::AssertionInstance) {
        if (auto& aie = expr.as<AssertionInstanceExpression>(); aie.type->isSequenceType()) {
            if (std::optional<SequenceRange> aieSeqLength = aie.body.computeSequenceLength();
                aieSeqLength.has_value() && (res < aieSeqLength.value()))
                return aieSeqLength.value();
        }
    }
    return res;
}

void SimpleAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
    if (repetition) {
        serializer.writeProperty("repetition");
        repetition->serializeTo(serializer);
    }
}

AssertionExpr& SequenceConcatExpr::fromSyntax(const DelayedSequenceExprSyntax& syntax,
                                              const ASTContext& context) {
    bool ok = true;
    SmallVector<Element, 8> elems;
    if (syntax.first) {
        auto& seq = bind(*syntax.first, context);
        seq.requireSequence(context);
        ok &= !seq.bad();

        SequenceRange delay{0, 0};
        elems.push_back({delay, &seq});
    }

    for (auto es : syntax.elements) {
        SequenceRange delay;
        auto& seq = bind(*es->expr, context);
        seq.requireSequence(context);
        ok &= !seq.bad();

        if (es->delayVal) {
            auto val = context.evalInteger(*es->delayVal, ASTFlags::AssertionDelayOrRepetition);
            if (!context.requirePositive(val, es->delayVal->sourceRange()))
                ok = false;
            else
                delay.max = delay.min = uint32_t(*val);
        }
        else if (es->range) {
            delay = SequenceRange::fromSyntax(*es->range, context,
                                              /* allowUnbounded */ true);
        }
        else if (es->op.kind == TokenKind::Plus) {
            delay.min = 1;
        }

        elems.push_back(Element{delay, &seq});
    }

    auto& comp = context.getCompilation();
    auto result = comp.emplace<SequenceConcatExpr>(elems.copy(comp));
    if (!ok)
        return badExpr(comp, result);

    return *result;
}

bitmask<NondegeneracyStatus> SequenceConcatExpr::checkNondegeneracyImpl() const {
    bool admitsEmpty = true;
    bool admitsNoMatch = false;
    auto left = elements.begin();
    SLANG_ASSERT(left != elements.end());
    auto leftNondegenSt = left->sequence->checkNondegeneracy();

    if (left->delay.min != 0 || !leftNondegenSt.has(NondegeneracyStatus::AdmitsEmpty))
        admitsEmpty = false;

    if (leftNondegenSt.has(NondegeneracyStatus::AdmitsNoMatch))
        admitsNoMatch = true;

    // See SystemVerilog LRM sections 16.9.2.1 and F.3.4.2.2 for details
    while (admitsEmpty || !admitsNoMatch) {
        const auto right = left + 1;
        if (left == elements.end() || right == elements.end())
            break;

        const auto rightNondegenSt = right->sequence->checkNondegeneracy();
        // If any element of concat sequence is no match then all concat sequence is no match
        if (rightNondegenSt.has(NondegeneracyStatus::AdmitsNoMatch))
            admitsNoMatch = true;

        if (!rightNondegenSt.has(NondegeneracyStatus::AdmitsEmpty))
            admitsEmpty = false;

        // If right part is present with zero min and max delays
        if (!right->delay.min && right->delay.max.has_value() && !right->delay.max.value()) {
            admitsEmpty = false;

            // (empty ##0 seq) does not result in a match
            // We need to check that case if and only if we are at the start of concat sequence
            // because empty parts in the middle of concat sequence are processed by the next `if`
            if (left == elements.begin() &&
                leftNondegenSt.has(NondegeneracyStatus::AcceptsOnlyEmpty))
                admitsNoMatch = true;

            // (seq ##0 empty) does not result in a match.
            if (rightNondegenSt.has(NondegeneracyStatus::AcceptsOnlyEmpty))
                admitsNoMatch = true;
        }

        if (right->delay.min > 1)
            admitsEmpty = false;

        ++left;
        leftNondegenSt = rightNondegenSt;
    }

    bitmask<NondegeneracyStatus> res;
    res = (admitsEmpty) ? res | NondegeneracyStatus::AdmitsEmpty : res;
    res = (admitsNoMatch) ? res | NondegeneracyStatus::AdmitsNoMatch : res;
    return res;
}

std::optional<SequenceRange> SequenceConcatExpr::computeSequenceLengthImpl() const {
    auto it = elements.begin();
    SLANG_ASSERT(it != elements.end());

    // Default delay length for concat sequence is 1 if it's admits not only empty matches.
    bool isAcceptsOnlyEmpty = it->sequence->checkNondegeneracy().has(
        NondegeneracyStatus::AcceptsOnlyEmpty);
    uint32_t delayMin = (isAcceptsOnlyEmpty) ? 0 : 1;
    uint32_t delayMax = delayMin;

    while (it != elements.end()) {
        // (empty ##n seq), where n is greater than 0, is equivalent to (##(n-1) seq).
        // also ((##n empty) ; (seq ##n empty)), where n is greater than 0, is equivalent to
        // ((##(n-1) `true) ; (seq ##(n-1) `true))
        delayMin += ((it->delay.min && isAcceptsOnlyEmpty) ? it->delay.min - 1 : it->delay.min);
        if (it->delay.max.has_value()) {
            const auto maxVal = it->delay.max.value();
            delayMax += ((maxVal && isAcceptsOnlyEmpty) ? maxVal - 1 : maxVal);
        }

        ++it;
        if (it != elements.end())
            isAcceptsOnlyEmpty = it->sequence->checkNondegeneracy().has(
                NondegeneracyStatus::AcceptsOnlyEmpty);
    }

    SequenceRange res;
    res.min = delayMin;
    res.max = delayMax;
    return res;
}

void SequenceConcatExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("elements");

    for (auto& elem : elements) {
        serializer.startObject();
        serializer.write("sequence", *elem.sequence);
        elem.delay.serializeTo(serializer);
        serializer.endObject();
    }

    serializer.endArray();
}

static std::span<const Expression* const> bindMatchItems(const SequenceMatchListSyntax& syntax,
                                                         const ASTContext& context,
                                                         const AssertionExpr& sequence) {
    auto checkLocalVar = [&](const Expression& expr) {
        auto sym = expr.getSymbolReference();
        if (!sym || sym->kind != SymbolKind::LocalAssertionVar)
            context.addDiag(diag::LocalVarMatchItem, expr.sourceRange);
    };

    ASTContext ctx = context;
    ctx.flags &= ~ASTFlags::AssignmentDisallowed;

    // If we are creating an argument, these "match items" might actually be part of
    // a comma-separated event expression. We need to avoid erroring in that case.
    // Just do the bare minimum to check the expressions here.
    if (ctx.flags.has(ASTFlags::AssertionInstanceArgCheck)) {
        for (auto item : syntax.items)
            AssertionExpr::bind(*item, ctx);
        return {};
    }

    SmallVector<const Expression*> results;
    for (auto item : syntax.items) {
        auto exprSyn = context.requireSimpleExpr(*item, diag::InvalidMatchItem);
        if (!exprSyn)
            continue;

        auto& expr = Expression::bind(*exprSyn, ctx, ASTFlags::AssignmentAllowed);
        results.push_back(&expr);

        switch (expr.kind) {
            case ExpressionKind::Assignment: {
                auto& assign = expr.as<AssignmentExpression>();
                checkLocalVar(assign.left());
                break;
            }
            case ExpressionKind::UnaryOp: {
                auto& unary = expr.as<UnaryExpression>();
                switch (unary.op) {
                    case UnaryOperator::Preincrement:
                    case UnaryOperator::Predecrement:
                    case UnaryOperator::Postincrement:
                    case UnaryOperator::Postdecrement:
                        checkLocalVar(unary.operand());
                        break;
                    default:
                        context.addDiag(diag::InvalidMatchItem, expr.sourceRange);
                        break;
                }
                break;
            }
            case ExpressionKind::Call: {
                AssertionExpr::checkAssertionCall(expr.as<CallExpression>(), context,
                                                  diag::SubroutineMatchOutArg,
                                                  diag::SubroutineMatchAutoRefArg,
                                                  diag::SubroutineMatchNonVoid, expr.sourceRange);
                break;
            }
            case ExpressionKind::Invalid:
                break;
            default:
                context.addDiag(diag::InvalidMatchItem, expr.sourceRange);
                break;
        }
    }

    if (sequence.checkNondegeneracy().has(NondegeneracyStatus::AdmitsEmpty)) {
        auto& diag = context.addDiag(diag::MatchItemsAdmitEmpty, syntax.items.sourceRange());
        if (sequence.syntax)
            diag << sequence.syntax->sourceRange();
    }

    return results.copy(context.getCompilation());
}

AssertionExpr& SequenceWithMatchExpr::fromSyntax(const ParenthesizedSequenceExprSyntax& syntax,
                                                 const ASTContext& context) {
    auto& expr = bind(*syntax.expr, context);
    expr.requireSequence(context);

    std::optional<SequenceRepetition> repetition;
    if (syntax.repetition) {
        repetition.emplace(*syntax.repetition, context);
        if (repetition->kind != SequenceRepetition::Consecutive)
            context.addDiag(diag::SeqInstanceRepetition, syntax.repetition->sourceRange());
    }

    std::span<const Expression* const> matchItems;
    if (syntax.matchList)
        matchItems = bindMatchItems(*syntax.matchList, context, expr);

    return *context.getCompilation().emplace<SequenceWithMatchExpr>(expr, repetition, matchItems);
}

bitmask<NondegeneracyStatus> SequenceWithMatchExpr::checkNondegeneracyImpl() const {
    bitmask<NondegeneracyStatus> res;

    if (repetition) {
        const auto seqRepEmpty = repetition->admitsEmpty();
        res = (seqRepEmpty == SequenceRepetition::AdmitsEmpty::Yes)
                  ? res | NondegeneracyStatus::AdmitsEmpty
                  : res;
        if (seqRepEmpty == SequenceRepetition::AdmitsEmpty::Only)
            res = res | NondegeneracyStatus::AcceptsOnlyEmpty | NondegeneracyStatus::AdmitsEmpty;
    }

    return res | expr.checkNondegeneracy();
}

void SequenceWithMatchExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
    if (repetition) {
        serializer.writeProperty("repetition");
        repetition->serializeTo(serializer);
    }

    serializer.startArray("matchItems");
    for (auto item : matchItems)
        serializer.serialize(*item);
    serializer.endArray();
}

static UnaryAssertionOperator getUnaryOp(TokenKind kind) {
    // clang-format off
    switch (kind) {
        case TokenKind::NotKeyword: return UnaryAssertionOperator::Not;
        case TokenKind::NextTimeKeyword: return UnaryAssertionOperator::NextTime;
        case TokenKind::SNextTimeKeyword: return UnaryAssertionOperator::SNextTime;
        case TokenKind::AlwaysKeyword: return UnaryAssertionOperator::Always;
        case TokenKind::SAlwaysKeyword: return UnaryAssertionOperator::SAlways;
        case TokenKind::EventuallyKeyword: return UnaryAssertionOperator::Eventually;
        case TokenKind::SEventuallyKeyword: return UnaryAssertionOperator::SEventually;
        default: SLANG_UNREACHABLE;
    }
    // clang-format on
}

static bool isNegationOp(UnaryAssertionOperator op) {
    switch (op) {
        case UnaryAssertionOperator::Not:
        case UnaryAssertionOperator::SAlways:
        case UnaryAssertionOperator::SEventually:
        case UnaryAssertionOperator::SNextTime:
            return true;
        default:
            return false;
    }
}

AssertionExpr& UnaryAssertionExpr::fromSyntax(const UnaryPropertyExprSyntax& syntax,
                                              const ASTContext& context) {
    auto op = getUnaryOp(syntax.op.kind);

    bitmask<ASTFlags> extraFlags;
    if (op == UnaryAssertionOperator::NextTime)
        extraFlags = ASTFlags::PropertyTimeAdvance;
    else if (isNegationOp(op))
        extraFlags = ASTFlags::PropertyNegation;

    auto& comp = context.getCompilation();
    auto& expr = bind(*syntax.expr, context.resetFlags(extraFlags));
    return *comp.emplace<UnaryAssertionExpr>(op, expr, std::nullopt);
}

AssertionExpr& UnaryAssertionExpr::fromSyntax(const UnarySelectPropertyExprSyntax& syntax,
                                              const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto op = getUnaryOp(syntax.op.kind);

    std::optional<SequenceRange> range;
    if (syntax.selector) {
        bool allowUnbounded = op == UnaryAssertionOperator::Always ||
                              op == UnaryAssertionOperator::SEventually;
        range = SequenceRange::fromSyntax(*syntax.selector, context, allowUnbounded);
    }

    bitmask<ASTFlags> extraFlags;
    if ((op == UnaryAssertionOperator::Always || op == UnaryAssertionOperator::NextTime ||
         op == UnaryAssertionOperator::Eventually) &&
        range && range->min > 0) {
        extraFlags = ASTFlags::PropertyTimeAdvance;
    }
    else if (isNegationOp(op)) {
        extraFlags = ASTFlags::PropertyNegation;
    }

    auto& expr = bind(*syntax.expr, context.resetFlags(extraFlags));

    return *comp.emplace<UnaryAssertionExpr>(op, expr, range);
}

void UnaryAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("op", toString(op));
    serializer.write("expr", expr);
    if (range)
        range->serializeTo(serializer);
}

AssertionExpr& BinaryAssertionExpr::fromSyntax(const BinarySequenceExprSyntax& syntax,
                                               const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& left = bind(*syntax.left, context);
    auto& right = bind(*syntax.right, context);

    // clang-format off
    BinaryAssertionOperator op;
    switch (syntax.kind) {
        case SyntaxKind::AndSequenceExpr: op = BinaryAssertionOperator::And; break;
        case SyntaxKind::OrSequenceExpr: op = BinaryAssertionOperator::Or; break;
        case SyntaxKind::IntersectSequenceExpr: op = BinaryAssertionOperator::Intersect; break;
        case SyntaxKind::ThroughoutSequenceExpr: op = BinaryAssertionOperator::Throughout; break;
        case SyntaxKind::WithinSequenceExpr: op = BinaryAssertionOperator::Within; break;
        default: SLANG_UNREACHABLE;
    }
    // clang-format on

    if (op == BinaryAssertionOperator::Throughout) {
        auto check = [&] {
            if (left.kind != AssertionExprKind::Simple)
                return false;

            auto& simple = left.as<SimpleAssertionExpr>();
            if (simple.repetition)
                return false;

            return simple.expr.kind != ExpressionKind::AssertionInstance;
        };

        if (!check()) {
            context.addDiag(diag::ThroughoutLhsInvalid, syntax.left->sourceRange())
                << syntax.op.range();
        }
        right.requireSequence(context);
    }
    else if (op != BinaryAssertionOperator::And && op != BinaryAssertionOperator::Or) {
        // The 'and' and 'or' operators may just be simple property references,
        // which is fine unless someone up above us decides they need sequences only.
        left.requireSequence(context);
        right.requireSequence(context);
    }

    return *comp.emplace<BinaryAssertionExpr>(op, left, right);
}

AssertionExpr& BinaryAssertionExpr::fromSyntax(const BinaryPropertyExprSyntax& syntax,
                                               const ASTContext& context) {
    // The followed-by operators are the duals of the implication operators. So implication
    // nondegeneracy check rules are also applyed to it. Therefore, sequence_expr #-# property_expr
    // is equivalent to the following: `not (sequence_expr |-> not property_expr)`
    bool isOverlapImplOrHashMinus = (syntax.op.kind == TokenKind::OrMinusArrow) ||
                                    (syntax.op.kind == TokenKind::HashMinusHash);
    // sequence_expr #=# property_expr is equivalent to the following:
    // not (sequence_expr |=> not property_expr)
    bool isNonOverlapImplOrHashEq = (syntax.op.kind == TokenKind::OrEqualsArrow) ||
                                    (syntax.op.kind == TokenKind::HashEqualsHash);

    bitmask<ASTFlags> lflags, rflags;
    if (isNonOverlapImplOrHashEq) {
        rflags = ASTFlags::PropertyTimeAdvance;
    }
    else if (syntax.kind == SyntaxKind::SUntilPropertyExpr ||
             syntax.kind == SyntaxKind::SUntilWithPropertyExpr) {
        lflags = rflags = ASTFlags::PropertyNegation;
    }

    NondegeneracyFlags nondegFlags = (isOverlapImplOrHashMinus)
                                         ? NondegeneracyFlags::IsOverlapImplOrHashMinus
                                         : NondegeneracyFlags::None;
    nondegFlags = (isNonOverlapImplOrHashEq) ? NondegeneracyFlags::IsNonOverlapImplOrHashEq
                                             : nondegFlags;

    auto& comp = context.getCompilation();
    auto& left = bind(*syntax.left, context.resetFlags(lflags), false, nondegFlags);
    auto& right = bind(*syntax.right, context.resetFlags(rflags));

    // clang-format off
    BinaryAssertionOperator op;
    switch (syntax.kind) {
        case SyntaxKind::AndPropertyExpr: op = BinaryAssertionOperator::And; break;
        case SyntaxKind::OrPropertyExpr: op = BinaryAssertionOperator::Or; break;
        case SyntaxKind::IffPropertyExpr: op = BinaryAssertionOperator::Iff; break;
        case SyntaxKind::UntilPropertyExpr: op = BinaryAssertionOperator::Until; break;
        case SyntaxKind::SUntilPropertyExpr: op = BinaryAssertionOperator::SUntil; break;
        case SyntaxKind::UntilWithPropertyExpr: op = BinaryAssertionOperator::UntilWith; break;
        case SyntaxKind::SUntilWithPropertyExpr: op = BinaryAssertionOperator::SUntilWith; break;
        case SyntaxKind::ImpliesPropertyExpr: op = BinaryAssertionOperator::Implies; break;
        case SyntaxKind::ImplicationPropertyExpr:
            left.requireSequence(context, diag::PropertyLhsInvalid);
            op = syntax.op.kind == TokenKind::OrMinusArrow ? BinaryAssertionOperator::OverlappedImplication :
                                                             BinaryAssertionOperator::NonOverlappedImplication;
            break;
        case SyntaxKind::FollowedByPropertyExpr:
            left.requireSequence(context, diag::PropertyLhsInvalid);
            op = syntax.op.kind == TokenKind::HashMinusHash ? BinaryAssertionOperator::OverlappedFollowedBy :
                                                              BinaryAssertionOperator::NonOverlappedFollowedBy;
            break;
        default:
            SLANG_UNREACHABLE;
    }
    // clang-format on

    return *comp.emplace<BinaryAssertionExpr>(op, left, right);
}

void BinaryAssertionExpr::requireSequence(const ASTContext& context, DiagCode code) const {
    switch (op) {
        case BinaryAssertionOperator::And:
        case BinaryAssertionOperator::Or:
            left.requireSequence(context, code);
            right.requireSequence(context, code);
            return;
        case BinaryAssertionOperator::Intersect:
        case BinaryAssertionOperator::Throughout:
        case BinaryAssertionOperator::Within:
            return;
        case BinaryAssertionOperator::Iff:
        case BinaryAssertionOperator::Until:
        case BinaryAssertionOperator::SUntil:
        case BinaryAssertionOperator::UntilWith:
        case BinaryAssertionOperator::SUntilWith:
        case BinaryAssertionOperator::Implies:
        case BinaryAssertionOperator::OverlappedImplication:
        case BinaryAssertionOperator::NonOverlappedImplication:
        case BinaryAssertionOperator::OverlappedFollowedBy:
        case BinaryAssertionOperator::NonOverlappedFollowedBy:
            SLANG_ASSERT(syntax);
            context.addDiag(code, syntax->sourceRange());
            return;
    }
    SLANG_UNREACHABLE;
}

bitmask<NondegeneracyStatus> BinaryAssertionExpr::checkNondegeneracyImpl() const {
    bitmask<NondegeneracyStatus> res;
    const auto leftNondegenSt = left.checkNondegeneracy();
    const auto rightNondegenSt = right.checkNondegeneracy();
    bool leftAdmitsEmpty = leftNondegenSt.has(NondegeneracyStatus::AdmitsEmpty);
    bool rightAdmitsEmpty = rightNondegenSt.has(NondegeneracyStatus::AdmitsEmpty);
    bool leftAdmitsNoMatch = leftNondegenSt.has(NondegeneracyStatus::AdmitsNoMatch);
    bool rightAdmitsNoMatch = rightNondegenSt.has(NondegeneracyStatus::AdmitsNoMatch);

    switch (op) {
        case BinaryAssertionOperator::Or: {
            res = (leftAdmitsEmpty || rightAdmitsEmpty) ? res | NondegeneracyStatus::AdmitsEmpty
                                                        : res;

            // In case of `or` full sequence is no match if and only if both parts are no match
            res = (leftAdmitsNoMatch && rightAdmitsNoMatch)
                      ? res | NondegeneracyStatus::AdmitsNoMatch
                      : res;
            break;
        }
        case BinaryAssertionOperator::And: {
            res = (leftAdmitsEmpty && rightAdmitsEmpty) ? res | NondegeneracyStatus::AdmitsEmpty
                                                        : res;

            // In case of `and` full sequence is no match if and only if any part is no match
            res = (leftAdmitsNoMatch || rightAdmitsNoMatch)
                      ? res | NondegeneracyStatus::AdmitsNoMatch
                      : res;
            break;
        }
        case BinaryAssertionOperator::Intersect: {
            res = (leftAdmitsEmpty && rightAdmitsEmpty) ? res | NondegeneracyStatus::AdmitsEmpty
                                                        : res;

            const auto leftLen = left.computeSequenceLength();
            const auto rightLen = right.computeSequenceLength();

            // In case of `intersect` full sequence is no match if both parts aren't have any
            // possible equal delay range
            res = (leftAdmitsNoMatch || rightAdmitsNoMatch || !leftLen.has_value() ||
                   !rightLen.has_value() || !leftLen.value().isIntersect(rightLen.value()))
                      ? res | NondegeneracyStatus::AdmitsNoMatch
                      : res;
            break;
        }
        case BinaryAssertionOperator::Within: {
            res = (leftAdmitsEmpty && rightAdmitsEmpty) ? res | NondegeneracyStatus::AdmitsEmpty
                                                        : res;

            const auto leftLen = left.computeSequenceLength();
            const auto rightLen = right.computeSequenceLength();

            // In case of `within` full sequence is no match if left part delay range is within
            // right part delay range
            res = (leftAdmitsNoMatch || rightAdmitsNoMatch || !leftLen.has_value() ||
                   !rightLen.has_value() || !leftLen.value().isWithin(rightLen.value()))
                      ? res | NondegeneracyStatus::AdmitsNoMatch
                      : res;
            break;
        }
        case BinaryAssertionOperator::Throughout: {
            res = (rightAdmitsEmpty) ? res | NondegeneracyStatus::AdmitsEmpty : res;

            // In case of `throughout` full sequence is no match if right part is no match
            res = (rightAdmitsNoMatch) ? res | NondegeneracyStatus::AdmitsNoMatch : res;
            break;
        }
        default:
            break;
    }

    return res;
};

std::optional<SequenceRange> BinaryAssertionExpr::computeSequenceLengthImpl() const {
    if (op == BinaryAssertionOperator::Throughout)
        return right.computeSequenceLength();

    const auto leftLen = left.computeSequenceLength();
    const auto rightLen = right.computeSequenceLength();
    if (leftLen.has_value() && rightLen.has_value()) {
        const auto leftLenVal = leftLen.value();
        const auto rightLenVal = rightLen.value();
        return (rightLenVal < leftLenVal) ? leftLenVal : rightLenVal;
    }
    else if (leftLen.has_value()) {
        return leftLen.value();
    }
    else if (rightLen.has_value()) {
        return rightLen.value();
    }

    return std::nullopt;
}

void BinaryAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("op", toString(op));
    serializer.write("left", left);
    serializer.write("right", right);
}

AssertionExpr& FirstMatchAssertionExpr::fromSyntax(const FirstMatchSequenceExprSyntax& syntax,
                                                   const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& seq = bind(*syntax.expr, context);
    seq.requireSequence(context);

    std::span<const Expression* const> matchItems;
    if (syntax.matchList)
        matchItems = bindMatchItems(*syntax.matchList, context, seq);

    return *comp.emplace<FirstMatchAssertionExpr>(seq, matchItems);
}

bitmask<NondegeneracyStatus> FirstMatchAssertionExpr::checkNondegeneracyImpl() const {
    auto res = seq.checkNondegeneracy();
    if (!matchItems.empty()) {
        // Clear `admitEmpty` and `acceptOnlyEmpty` bits
        res = (res.has(NondegeneracyStatus::AdmitsNoMatch)) ? NondegeneracyStatus::AdmitsNoMatch
                                                            : NondegeneracyStatus::None;
    }

    return res;
}

void FirstMatchAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("seq", seq);

    serializer.startArray("matchItems");
    for (auto item : matchItems)
        serializer.serialize(*item);
    serializer.endArray();
}

AssertionExpr& ClockingAssertionExpr::fromSyntax(const ClockingSequenceExprSyntax& syntax,
                                                 const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& clocking = TimingControl::bind(*syntax.event,
                                         context.resetFlags(ASTFlags::NonProcedural));
    auto& expr = bind(*syntax.expr, context);
    return *comp.emplace<ClockingAssertionExpr>(clocking, expr);
}

AssertionExpr& ClockingAssertionExpr::fromSyntax(const ClockingPropertyExprSyntax& syntax,
                                                 const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& clocking = TimingControl::bind(*syntax.event,
                                         context.resetFlags(ASTFlags::NonProcedural));

    if (!syntax.expr) {
        auto last = syntax.getLastToken();
        context.addDiag(diag::ExpectedExpression, last.location() + last.rawText().length());
        return badExpr(comp, nullptr);
    }

    auto& expr = bind(*syntax.expr, context);
    return *comp.emplace<ClockingAssertionExpr>(clocking, expr);
}

AssertionExpr& ClockingAssertionExpr::fromSyntax(const SignalEventExpressionSyntax& syntax,
                                                 const ASTContext& context) {
    // If we are creating an argument then assume it's possible it could be used in an
    // event expression and allow this. Actual usage later on will report an error if
    // this ends up not being true. Otherwise this is just an error.
    auto& comp = context.getCompilation();
    if (!context.flags.has(ASTFlags::AssertionInstanceArgCheck)) {
        context.addDiag(diag::InvalidSignalEventInSeq, syntax.sourceRange());
        return badExpr(comp, nullptr);
    }

    auto& clocking = TimingControl::bind(syntax, context.resetFlags(ASTFlags::NonProcedural));
    return *comp.emplace<ClockingAssertionExpr>(clocking, badExpr(comp, nullptr));
}

AssertionExpr& ClockingAssertionExpr::fromSyntax(const TimingControlSyntax& syntax,
                                                 const AssertionExpr& expr,
                                                 const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& clocking = TimingControl::bind(syntax, context.resetFlags(ASTFlags::NonProcedural));
    return *comp.emplace<ClockingAssertionExpr>(clocking, expr);
}

bitmask<NondegeneracyStatus> ClockingAssertionExpr::checkNondegeneracyImpl() const {
    return expr.checkNondegeneracy();
}

void ClockingAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("clocking", clocking);
    serializer.write("expr", expr);
}

AssertionExpr& StrongWeakAssertionExpr::fromSyntax(const StrongWeakPropertyExprSyntax& syntax,
                                                   const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& expr = bind(*syntax.expr, context);
    expr.requireSequence(context);

    // Any sequence that is used as a property shall be nondegenerate and shall not admit
    // any empty match.
    const auto seqNondegenSt = expr.checkNondegeneracy();
    bool isSeqAdmitsEmpty = seqNondegenSt.has(NondegeneracyStatus::AdmitsEmpty);
    bool isSeqAdmitsNoMatch = seqNondegenSt.has(NondegeneracyStatus::AdmitsNoMatch);
    if (isSeqAdmitsEmpty || isSeqAdmitsNoMatch) {
        auto& diag = context.addDiag(diag::SeqPropNondegenerate, syntax.sourceRange());
        diag.addNote((isSeqAdmitsEmpty) ? diag::SeqAdmitsEmptyMatches : diag::SeqAdmitsNoMatches,
                     syntax.expr->sourceRange());
    }

    return *comp.emplace<StrongWeakAssertionExpr>(
        expr, syntax.keyword.kind == TokenKind::StrongKeyword ? Strong : Weak);
}

void StrongWeakAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
    serializer.write("strength", strength == Strong ? "strong"sv : "weak"sv);
}

AssertionExpr& AbortAssertionExpr::fromSyntax(const AcceptOnPropertyExprSyntax& syntax,
                                              const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& cond = bindExpr(*syntax.condition, context);
    auto& expr = bind(*syntax.expr, context);

    Action action;
    bool isSync;
    switch (syntax.keyword.kind) {
        case TokenKind::AcceptOnKeyword:
            action = Accept;
            isSync = false;
            break;
        case TokenKind::SyncAcceptOnKeyword:
            action = Accept;
            isSync = true;
            break;
        case TokenKind::RejectOnKeyword:
            action = Reject;
            isSync = false;
            break;
        case TokenKind::SyncRejectOnKeyword:
            action = Reject;
            isSync = true;
            break;
        default:
            SLANG_UNREACHABLE;
    }

    checkSampledValueExpr(cond, context, false, diag::PropAbortLocalVar, diag::PropAbortMatched);

    return *comp.emplace<AbortAssertionExpr>(cond, expr, action, isSync);
}

void AbortAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("condition", condition);
    serializer.write("expr", expr);
    serializer.write("action", action == Accept ? "accept"sv : "reject"sv);
    serializer.write("isSync", isSync);
}

std::optional<SequenceRange> ConditionalAssertionExpr::computeSequenceLengthImpl() const {
    if (checkNondegeneracy().has(NondegeneracyStatus::AdmitsNoMatch))
        return std::nullopt;

    std::optional<SequenceRange> max;
    if (const auto ifLen = ifExpr.computeSequenceLength(); ifLen.has_value())
        max = ifLen.value();

    if (elseExpr) {
        if (const auto elseLen = elseExpr->computeSequenceLength(); elseLen.has_value()) {
            if (const auto elseLenVal = elseLen.value(); !max.has_value() || max < elseLenVal)
                max = elseLenVal;
        }
    }

    return max;
}

AssertionExpr& ConditionalAssertionExpr::fromSyntax(const ConditionalPropertyExprSyntax& syntax,
                                                    const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& cond = bindExpr(*syntax.condition, context);
    auto& ifExpr = bind(*syntax.expr, context);

    const AssertionExpr* elseExpr = nullptr;
    if (syntax.elseClause)
        elseExpr = &bind(*syntax.elseClause->expr, context);

    // If condition can be evaluated only as `false` (`0`) than sequence property
    // is no match
    if (!elseExpr) {
        if (const auto evaluatedValue = context.tryEval(cond);
            evaluatedValue.isInteger() && !evaluatedValue.isTrue()) {
            auto& diag = context.addDiag(diag::SeqPropNondegenerate, syntax.sourceRange());
            diag.addNote(diag::SeqPropCondAlwaysFalse, cond.sourceRange);
        }
    }

    return *comp.emplace<ConditionalAssertionExpr>(cond, ifExpr, elseExpr);
}

void ConditionalAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("condition", condition);
    serializer.write("if", ifExpr);
    if (elseExpr)
        serializer.write("else", *elseExpr);
}

std::optional<SequenceRange> CaseAssertionExpr::computeSequenceLengthImpl() const {
    std::optional<SequenceRange> max;
    for (const auto& item : items) {
        if (const auto itemLen = item.body->computeSequenceLength(); itemLen.has_value()) {
            if (const auto itemLenVal = itemLen.value(); !max.has_value() || max < itemLenVal)
                max = itemLenVal;
        }
    }

    if (defaultCase) {
        if (const auto defaultItemLen = defaultCase->computeSequenceLength();
            defaultItemLen.has_value()) {
            if (const auto defaultItemLenVal = defaultItemLen.value();
                !max.has_value() || max < defaultItemLenVal)
                max = defaultItemLenVal;
        }
    }

    return max;
};

AssertionExpr& CaseAssertionExpr::fromSyntax(const CasePropertyExprSyntax& syntax,
                                             const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& expr = bindExpr(*syntax.expr, context);

    const AssertionExpr* defCase = nullptr;
    SmallVector<ItemGroup, 4> items;
    for (auto item : syntax.items) {
        if (item->kind == SyntaxKind::StandardPropertyCaseItem) {
            auto& sci = item->as<StandardPropertyCaseItemSyntax>();
            auto& body = AssertionExpr::bind(*sci.expr, context);

            SmallVector<const Expression*> exprs;
            for (auto es : sci.expressions)
                exprs.push_back(&bindExpr(*es, context));

            items.push_back(ItemGroup{exprs.copy(comp), &body});
        }
        else {
            // The parser already errored for duplicate defaults,
            // so just ignore if it happens here.
            if (!defCase) {
                defCase = &AssertionExpr::bind(*item->as<DefaultPropertyCaseItemSyntax>().expr,
                                               context);
            }
        }
    }

    return *comp.emplace<CaseAssertionExpr>(expr, items.copy(comp), defCase);
}

void CaseAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);

    serializer.startArray("items");
    for (auto const& item : items) {
        serializer.startObject();

        serializer.startArray("expressions");
        for (auto ex : item.expressions)
            serializer.serialize(*ex);
        serializer.endArray();

        serializer.write("body", *item.body);

        serializer.endObject();
    }
    serializer.endArray();

    if (defaultCase)
        serializer.write("defaultCase", *defaultCase);
}

std::optional<SequenceRange> DisableIffAssertionExpr::computeSequenceLengthImpl() const {
    if (condition.constant && condition.constant->isTrue())
        return std::nullopt;

    return expr.computeSequenceLength();
}

AssertionExpr& DisableIffAssertionExpr::fromSyntax(const DisableIffSyntax& syntax,
                                                   const AssertionExpr& expr,
                                                   const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& cond = bindExpr(*syntax.expr, context);

    checkSampledValueExpr(cond, context, false, diag::DisableIffLocalVar, diag::DisableIffMatched);

    // If condition of `disable iff` can be evaluated only as `true` (`1`) than sequence property
    // is no match
    if (context.tryEval(cond).isTrue()) {
        auto& diag = context.addDiag(diag::SeqPropNondegenerate, syntax.sourceRange());
        diag.addNote(diag::DisableIffCondAlwaysTrue, cond.sourceRange);
    }

    if (context.assertionInstance && context.assertionInstance->isRecursive)
        context.addDiag(diag::RecursivePropDisableIff, syntax.sourceRange());

    return *comp.emplace<DisableIffAssertionExpr>(cond, expr);
}

void DisableIffAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("condition", condition);
    serializer.write("expr", expr);
}

} // namespace slang::ast
