//------------------------------------------------------------------------------
// AssertionExpr.cpp
// Assertion expression creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/AssertionExpr.h"

#include "slang/binding/AssignmentExpressions.h"
#include "slang/binding/BindContext.h"
#include "slang/binding/Expression.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/binding/OperatorExpressions.h"
#include "slang/binding/TimingControl.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/Type.h"

namespace slang {

static const Expression& bindExpr(const ExpressionSyntax& syntax, const BindContext& context,
                                  bool allowInstances = false) {
    auto& expr = Expression::bind(syntax, context, BindFlags::AssertionExpr);
    if (expr.bad())
        return expr;

    if (allowInstances && (expr.type->isSequenceType() || expr.type->isPropertyType()))
        return expr;

    if (!expr.type->isValidForSequence()) {
        auto& comp = context.getCompilation();
        context.addDiag(diag::AssertionExprType, expr.sourceRange) << *expr.type;
        return *comp.emplace<InvalidExpression>(&expr, comp.getErrorType());
    }

    return expr;
}

const AssertionExpr& AssertionExpr::bind(const SequenceExprSyntax& syntax,
                                         const BindContext& context) {
    BindContext ctx(context);
    ctx.flags |= BindFlags::AssignmentDisallowed;

    AssertionExpr* result;
    switch (syntax.kind) {
        case SyntaxKind::SimpleSequenceExpr:
            result = &SimpleAssertionExpr::fromSyntax(syntax.as<SimpleSequenceExprSyntax>(), ctx);
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
            result =
                &ClockingAssertionExpr::fromSyntax(syntax.as<ClockingSequenceExprSyntax>(), ctx);
            break;
        case SyntaxKind::SignalEventExpression:
            result =
                &ClockingAssertionExpr::fromSyntax(syntax.as<SignalEventExpressionSyntax>(), ctx);
            break;
        default:
            THROW_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

const AssertionExpr& AssertionExpr::bind(const PropertyExprSyntax& syntax,
                                         const BindContext& context) {
    BindContext ctx(context);
    ctx.flags |= BindFlags::AssignmentDisallowed;

    AssertionExpr* result;
    switch (syntax.kind) {
        case SyntaxKind::SimplePropertyExpr:
            // Just a simple passthrough to binding the sequence expression
            // contained within.
            return bind(*syntax.as<SimplePropertyExprSyntax>().expr, context);
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
                if (ctx.flags.has(BindFlags::AssertionInstanceArgCheck)) {
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
            result =
                &ClockingAssertionExpr::fromSyntax(syntax.as<ClockingPropertyExprSyntax>(), ctx);
            break;
        case SyntaxKind::StrongWeakPropertyExpr:
            result = &StrongWeakAssertionExpr::fromSyntax(syntax.as<StrongWeakPropertyExprSyntax>(),
                                                          ctx);
            break;
        case SyntaxKind::UnaryPropertyExpr:
            result = &UnaryAssertionExpr::fromSyntax(syntax.as<UnaryPropertyExprSyntax>(), ctx);
            break;
        case SyntaxKind::UnarySelectPropertyExpr:
            result =
                &UnaryAssertionExpr::fromSyntax(syntax.as<UnarySelectPropertyExprSyntax>(), ctx);
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
            THROW_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

void AssertionExpr::requireSequence(const BindContext& context) const {
    requireSequence(context, diag::PropExprInSequence);
}

void AssertionExpr::requireSequence(const BindContext& context, DiagCode code) const {
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
            ASSERT(syntax);
            context.addDiag(code, syntax->sourceRange());
            return;
        case AssertionExprKind::SequenceConcat:
        case AssertionExprKind::SequenceWithMatch:
        case AssertionExprKind::FirstMatch:
        case AssertionExprKind::Invalid:
            return;
    }
    THROW_UNREACHABLE;
}

AssertionExpr& AssertionExpr::badExpr(Compilation& compilation, const AssertionExpr* expr) {
    return *compilation.emplace<InvalidAssertionExpr>(expr);
}

void InvalidAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    if (child)
        serializer.write("child", *child);
}

SequenceRange SequenceRange::fromSyntax(const SelectorSyntax& syntax, const BindContext& context,
                                        bool allowUnbounded) {
    if (syntax.kind == SyntaxKind::BitSelect) {
        SequenceRange range;
        auto val = context.evalInteger(*syntax.as<BitSelectSyntax>().expr);
        if (context.requirePositive(val, syntax.sourceRange()))
            range.max = range.min = uint32_t(*val);

        return range;
    }
    else {
        auto& rs = syntax.as<RangeSelectSyntax>();
        return fromSyntax(rs, context, allowUnbounded);
    }
}

SequenceRange SequenceRange::fromSyntax(const RangeSelectSyntax& syntax, const BindContext& context,
                                        bool allowUnbounded) {
    SequenceRange range;
    auto l = context.evalInteger(*syntax.left);
    if (context.requirePositive(l, syntax.left->sourceRange()))
        range.min = uint32_t(*l);

    // The rhs can be an unbounded '$' so we need extra bind flags.
    bitmask<BindFlags> flags = BindFlags::AssertionExpr;
    if (allowUnbounded)
        flags |= BindFlags::AllowUnboundedLiteral;

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

SequenceRepetition::SequenceRepetition(const SequenceRepetitionSyntax& syntax,
                                       const BindContext& context) {
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
                                               const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& expr = bindExpr(*syntax.expr, context, /* allowInstances */ true);

    optional<SequenceRepetition> repetition;
    if (syntax.repetition) {
        repetition.emplace(*syntax.repetition, context);

        if (expr.kind == ExpressionKind::AssertionInstance) {
            if (expr.type->isPropertyType())
                context.addDiag(diag::PropInstanceRepetition, syntax.repetition->sourceRange());
            else if (repetition->kind != SequenceRepetition::Consecutive)
                context.addDiag(diag::SeqInstanceRepetition, syntax.repetition->sourceRange());
        }
    }

    return *comp.emplace<SimpleAssertionExpr>(expr, repetition);
}

void SimpleAssertionExpr::requireSequence(const BindContext& context, DiagCode code) const {
    if (expr.kind == ExpressionKind::AssertionInstance) {
        auto& aie = expr.as<AssertionInstanceExpression>();
        if (aie.type->isPropertyType()) {
            ASSERT(syntax);
            context.addDiag(code, syntax->sourceRange());
            return;
        }

        aie.body.requireSequence(context, code);
    }
}

void SimpleAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
    if (repetition) {
        serializer.writeProperty("repetition");
        repetition->serializeTo(serializer);
    }
}

AssertionExpr& SequenceConcatExpr::fromSyntax(const DelayedSequenceExprSyntax& syntax,
                                              const BindContext& context) {
    bool ok = true;
    SmallVectorSized<Element, 8> elems;
    if (syntax.first) {
        auto& seq = bind(*syntax.first, context);
        ok &= !seq.bad();

        SequenceRange delay{ 0, 0 };
        elems.append(Element{ delay, &seq });
    }

    for (auto es : syntax.elements) {
        SequenceRange delay;
        auto& seq = bind(*es->expr, context);
        ok &= !seq.bad();

        if (es->delayVal) {
            auto val = context.evalInteger(*es->delayVal);
            if (!context.requirePositive(val, es->delayVal->sourceRange()))
                ok = false;
            else
                delay.max = delay.min = uint32_t(*val);
        }
        else if (es->range && es->range->kind == SyntaxKind::SimpleRangeSelect) {
            delay = SequenceRange::fromSyntax(es->range->as<RangeSelectSyntax>(), context,
                                              /* allowUnbounded */ true);
        }
        else if (es->op.kind == TokenKind::Plus) {
            delay.min = 1;
        }

        elems.append(Element{ delay, &seq });
    }

    auto& comp = context.getCompilation();
    auto result = comp.emplace<SequenceConcatExpr>(elems.copy(comp));
    if (!ok)
        return badExpr(comp, result);

    return *result;
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

static span<const Expression* const> bindMatchItems(const SequenceMatchListSyntax& syntax,
                                                    const BindContext& context) {
    auto checkLocalVar = [&](const Expression& expr) {
        auto sym = expr.getSymbolReference();
        if (!sym || sym->kind != SymbolKind::Variable ||
            !sym->as<VariableSymbol>().isLocalAssertionVar) {
            context.addDiag(diag::LocalVarMatchItem, expr.sourceRange);
        }
    };

    BindContext ctx = context;
    ctx.flags &= ~BindFlags::AssignmentDisallowed;
    ctx.flags |= BindFlags::AssertionExpr;

    // If we are binding an argument, these "match items" might actually be part of
    // a comma-separated event expression. We need to avoid erroring in that case.
    // Just do the bare minimum to check the expressions here.
    if (ctx.flags.has(BindFlags::AssertionInstanceArgCheck)) {
        for (auto item : syntax.items)
            AssertionExpr::bind(*item, ctx);
        return {};
    }

    SmallVectorSized<const Expression*, 4> results;
    for (auto item : syntax.items) {
        auto exprSyn = context.requireSimpleExpr(*item, diag::InvalidMatchItem);
        if (!exprSyn)
            continue;

        auto& expr = Expression::bind(*exprSyn, ctx, BindFlags::AssignmentAllowed);
        results.append(&expr);

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
            case ExpressionKind::Call:
                // TODO:
                break;
            case ExpressionKind::Invalid:
                break;
            default:
                context.addDiag(diag::InvalidMatchItem, expr.sourceRange);
                break;
        }
    }

    return results.copy(context.getCompilation());
}

AssertionExpr& SequenceWithMatchExpr::fromSyntax(const ParenthesizedSequenceExprSyntax& syntax,
                                                 const BindContext& context) {
    auto& expr = bind(*syntax.expr, context);

    optional<SequenceRepetition> repetition;
    if (syntax.repetition) {
        repetition.emplace(*syntax.repetition, context);
        if (repetition->kind != SequenceRepetition::Consecutive)
            context.addDiag(diag::SeqInstanceRepetition, syntax.repetition->sourceRange());
    }

    span<const Expression* const> matchItems;
    if (syntax.matchList)
        matchItems = bindMatchItems(*syntax.matchList, context);

    return *context.getCompilation().emplace<SequenceWithMatchExpr>(expr, repetition, matchItems);
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
        default: THROW_UNREACHABLE;
    }
    // clang-format on
}

AssertionExpr& UnaryAssertionExpr::fromSyntax(const UnaryPropertyExprSyntax& syntax,
                                              const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& expr = bind(*syntax.expr, context);
    return *comp.emplace<UnaryAssertionExpr>(getUnaryOp(syntax.op.kind), expr, std::nullopt);
}

AssertionExpr& UnaryAssertionExpr::fromSyntax(const UnarySelectPropertyExprSyntax& syntax,
                                              const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& expr = bind(*syntax.expr, context);
    auto op = getUnaryOp(syntax.op.kind);

    optional<SequenceRange> range;
    if (syntax.selector) {
        bool allowUnbounded =
            op == UnaryAssertionOperator::Always || op == UnaryAssertionOperator::SEventually;
        range = SequenceRange::fromSyntax(*syntax.selector, context, allowUnbounded);
    }

    return *comp.emplace<UnaryAssertionExpr>(op, expr, range);
}

void UnaryAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("op", toString(op));
    serializer.write("expr", expr);
    if (range)
        range->serializeTo(serializer);
}

AssertionExpr& BinaryAssertionExpr::fromSyntax(const BinarySequenceExprSyntax& syntax,
                                               const BindContext& context) {
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
        default: THROW_UNREACHABLE;
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
    }

    return *comp.emplace<BinaryAssertionExpr>(op, left, right);
}

AssertionExpr& BinaryAssertionExpr::fromSyntax(const BinaryPropertyExprSyntax& syntax,
                                               const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& left = bind(*syntax.left, context);
    auto& right = bind(*syntax.right, context);

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
            THROW_UNREACHABLE;
    }
    // clang-format on

    return *comp.emplace<BinaryAssertionExpr>(op, left, right);
}

void BinaryAssertionExpr::requireSequence(const BindContext& context, DiagCode code) const {
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
            ASSERT(syntax);
            context.addDiag(code, syntax->sourceRange());
            return;
    }
    THROW_UNREACHABLE;
}

void BinaryAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("op", toString(op));
    serializer.write("left", left);
    serializer.write("right", right);
}

AssertionExpr& FirstMatchAssertionExpr::fromSyntax(const FirstMatchSequenceExprSyntax& syntax,
                                                   const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& seq = bind(*syntax.expr, context);

    span<const Expression* const> matchItems;
    if (syntax.matchList)
        matchItems = bindMatchItems(*syntax.matchList, context);

    return *comp.emplace<FirstMatchAssertionExpr>(seq, matchItems);
}

void FirstMatchAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("seq", seq);

    serializer.startArray("matchItems");
    for (auto item : matchItems)
        serializer.serialize(*item);
    serializer.endArray();
}

AssertionExpr& ClockingAssertionExpr::fromSyntax(const ClockingSequenceExprSyntax& syntax,
                                                 const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& clocking = TimingControl::bind(*syntax.event, context);
    auto& expr = bind(*syntax.expr, context);
    return *comp.emplace<ClockingAssertionExpr>(clocking, expr);
}

AssertionExpr& ClockingAssertionExpr::fromSyntax(const ClockingPropertyExprSyntax& syntax,
                                                 const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& clocking = TimingControl::bind(*syntax.event, context);

    if (!syntax.expr) {
        auto last = syntax.getLastToken();
        context.addDiag(diag::ExpectedExpression, last.location() + last.rawText().length());
        return badExpr(comp, nullptr);
    }

    auto& expr = bind(*syntax.expr, context);
    return *comp.emplace<ClockingAssertionExpr>(clocking, expr);
}

AssertionExpr& ClockingAssertionExpr::fromSyntax(const SignalEventExpressionSyntax& syntax,
                                                 const BindContext& context) {
    // If we are binding an argument then assume it's possible it could be used in an
    // event expression and allow this. Actual usage later on will report an error if
    // this ends up not being true. Otherwise this is just an error.
    auto& comp = context.getCompilation();
    if (!context.flags.has(BindFlags::AssertionInstanceArgCheck)) {
        context.addDiag(diag::InvalidSignalEventInSeq, syntax.sourceRange());
        return badExpr(comp, nullptr);
    }

    auto& clocking = TimingControl::bind(syntax, context);
    return *comp.emplace<ClockingAssertionExpr>(clocking, badExpr(comp, nullptr));
}

void ClockingAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("clocking", clocking);
    serializer.write("expr", expr);
}

AssertionExpr& StrongWeakAssertionExpr::fromSyntax(const StrongWeakPropertyExprSyntax& syntax,
                                                   const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& expr = bind(*syntax.expr, context);
    expr.requireSequence(context);

    return *comp.emplace<StrongWeakAssertionExpr>(
        expr, syntax.keyword.kind == TokenKind::StrongKeyword ? Strong : Weak);
}

void StrongWeakAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
    serializer.write("strength", strength == Strong ? "strong"sv : "weak"sv);
}

AssertionExpr& AbortAssertionExpr::fromSyntax(const AcceptOnPropertyExprSyntax& syntax,
                                              const BindContext& context) {
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
            THROW_UNREACHABLE;
    }

    return *comp.emplace<AbortAssertionExpr>(cond, expr, action, isSync);
}

void AbortAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("condition", condition);
    serializer.write("expr", expr);
    serializer.write("action", action == Accept ? "accept"sv : "reject"sv);
    serializer.write("isSync", isSync);
}

AssertionExpr& ConditionalAssertionExpr::fromSyntax(const ConditionalPropertyExprSyntax& syntax,
                                                    const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& cond = bindExpr(*syntax.condition, context);
    auto& ifExpr = bind(*syntax.expr, context);

    const AssertionExpr* elseExpr = nullptr;
    if (syntax.elseClause)
        elseExpr = &bind(*syntax.elseClause->expr, context);

    return *comp.emplace<ConditionalAssertionExpr>(cond, ifExpr, elseExpr);
}

void ConditionalAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("condition", condition);
    serializer.write("if", ifExpr);
    if (elseExpr)
        serializer.write("else", *elseExpr);
}

AssertionExpr& CaseAssertionExpr::fromSyntax(const CasePropertyExprSyntax& syntax,
                                             const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& expr = bindExpr(*syntax.expr, context);

    const AssertionExpr* defCase = nullptr;
    SmallVectorSized<ItemGroup, 4> items;
    for (auto item : syntax.items) {
        if (item->kind == SyntaxKind::StandardPropertyCaseItem) {
            auto& sci = item->as<StandardPropertyCaseItemSyntax>();
            auto& body = AssertionExpr::bind(*sci.expr, context);

            SmallVectorSized<const Expression*, 4> exprs;
            for (auto es : sci.expressions)
                exprs.append(&bindExpr(*es, context));

            items.append(ItemGroup{ exprs.copy(comp), &body });
        }
        else {
            // The parser already errored for duplicate defaults,
            // so just ignore if it happens here.
            if (!defCase) {
                defCase =
                    &AssertionExpr::bind(*item->as<DefaultPropertyCaseItemSyntax>().expr, context);
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

} // namespace slang
