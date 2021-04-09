//------------------------------------------------------------------------------
// AssertionExpr.cpp
// Assertion expression creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/AssertionExpr.h"

#include "slang/binding/BindContext.h"
#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/Type.h"

namespace slang {

static const Expression& bindExpr(const ExpressionSyntax& syntax, const BindContext& context) {
    auto& expr = Expression::bind(syntax, context, BindFlags::AssertionExpr);
    if (expr.bad())
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
        case SyntaxKind::ClockingSequenceExpr:
        case SyntaxKind::FirstMatchSequenceExpr:
        case SyntaxKind::ParenthesizedSequenceExpr:
        case SyntaxKind::AndSequenceExpr:
        case SyntaxKind::OrSequenceExpr:
        case SyntaxKind::IntersectSequenceExpr:
        case SyntaxKind::ThroughoutSequenceExpr:
        case SyntaxKind::WithinSequenceExpr:
            context.addDiag(diag::NotYetSupported, syntax.sourceRange());
            result = &badExpr(ctx.getCompilation(), nullptr);
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
        case SyntaxKind::ClockingPropertyExpr:
        case SyntaxKind::ParenthesizedPropertyExpr:
        case SyntaxKind::StrongWeakPropertyExpr:
        case SyntaxKind::UnaryPropertyExpr:
        case SyntaxKind::UnarySelectPropertyExpr:
        case SyntaxKind::AcceptOnPropertyExpr:
        case SyntaxKind::ConditionalPropertyExpr:
        case SyntaxKind::CasePropertyExpr:
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
            context.addDiag(diag::NotYetSupported, syntax.sourceRange());
            result = &badExpr(ctx.getCompilation(), nullptr);
            break;
        default:
            THROW_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

AssertionExpr& AssertionExpr::badExpr(Compilation& compilation, const AssertionExpr* expr) {
    return *compilation.emplace<InvalidAssertionExpr>(expr);
}

void InvalidAssertionExpr::serializeTo(ASTSerializer& serializer) const {
    if (child)
        serializer.write("child", *child);
}

SequenceRange SequenceRange::fromSyntax(const RangeSelectSyntax& syntax,
                                        const BindContext& context) {
    SequenceRange range;
    auto l = context.evalInteger(*syntax.left);
    if (context.requirePositive(l, syntax.left->sourceRange()))
        range.min = uint32_t(*l);

    // The rhs can be an unbounded '$' so we need extra bind flags.
    auto& re = Expression::bind(*syntax.right, context,
                                BindFlags::AllowUnboundedLiteral | BindFlags::AssertionExpr);
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

    if (!syntax.selector)
        return;

    if (syntax.selector->kind == SyntaxKind::BitSelect) {
        auto val = context.evalInteger(*syntax.selector->as<BitSelectSyntax>().expr);
        if (context.requirePositive(val, syntax.selector->sourceRange()))
            range.max = range.min = uint32_t(*val);
    }
    else {
        auto& rs = syntax.selector->as<RangeSelectSyntax>();
        range = SequenceRange::fromSyntax(rs, context);
    }
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

    serializer.write("min", range.min);
    if (range.max)
        serializer.write("max", *range.max);
    else
        serializer.write("max", "$"sv);

    serializer.endObject();
}

AssertionExpr& SimpleAssertionExpr::fromSyntax(const SimpleSequenceExprSyntax& syntax,
                                               const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& expr = bindExpr(*syntax.expr, context);

    optional<SequenceRepetition> repetition;
    if (syntax.repetition)
        repetition.emplace(*syntax.repetition, context);

    return *comp.emplace<SimpleAssertionExpr>(expr, repetition);
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
            delay = SequenceRange::fromSyntax(es->range->as<RangeSelectSyntax>(), context);
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
        serializer.write("minDelay", elem.delay.min);
        if (elem.delay.max)
            serializer.write("maxDelay", *elem.delay.max);
        else
            serializer.write("maxDelay", "$"sv);
        serializer.endObject();
    }

    serializer.endArray();
}

} // namespace slang
