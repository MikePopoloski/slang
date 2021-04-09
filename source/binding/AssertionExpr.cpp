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

AssertionExpr& SimpleAssertionExpr::fromSyntax(const SimpleSequenceExprSyntax& syntax,
                                               const BindContext& context) {
    // TODO: repetition
    auto& comp = context.getCompilation();
    auto& expr = bindExpr(*syntax.expr, context);
    return *comp.emplace<SimpleAssertionExpr>(expr);
}

} // namespace slang
