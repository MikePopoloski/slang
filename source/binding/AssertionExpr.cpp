//------------------------------------------------------------------------------
// AssertionExpr.cpp
// Assertion expression creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/AssertionExpr.h"

#include "slang/binding/BindContext.h"
#include "slang/compilation/Compilation.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

const AssertionExpr& AssertionExpr::bind(const SequenceExprSyntax& syntax,
                                         const BindContext& context) {
    BindContext ctx(context);
    ctx.flags |= BindFlags::AssignmentDisallowed;

    AssertionExpr* result;
    switch (syntax.kind) {
        case SyntaxKind::DelayedSequenceExpr:
        case SyntaxKind::ClockingSequenceExpr:
        case SyntaxKind::FirstMatchSequenceExpr:
        case SyntaxKind::ParenthesizedSequenceExpr:
        case SyntaxKind::SimpleSequenceExpr:
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
        case SyntaxKind::ClockingPropertyExpr:
        case SyntaxKind::ParenthesizedPropertyExpr:
        case SyntaxKind::StrongWeakPropertyExpr:
        case SyntaxKind::UnaryPropertyExpr:
        case SyntaxKind::UnarySelectPropertyExpr:
        case SyntaxKind::AcceptOnPropertyExpr:
        case SyntaxKind::ConditionalPropertyExpr:
        case SyntaxKind::CasePropertyExpr:
        case SyntaxKind::SimplePropertyExpr:
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

} // namespace slang
