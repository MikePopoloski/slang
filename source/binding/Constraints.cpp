//------------------------------------------------------------------------------
// Constraints.cpp
// Constraint creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/Constraints.h"

#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/symbols/ASTVisitor.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/TypeTraits.h"

namespace slang {

const Constraint& Constraint::bind(const ConstraintItemSyntax& syntax, const BindContext& context) {
    BindContext ctx(context);
    ctx.flags &= ~BindFlags::ProceduralStatement;

    auto& comp = ctx.scope.getCompilation();
    Constraint* result;
    switch (syntax.kind) {
        case SyntaxKind::ConstraintBlock:
            result = &ConstraintList::fromSyntax(syntax.as<ConstraintBlockSyntax>(), ctx);
            break;
        case SyntaxKind::ExpressionConstraint:
            result =
                &ExpressionConstraint::fromSyntax(syntax.as<ExpressionConstraintSyntax>(), ctx);
            break;
        case SyntaxKind::SolveBeforeConstraint:
        case SyntaxKind::DisableConstraint:
        case SyntaxKind::LoopConstraint:
        case SyntaxKind::ConditionalConstraint:
        case SyntaxKind::UniquenessConstraint:
        case SyntaxKind::ImplicationConstraint:
            ctx.addDiag(diag::NotYetSupported, syntax.sourceRange());
            result = &badConstraint(comp, nullptr);
            break;
        default:
            THROW_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

Constraint& Constraint::badConstraint(Compilation& compilation, const Constraint* ctrl) {
    return *compilation.emplace<InvalidConstraint>(ctrl);
}

void InvalidConstraint::serializeTo(ASTSerializer& serializer) const {
    if (child)
        serializer.write("child", *child);
}

Constraint& ConstraintList::fromSyntax(const ConstraintBlockSyntax& syntax,
                                       const BindContext& context) {
    bool anyBad = false;
    SmallVectorSized<const Constraint*, 8> buffer;
    for (auto item : syntax.items) {
        auto& constraint = Constraint::bind(*item, context);
        buffer.append(&constraint);
        anyBad |= constraint.bad();
    }

    auto& comp = context.getCompilation();
    auto list = comp.emplace<ConstraintList>(buffer.copy(comp));
    if (anyBad)
        return badConstraint(comp, list);

    return *list;
}

void ConstraintList::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("list");
    for (auto constraint : list) {
        serializer.serialize(*constraint);
    }
    serializer.endArray();
}

struct ConstraintExprVisitor {
    template<typename T, typename Arg>
    using visitExprs_t = decltype(std::declval<T>().visitExprs(std::declval<Arg>()));

    const BindContext& context;
    bool failed = false;

    ConstraintExprVisitor(const BindContext& context) : context(context) {}

    template<typename T>
    bool visit(const T& expr) {
        if constexpr (is_detected_v<visitExprs_t, T, ConstraintExprVisitor>)
            expr.visitExprs(*this);

        if (failed)
            return false;

        switch (expr.kind) {
            case ExpressionKind::Streaming:
            case ExpressionKind::NewArray:
            case ExpressionKind::NewClass:
            case ExpressionKind::CopyClass:
                context.addDiag(diag::ExprNotConstraint, expr.sourceRange);
                return visitInvalid(expr);
            case ExpressionKind::RealLiteral:
            case ExpressionKind::TimeLiteral:
                context.addDiag(diag::NonIntegralConstraintLiteral, expr.sourceRange);
                return visitInvalid(expr);
            case ExpressionKind::IntegerLiteral:
                if (expr.as<IntegerLiteral>().getValue().hasUnknown()) {
                    context.addDiag(diag::UnknownConstraintLiteral, expr.sourceRange);
                    return visitInvalid(expr);
                }
                return true;
            case ExpressionKind::UnbasedUnsizedIntegerLiteral:
                if (expr.as<UnbasedUnsizedIntegerLiteral>().getValue().hasUnknown()) {
                    context.addDiag(diag::UnknownConstraintLiteral, expr.sourceRange);
                    return visitInvalid(expr);
                }
                return true;
            case ExpressionKind::BinaryOp: {
                switch (expr.as<BinaryExpression>().op) {
                    case BinaryOperator::CaseEquality:
                    case BinaryOperator::CaseInequality:
                    case BinaryOperator::WildcardEquality:
                    case BinaryOperator::WildcardInequality:
                        context.addDiag(diag::ExprNotConstraint, expr.sourceRange);
                        return visitInvalid(expr);
                    default:
                        break;
                }
                break;
            }
            case ExpressionKind::OpenRange:
                return true;
            default:
                break;
        }

        if (!expr.type->isValidForRand(RandMode::Rand)) {
            context.addDiag(diag::NonIntegralConstraintExpr, expr.sourceRange) << *expr.type;
            return visitInvalid(expr);
        }

        return true;
    }

    bool visitInvalid(const Expression&) {
        failed = true;
        return false;
    }
};

Constraint& ExpressionConstraint::fromSyntax(const ExpressionConstraintSyntax& syntax,
                                             const BindContext& context) {
    auto& comp = context.getCompilation();
    bool isSoft = syntax.soft.kind == TokenKind::SoftKeyword;
    auto& expr = Expression::bind(*syntax.expr, context);
    auto result = comp.emplace<ExpressionConstraint>(expr, isSoft);
    if (expr.bad())
        return badConstraint(comp, result);

    ConstraintExprVisitor visitor(context);
    if (!expr.visit(visitor))
        return badConstraint(comp, result);

    return *result;
}

void ExpressionConstraint::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
    serializer.write("isSoft", isSoft);
}

} // namespace slang
