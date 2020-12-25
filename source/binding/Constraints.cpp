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

    Constraint* result;
    switch (syntax.kind) {
        case SyntaxKind::ConstraintBlock:
            result = &ConstraintList::fromSyntax(syntax.as<ConstraintBlockSyntax>(), ctx);
            break;
        case SyntaxKind::ExpressionConstraint:
            result =
                &ExpressionConstraint::fromSyntax(syntax.as<ExpressionConstraintSyntax>(), ctx);
            break;
        case SyntaxKind::ImplicationConstraint:
            result =
                &ImplicationConstraint::fromSyntax(syntax.as<ImplicationConstraintSyntax>(), ctx);
            break;
        case SyntaxKind::ConditionalConstraint:
            result =
                &ConditionalConstraint::fromSyntax(syntax.as<ConditionalConstraintSyntax>(), ctx);
            break;
        case SyntaxKind::UniquenessConstraint:
            result =
                &UniquenessConstraint::fromSyntax(syntax.as<UniquenessConstraintSyntax>(), ctx);
            break;
        case SyntaxKind::DisableConstraint:
            result = &DisableSoftConstraint::fromSyntax(syntax.as<DisableConstraintSyntax>(), ctx);
            break;
        case SyntaxKind::SolveBeforeConstraint:
            result =
                &SolveBeforeConstraint::fromSyntax(syntax.as<SolveBeforeConstraintSyntax>(), ctx);
            break;
        case SyntaxKind::LoopConstraint:
            result = &ForeachConstraint::fromSyntax(syntax.as<LoopConstraintSyntax>(), ctx);
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

template<typename T, typename Arg>
using visitExprs_t = decltype(std::declval<T>().visitExprs(std::declval<Arg>()));

struct DistVarVisitor {
    const BindContext& context;
    bool anyRandVars = false;

    DistVarVisitor(const BindContext& context) : context(context) {}

    template<typename T>
    void visit(const T& expr) {
        switch (expr.kind) {
            case ExpressionKind::NamedValue:
            case ExpressionKind::HierarchicalValue:
            case ExpressionKind::MemberAccess:
            case ExpressionKind::ElementSelect:
            case ExpressionKind::RangeSelect: {
                if (auto sym = expr.getSymbolReference()) {
                    RandMode mode = sym->getRandMode();
                    if (mode == RandMode::Rand)
                        anyRandVars = true;
                    else if (mode == RandMode::RandC)
                        context.addDiag(diag::RandCInDist, expr.sourceRange);
                }
                break;
            }
            default:
                if constexpr (is_detected_v<visitExprs_t, T, DistVarVisitor>)
                    expr.visitExprs(*this);
                break;
        }
    }

    void visitInvalid(const Expression&) {}
};

struct ConstraintExprVisitor {
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
                if (expr.template as<IntegerLiteral>().getValue().hasUnknown()) {
                    context.addDiag(diag::UnknownConstraintLiteral, expr.sourceRange);
                    return visitInvalid(expr);
                }
                return true;
            case ExpressionKind::UnbasedUnsizedIntegerLiteral:
                if (expr.template as<UnbasedUnsizedIntegerLiteral>().getValue().hasUnknown()) {
                    context.addDiag(diag::UnknownConstraintLiteral, expr.sourceRange);
                    return visitInvalid(expr);
                }
                return true;
            case ExpressionKind::BinaryOp: {
                switch (expr.template as<BinaryExpression>().op) {
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
            case ExpressionKind::Dist: {
                // Additional restrictions on dist expressions:
                // - must contain at least one 'rand' var
                // - cannot contain any 'randc' vars
                DistVarVisitor distVisitor(context);
                auto& left = expr.template as<DistExpression>().left();
                left.visit(distVisitor);
                if (!distVisitor.anyRandVars)
                    context.addDiag(diag::RandNeededInDist, left.sourceRange);
                return true;
            }
            case ExpressionKind::Call: {
                auto& call = expr.template as<CallExpression>();
                if (call.getSubroutineKind() == SubroutineKind::Task) {
                    context.addDiag(diag::TaskInConstraint, expr.sourceRange);
                    return visitInvalid(expr);
                }

                if (!call.isSystemCall()) {
                    const SubroutineSymbol& sub = *std::get<0>(call.subroutine);
                    for (auto arg : sub.getArguments()) {
                        if (arg->direction == ArgumentDirection::Out ||
                            (arg->direction == ArgumentDirection::Ref && !arg->isConstant)) {
                            context.addDiag(diag::OutRefFuncConstraint, expr.sourceRange);
                            return visitInvalid(expr);
                        }
                    }
                }
                break;
            }
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

Constraint& ImplicationConstraint::fromSyntax(const ImplicationConstraintSyntax& syntax,
                                              const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& pred = Expression::bind(*syntax.left, context);
    auto& body = Constraint::bind(*syntax.constraints, context);
    auto result = comp.emplace<ImplicationConstraint>(pred, body);
    if (pred.bad() || body.bad())
        return badConstraint(comp, result);

    ConstraintExprVisitor visitor(context);
    if (!pred.visit(visitor))
        return badConstraint(comp, result);

    return *result;
}

void ImplicationConstraint::serializeTo(ASTSerializer& serializer) const {
    serializer.write("predicate", predicate);
    serializer.write("body", body);
}

Constraint& ConditionalConstraint::fromSyntax(const ConditionalConstraintSyntax& syntax,
                                              const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& pred = Expression::bind(*syntax.condition, context);
    auto& ifBody = Constraint::bind(*syntax.constraints, context);

    const Constraint* elseBody = nullptr;
    if (syntax.elseClause)
        elseBody = &Constraint::bind(*syntax.elseClause->constraints, context);

    auto result = comp.emplace<ConditionalConstraint>(pred, ifBody, elseBody);
    if (pred.bad() || ifBody.bad() || (elseBody && elseBody->bad()))
        return badConstraint(comp, result);

    ConstraintExprVisitor visitor(context);
    if (!pred.visit(visitor))
        return badConstraint(comp, result);

    return *result;
}

void ConditionalConstraint::serializeTo(ASTSerializer& serializer) const {
    serializer.write("predicate", predicate);
    serializer.write("ifBody", ifBody);
    if (elseBody)
        serializer.write("elseBody", *elseBody);
}

static bool isAllowedForUniqueness(const Type& type) {
    if (type.isIntegral())
        return true;

    if (type.isUnpackedArray())
        return isAllowedForUniqueness(*type.getArrayElementType());

    return false;
}

Constraint& UniquenessConstraint::fromSyntax(const UniquenessConstraintSyntax& syntax,
                                             const BindContext& context) {
    auto& comp = context.getCompilation();
    bool bad = false;
    const Type* commonType = nullptr;
    SmallVectorSized<const Expression*, 4> items;
    for (auto item : syntax.ranges->valueRanges) {
        auto& expr = Expression::bind(*item, context);
        items.append(&expr);

        if (expr.bad()) {
            bad = true;
        }
        else {
            auto sym = expr.getSymbolReference();
            if (!sym || !isAllowedForUniqueness(sym->getDeclaredType()->getType())) {
                context.addDiag(diag::InvalidUniquenessExpr, expr.sourceRange);
                bad = true;
            }
            else {
                const Type* symType = &sym->getDeclaredType()->getType();
                while (symType->isUnpackedArray())
                    symType = symType->getArrayElementType();

                RandMode mode = sym->getRandMode();
                if (mode == RandMode::RandC)
                    context.addDiag(diag::RandCInUnique, expr.sourceRange);
                else if (mode == RandMode::None)
                    context.addDiag(diag::InvalidUniquenessExpr, expr.sourceRange);
                else if (!commonType)
                    commonType = symType;
                else if (!commonType->isEquivalent(*symType)) {
                    // All variables used in a uniqueness constraint must have equivalent types.
                    if (!bad && !commonType->isError() && !symType->isError()) {
                        auto& diag =
                            context.addDiag(diag::InequivalentUniquenessTypes, expr.sourceRange);
                        diag << sym->name << *symType << *commonType;
                        bad = true;
                    }
                }
            }
        }
    }

    auto result = comp.emplace<UniquenessConstraint>(items.copy(comp));
    if (bad)
        return badConstraint(comp, result);

    return *result;
}

void UniquenessConstraint::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("items");
    for (auto item : items)
        serializer.serialize(*item);
    serializer.endArray();
}

Constraint& DisableSoftConstraint::fromSyntax(const DisableConstraintSyntax& syntax,
                                              const BindContext& context) {
    auto& comp = context.getCompilation();
    auto& expr = Expression::bind(*syntax.name, context);
    auto result = comp.emplace<DisableSoftConstraint>(expr);
    if (expr.bad())
        return badConstraint(comp, result);

    auto sym = expr.getSymbolReference();
    if (!sym || sym->getRandMode() == RandMode::None) {
        context.addDiag(diag::BadDisableSoft, expr.sourceRange);
        return badConstraint(comp, result);
    }

    return *result;
}

void DisableSoftConstraint::serializeTo(ASTSerializer& serializer) const {
    serializer.write("target", target);
}

Constraint& SolveBeforeConstraint::fromSyntax(const SolveBeforeConstraintSyntax& syntax,
                                              const BindContext& context) {
    bool bad = false;
    auto bindExprs = [&](auto& list, auto& results) {
        for (auto item : list) {
            auto& expr = Expression::bind(*item, context);
            results.append(&expr);

            if (expr.bad())
                bad = true;
            else {
                auto sym = expr.getSymbolReference();
                if (!sym || sym->getRandMode() == RandMode::None)
                    context.addDiag(diag::BadSolveBefore, expr.sourceRange);
                else if (sym && sym->getRandMode() == RandMode::RandC)
                    context.addDiag(diag::RandCInSolveBefore, expr.sourceRange);
            }
        }
    };

    auto& comp = context.getCompilation();
    SmallVectorSized<const Expression*, 4> solve;
    SmallVectorSized<const Expression*, 4> before;
    bindExprs(syntax.beforeExpr, solve);
    bindExprs(syntax.afterExpr, before);

    auto result = comp.emplace<SolveBeforeConstraint>(solve.copy(comp), before.copy(comp));
    if (bad)
        return badConstraint(comp, result);

    return *result;
}

void SolveBeforeConstraint::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("solve");
    for (auto item : solve)
        serializer.serialize(*item);
    serializer.endArray();

    serializer.startArray("before");
    for (auto item : before)
        serializer.serialize(*item);
    serializer.endArray();
}

Constraint& ForeachConstraint::fromSyntax(const LoopConstraintSyntax& syntax,
                                          const BindContext& context) {
    auto& comp = context.getCompilation();

    BindContext iterCtx = context;
    SmallVectorSized<ForeachLoopStatement::LoopDim, 4> dims;
    auto arrayRef = ForeachLoopStatement::buildLoopDims(*syntax.loopList, iterCtx, dims);
    if (!arrayRef)
        return badConstraint(comp, nullptr);

    auto& body = Constraint::bind(*syntax.constraints, iterCtx);
    auto result = comp.emplace<ForeachConstraint>(*arrayRef, dims.copy(comp), body);
    if (body.bad())
        return badConstraint(comp, result);

    return *result;
}

void ForeachConstraint::serializeTo(ASTSerializer& serializer) const {
    serializer.write("arrayRef", arrayRef);

    serializer.startArray("loopDims");
    for (auto& r : loopDims) {
        serializer.startObject();
        serializer.write("range", r.range ? r.range->toString() : "[]");
        if (r.loopVar)
            serializer.write("var", *r.loopVar);
        serializer.endObject();
    }
    serializer.endArray();

    serializer.write("body", body);
}

} // namespace slang
