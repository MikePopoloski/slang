//------------------------------------------------------------------------------
// Constraints.cpp
// Constraint creation and analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Constraints.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

const Constraint& Constraint::bind(const ConstraintItemSyntax& syntax, const ASTContext& context) {
    ASTContext ctx(context);
    ctx.flags |= ASTFlags::AssignmentDisallowed;

    Constraint* result;
    switch (syntax.kind) {
        case SyntaxKind::ConstraintBlock:
            result = &ConstraintList::fromSyntax(syntax.as<ConstraintBlockSyntax>(), ctx);
            break;
        case SyntaxKind::ExpressionConstraint:
            result = &ExpressionConstraint::fromSyntax(syntax.as<ExpressionConstraintSyntax>(),
                                                       ctx);
            break;
        case SyntaxKind::ImplicationConstraint:
            result = &ImplicationConstraint::fromSyntax(syntax.as<ImplicationConstraintSyntax>(),
                                                        ctx);
            break;
        case SyntaxKind::ConditionalConstraint:
            result = &ConditionalConstraint::fromSyntax(syntax.as<ConditionalConstraintSyntax>(),
                                                        ctx);
            break;
        case SyntaxKind::UniquenessConstraint:
            result = &UniquenessConstraint::fromSyntax(syntax.as<UniquenessConstraintSyntax>(),
                                                       ctx);
            break;
        case SyntaxKind::DisableConstraint:
            result = &DisableSoftConstraint::fromSyntax(syntax.as<DisableConstraintSyntax>(), ctx);
            break;
        case SyntaxKind::SolveBeforeConstraint:
            result = &SolveBeforeConstraint::fromSyntax(syntax.as<SolveBeforeConstraintSyntax>(),
                                                        ctx);
            break;
        case SyntaxKind::LoopConstraint:
            result = &ForeachConstraint::fromSyntax(syntax.as<LoopConstraintSyntax>(), ctx);
            break;
        default:
            SLANG_UNREACHABLE;
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
                                       const ASTContext& context) {
    bool anyBad = false;
    SmallVector<const Constraint*> buffer;
    for (auto item : syntax.items) {
        auto& constraint = Constraint::bind(*item, context);
        buffer.push_back(&constraint);
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

struct DistVarVisitor {
    const ASTContext& context;
    bool anyRandVars = false;

    DistVarVisitor(const ASTContext& context) : context(context) {}

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_base_of_v<Expression, T>) {
            switch (expr.kind) {
                case ExpressionKind::NamedValue:
                case ExpressionKind::HierarchicalValue:
                case ExpressionKind::MemberAccess:
                case ExpressionKind::ElementSelect:
                case ExpressionKind::RangeSelect: {
                    if (auto sym = expr.getSymbolReference()) {
                        RandMode mode = context.getRandMode(*sym);
                        if (mode == RandMode::Rand)
                            anyRandVars = true;
                        else if (mode == RandMode::RandC)
                            context.addDiag(diag::RandCInDist, expr.sourceRange);
                    }
                    break;
                }
                default:
                    if constexpr (HasVisitExprs<T, DistVarVisitor>)
                        expr.visitExprs(*this);
                    break;
            }
        }
    }
};

struct ConstraintExprVisitor {
    const ASTContext& context;
    bool failed = false;
    bool isTop = true;
    bool sawRandVars = false;
    bool isSoft;

    ConstraintExprVisitor(const ASTContext& context, bool isSoft) :
        context(context), isSoft(isSoft) {}

    template<typename T>
    bool visit(const T& expr) {
        if (failed || expr.bad())
            return fail();

        if constexpr (std::is_base_of_v<Expression, T>) {
            if (auto sym = expr.getSymbolReference()) {
                RandMode mode = context.getRandMode(*sym);
                if (mode != RandMode::None)
                    sawRandVars = true;

                if (isSoft && mode == RandMode::RandC)
                    context.addDiag(diag::RandCInSoft, expr.sourceRange);
            }

            bool childrenHaveRand = false;

            if constexpr (HasVisitExprs<T, ConstraintExprVisitor>) {
                // Inside call and select expressions we don't care about the types.
                // This allows things like selections of associative arrays and built-in methods
                // on arrays of strings to work as long as the actual operators at the top level
                // don't have those types.
                if (expr.kind != ExpressionKind::ElementSelect &&
                    expr.kind != ExpressionKind::MemberAccess &&
                    expr.kind != ExpressionKind::Call) {

                    const bool oldTop = std::exchange(isTop, false);
                    const bool oldSawRand = std::exchange(sawRandVars, false);
                    expr.visitExprs(*this);
                    isTop = oldTop;
                    childrenHaveRand = sawRandVars;
                    sawRandVars = oldSawRand;
                }
            }

            switch (expr.kind) {
                case ExpressionKind::Streaming:
                case ExpressionKind::NewArray:
                case ExpressionKind::NewClass:
                case ExpressionKind::CopyClass:
                    context.addDiag(diag::ExprNotConstraint, expr.sourceRange);
                    return fail();
                case ExpressionKind::RealLiteral:
                case ExpressionKind::TimeLiteral:
                    if (context.getCompilation().languageVersion() < LanguageVersion::v1800_2023) {
                        context.addDiag(diag::NonIntegralConstraintLiteral, expr.sourceRange);
                        return fail();
                    }
                    break;
                case ExpressionKind::IntegerLiteral:
                    if (expr.template as<IntegerLiteral>().getValue().hasUnknown()) {
                        context.addDiag(diag::UnknownConstraintLiteral, expr.sourceRange);
                        return fail();
                    }
                    return true;
                case ExpressionKind::UnbasedUnsizedIntegerLiteral:
                    if (expr.template as<UnbasedUnsizedIntegerLiteral>().getValue().hasUnknown()) {
                        context.addDiag(diag::UnknownConstraintLiteral, expr.sourceRange);
                        return fail();
                    }
                    return true;
                case ExpressionKind::BinaryOp: {
                    auto& binExpr = expr.template as<BinaryExpression>();
                    switch (binExpr.op) {
                        case BinaryOperator::CaseEquality:
                        case BinaryOperator::CaseInequality:
                        case BinaryOperator::WildcardEquality:
                        case BinaryOperator::WildcardInequality:
                            context.addDiag(diag::ExprNotConstraint, expr.sourceRange);
                            return fail();
                        case BinaryOperator::Equality:
                        case BinaryOperator::Inequality:
                        case BinaryOperator::GreaterThanEqual:
                        case BinaryOperator::GreaterThan:
                        case BinaryOperator::LessThanEqual:
                        case BinaryOperator::LessThan:
                        case BinaryOperator::LogicalAnd:
                        case BinaryOperator::LogicalOr:
                        case BinaryOperator::LogicalImplication:
                        case BinaryOperator::LogicalEquivalence:
                            // We previously ignored invalid types of NamedValues when
                            // we visited subexpressions. If there were any rand vars
                            // used in our subexpressions we should re-check named values
                            // for the stricter integral / numeric type requirements.
                            if (childrenHaveRand) {
                                if (ValueExpressionBase::isKind(binExpr.left().kind) &&
                                    !checkType(binExpr.left())) {
                                    return fail();
                                }

                                if (ValueExpressionBase::isKind(binExpr.right().kind) &&
                                    !checkType(binExpr.right())) {
                                    return fail();
                                }
                            }
                            break;
                        default:
                            break;
                    }
                    break;
                }
                case ExpressionKind::NamedValue:
                case ExpressionKind::HierarchicalValue:
                    if (!isTop)
                        return true;
                    break;
                case ExpressionKind::ValueRange:
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
                        return fail();
                    }

                    if (!call.isSystemCall()) {
                        const SubroutineSymbol& sub = *std::get<0>(call.subroutine);
                        for (auto arg : sub.getArguments()) {
                            if (arg->direction == ArgumentDirection::Out ||
                                arg->direction == ArgumentDirection::InOut ||
                                (arg->direction == ArgumentDirection::Ref &&
                                 !arg->flags.has(VariableFlags::Const))) {
                                context.addDiag(diag::OutRefFuncConstraint, expr.sourceRange);
                                return fail();
                            }
                        }
                    }
                    break;
                }
                default:
                    break;
            }

            if (!checkType(expr))
                return fail();
        }

        return true;
    }

private:
    bool fail() {
        failed = true;
        return false;
    }

    bool checkType(const Expression& expr) {
        if (!expr.type->isValidForRand(RandMode::Rand,
                                       context.getCompilation().languageVersion())) {
            context.addDiag(diag::InvalidConstraintExpr, expr.sourceRange) << *expr.type;
            return false;
        }
        return true;
    }
};

Constraint& ExpressionConstraint::fromSyntax(const ExpressionConstraintSyntax& syntax,
                                             const ASTContext& context) {
    auto& comp = context.getCompilation();
    bool isSoft = syntax.soft.kind == TokenKind::SoftKeyword;
    auto& expr = Expression::bind(*syntax.expr, context);
    auto result = comp.emplace<ExpressionConstraint>(expr, isSoft);
    if (expr.bad())
        return badConstraint(comp, result);

    ConstraintExprVisitor visitor(context, isSoft);
    if (!expr.visit(visitor))
        return badConstraint(comp, result);

    return *result;
}

void ExpressionConstraint::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
    serializer.write("isSoft", isSoft);
}

Constraint& ImplicationConstraint::fromSyntax(const ImplicationConstraintSyntax& syntax,
                                              const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& pred = Expression::bind(*syntax.left, context);
    auto& body = Constraint::bind(*syntax.constraints, context);
    auto result = comp.emplace<ImplicationConstraint>(pred, body);
    if (pred.bad() || body.bad())
        return badConstraint(comp, result);

    ConstraintExprVisitor visitor(context, /* isSoft */ false);
    if (!pred.visit(visitor))
        return badConstraint(comp, result);

    return *result;
}

void ImplicationConstraint::serializeTo(ASTSerializer& serializer) const {
    serializer.write("predicate", predicate);
    serializer.write("body", body);
}

Constraint& ConditionalConstraint::fromSyntax(const ConditionalConstraintSyntax& syntax,
                                              const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& pred = Expression::bind(*syntax.condition, context);
    auto& ifBody = Constraint::bind(*syntax.constraints, context);

    const Constraint* elseBody = nullptr;
    if (syntax.elseClause)
        elseBody = &Constraint::bind(*syntax.elseClause->constraints, context);

    auto result = comp.emplace<ConditionalConstraint>(pred, ifBody, elseBody);
    if (pred.bad() || ifBody.bad() || (elseBody && elseBody->bad()))
        return badConstraint(comp, result);

    ConstraintExprVisitor visitor(context, /* isSoft */ false);
    if (!pred.visit(visitor) || !context.requireBooleanConvertible(pred))
        return badConstraint(comp, result);

    return *result;
}

void ConditionalConstraint::serializeTo(ASTSerializer& serializer) const {
    serializer.write("predicate", predicate);
    serializer.write("ifBody", ifBody);
    if (elseBody)
        serializer.write("elseBody", *elseBody);
}

static bool isAllowedForUniqueness(const Type& type, LanguageVersion languageVersion) {
    if (type.isIntegral())
        return true;

    if (languageVersion >= LanguageVersion::v1800_2023 && type.isFloating())
        return true;

    if (type.isUnpackedArray())
        return isAllowedForUniqueness(*type.getArrayElementType(), languageVersion);

    return false;
}

Constraint& UniquenessConstraint::fromSyntax(const UniquenessConstraintSyntax& syntax,
                                             const ASTContext& context) {
    auto& comp = context.getCompilation();
    const auto lv = comp.languageVersion();

    bool bad = false;
    const Type* commonType = nullptr;
    SmallVector<const Expression*> items;
    for (auto item : syntax.ranges->valueRanges) {
        auto& expr = Expression::bind(*item, context);
        items.push_back(&expr);

        if (expr.bad()) {
            bad = true;
        }
        else {
            auto sym = expr.getSymbolReference();
            if (!sym || !isAllowedForUniqueness(sym->getDeclaredType()->getType(), lv)) {
                if (!sym) {
                    context.addDiag(diag::InvalidUniquenessExpr, expr.sourceRange);
                }
                else {
                    context.addDiag(diag::BadUniquenessType, expr.sourceRange)
                        << sym->getDeclaredType()->getType();
                }
                bad = true;
            }
            else {
                const Type* symType = &sym->getDeclaredType()->getType();
                while (symType->isUnpackedArray())
                    symType = symType->getArrayElementType();

                RandMode mode = context.getRandMode(*sym);
                if (mode == RandMode::RandC)
                    context.addDiag(diag::RandCInUnique, expr.sourceRange);
                else if (mode == RandMode::None)
                    context.addDiag(diag::InvalidUniquenessExpr, expr.sourceRange);
                else if (!commonType)
                    commonType = symType;
                else if (!commonType->isEquivalent(*symType)) {
                    // All variables used in a uniqueness constraint must have equivalent types.
                    if (!bad && !commonType->isError() && !symType->isError()) {
                        auto& diag = context.addDiag(diag::InequivalentUniquenessTypes,
                                                     expr.sourceRange);
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

static std::pair<const Symbol*, SourceRange> getConstraintPrimary(const Expression& expr) {
    auto sym = expr.getSymbolReference();
    if (expr.kind == ExpressionKind::Call) {
        auto& call = expr.template as<CallExpression>();
        if (call.isSystemCall() && call.getSubroutineName() == "size"sv &&
            call.arguments().size() == 1) {
            auto& arg0 = *call.arguments()[0];
            return {arg0.getSymbolReference(), arg0.sourceRange};
        }
    }
    return {sym, expr.sourceRange};
}

Constraint& DisableSoftConstraint::fromSyntax(const DisableConstraintSyntax& syntax,
                                              const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& expr = Expression::bind(*syntax.name, context);
    auto result = comp.emplace<DisableSoftConstraint>(expr);
    if (expr.bad())
        return badConstraint(comp, result);

    auto [sym, sourceRange] = getConstraintPrimary(expr);
    if (!sym || context.getRandMode(*sym) != RandMode::Rand) {
        context.addDiag(diag::BadDisableSoft, sourceRange);
        return badConstraint(comp, result);
    }

    return *result;
}

void DisableSoftConstraint::serializeTo(ASTSerializer& serializer) const {
    serializer.write("target", target);
}

Constraint& SolveBeforeConstraint::fromSyntax(const SolveBeforeConstraintSyntax& syntax,
                                              const ASTContext& context) {
    bool bad = false;
    auto bindExprs = [&](auto& list, auto& results) {
        for (auto item : list) {
            auto& expr = Expression::bind(*item, context);
            results.push_back(&expr);

            if (expr.bad()) {
                bad = true;
                continue;
            }

            auto [sym, sourceRange] = getConstraintPrimary(expr);
            if (!sym || context.getRandMode(*sym) == RandMode::None)
                context.addDiag(diag::BadSolveBefore, sourceRange);
            else if (sym && context.getRandMode(*sym) == RandMode::RandC)
                context.addDiag(diag::RandCInSolveBefore, sourceRange);
        }
    };

    auto& comp = context.getCompilation();
    SmallVector<const Expression*> solve;
    SmallVector<const Expression*> after;
    bindExprs(syntax.beforeExpr, solve);
    bindExprs(syntax.afterExpr, after);

    auto result = comp.emplace<SolveBeforeConstraint>(solve.copy(comp), after.copy(comp));
    if (bad)
        return badConstraint(comp, result);

    return *result;
}

void SolveBeforeConstraint::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("solve");
    for (auto item : solve)
        serializer.serialize(*item);
    serializer.endArray();

    serializer.startArray("after");
    for (auto item : after)
        serializer.serialize(*item);
    serializer.endArray();
}

Constraint& ForeachConstraint::fromSyntax(const LoopConstraintSyntax& syntax,
                                          const ASTContext& context) {
    auto& comp = context.getCompilation();

    ASTContext iterCtx = context;
    SmallVector<ForeachLoopStatement::LoopDim, 4> dims;
    auto arrayRef = ForeachLoopStatement::buildLoopDims(*syntax.loopList, iterCtx, dims);
    if (!arrayRef)
        return badConstraint(comp, nullptr);

    // Set the parent pointer on the iterator variables in case
    // someone inspects them later. We just created these in the
    // method above so the const_cast is safe.
    for (auto& dim : dims) {
        if (dim.loopVar)
            const_cast<IteratorSymbol*>(dim.loopVar)->setParent(*context.scope);
    }

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

} // namespace slang::ast
