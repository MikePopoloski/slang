//------------------------------------------------------------------------------
// ConditionalStatements.cpp
// Conditional / case statement definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/statements/ConditionalStatements.h"

#include <fmt/core.h>

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace syntax;
using namespace parsing;

using ER = Statement::EvalResult;

static UniquePriorityCheck getUniquePriority(TokenKind kind) {
    UniquePriorityCheck check;
    switch (kind) {
        case TokenKind::Unknown:
            check = UniquePriorityCheck::None;
            break;
        case TokenKind::UniqueKeyword:
            check = UniquePriorityCheck::Unique;
            break;
        case TokenKind::Unique0Keyword:
            check = UniquePriorityCheck::Unique0;
            break;
        case TokenKind::PriorityKeyword:
            check = UniquePriorityCheck::Priority;
            break;
        default:
            SLANG_UNREACHABLE;
    }

    return check;
}

Statement& ConditionalStatement::fromSyntax(Compilation& comp,
                                            const ConditionalStatementSyntax& syntax,
                                            const ASTContext& context, StatementContext& stmtCtx) {
    bool bad = false;
    bool isConst = true;
    bool isTrue = true;
    SmallVector<Condition> conditions;
    ASTContext trueContext = context;
    const StatementBlockSymbol* currBlock = nullptr;
    const Statement* ifTrue = nullptr;

    for (auto condSyntax : syntax.predicate->conditions) {
        auto& cond = Expression::bind(*condSyntax->expr, trueContext);
        bad |= cond.bad();

        const Pattern* pattern = nullptr;
        if (condSyntax->matchesClause) {
            // If there is a matches clause we expect a block to have been created.
            // The first one will be registered with the stmtCtx, the rest are children
            // of that first block.
            if (!currBlock) {
                ifTrue = stmtCtx.tryGetBlock(context, *condSyntax);
                SLANG_ASSERT(ifTrue);
                if (ifTrue->bad())
                    return badStmt(comp, nullptr);

                currBlock = ifTrue->as<BlockStatement>().blockSymbol;
                SLANG_ASSERT(currBlock);
            }
            else {
                auto last = currBlock->getLastMember();
                SLANG_ASSERT(last);
                currBlock = &last->as<StatementBlockSymbol>();
            }

            // If the block was invalid (due to failing to bind pattern variables),
            // just bail out early.
            if (currBlock->isKnownBad())
                return badStmt(comp, nullptr);

            trueContext = ASTContext(*currBlock, LookupLocation::max, trueContext.flags);
            pattern = &Pattern::bind(trueContext, *condSyntax->matchesClause->pattern, *cond.type);
            bad |= pattern->bad();

            // We don't consider the condition to be const if there's a pattern.
            isConst = false;
        }
        else if (!bad && !trueContext.requireBooleanConvertible(cond)) {
            bad = true;
        }

        if (!bad && isConst) {
            ConstantValue condVal = trueContext.tryEval(cond);
            if (!condVal)
                isConst = false;
            else if (!condVal.isTrue())
                isTrue = false;
        }

        conditions.push_back({&cond, pattern});
    }

    // If the condition is constant, we know which branch will be taken.
    ASTFlags ifFlags = ASTFlags::None;
    ASTFlags elseFlags = ASTFlags::None;
    if (isConst) {
        if (isTrue)
            elseFlags = ASTFlags::UnevaluatedBranch;
        else
            ifFlags = ASTFlags::UnevaluatedBranch;
    }

    // If the `ifTrue` statement is already set it means we had a pattern
    // in at least one condition, so we don't need to bind it again.
    // We still need need to drill down in that case to the final block
    // which has the actual statement to execute; the others above it in the
    // tree just contain pattern variables.
    if (ifTrue) {
        SLANG_ASSERT(currBlock);
        auto last = currBlock->getLastMember();
        SLANG_ASSERT(last);
        currBlock = &last->as<StatementBlockSymbol>();
        ifTrue = &currBlock->getStatement(trueContext, stmtCtx);
    }
    else {
        ifTrue = &Statement::bind(*syntax.statement, trueContext.resetFlags(ifFlags), stmtCtx);
    }

    const Statement* ifFalse = nullptr;
    if (syntax.elseClause) {
        ifFalse = &Statement::bind(syntax.elseClause->clause->as<StatementSyntax>(),
                                   context.resetFlags(elseFlags), stmtCtx);
    }

    auto result = comp.emplace<ConditionalStatement>(
        conditions.copy(comp), getUniquePriority(syntax.uniqueOrPriority.kind), *ifTrue, ifFalse,
        syntax.sourceRange());

    if (bad || conditions.empty() || ifTrue->bad() || (ifFalse && ifFalse->bad()))
        return badStmt(comp, result);

    return *result;
}

struct EvalConditionalVisitor {
    EvalContext& context;
    SmallVector<const Statement*> items;
    bool bad = false;

    EvalConditionalVisitor(EvalContext& context) : context(context), items() {}

    void visit(const ConditionalStatement& stmt) {
        bool matched = true;
        for (auto& cond : stmt.conditions) {
            auto result = cond.expr->eval(context);
            bad |= result.bad();

            if (cond.pattern) {
                result = cond.pattern->eval(context, result, CaseStatementCondition::Normal);
                bad |= result.bad();
            }

            if (!result.isTrue()) {
                matched = false;
                break;
            }
        }

        if (matched)
            stmt.ifTrue.visit(*this);

        if (stmt.ifFalse) {
            if (ConditionalStatement::isKind(stmt.ifFalse->kind) || !matched)
                stmt.ifFalse->visit(*this);
        }
    }

    void visit(const Statement& stmt) { items.push_back(&stmt); }
};

ER ConditionalStatement::evalImpl(EvalContext& context) const {
    EvalConditionalVisitor visitor(context);
    this->visit(visitor);
    if (visitor.bad)
        return ER::Fail;

    if (visitor.items.empty()) {
        if (check == UniquePriorityCheck::Priority || check == UniquePriorityCheck::Unique) {
            auto& diag = context.addDiag(diag::ConstEvalNoIfItemsMatched,
                                         conditions.back().expr->sourceRange);
            diag << (check == UniquePriorityCheck::Priority ? "priority"sv : "unique"sv);
        }
        return ER::Success;
    }

    bool unique = check == UniquePriorityCheck::Unique || check == UniquePriorityCheck::Unique0;
    if (unique && visitor.items.size() > 1) {
        auto& diag = context.addDiag(diag::ConstEvalIfItemsNotUnique,
                                     visitor.items[1]->sourceRange);
        diag.addNote(diag::NotePreviousMatch, visitor.items[0]->sourceRange);
    }

    return visitor.items[0]->eval(context);
}

void ConditionalStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("conditions");
    for (auto& cond : conditions) {
        serializer.startObject();
        serializer.write("expr", *cond.expr);
        if (cond.pattern)
            serializer.write("pattern", *cond.pattern);
        serializer.endObject();
    }
    serializer.endArray();
    serializer.write("check", toString(check));

    serializer.write("ifTrue", ifTrue);
    if (ifFalse)
        serializer.write("ifFalse", *ifFalse);
}

static CaseStatementCondition getCondition(TokenKind kind) {
    CaseStatementCondition condition;
    switch (kind) {
        case TokenKind::CaseKeyword:
            condition = CaseStatementCondition::Normal;
            break;
        case TokenKind::CaseXKeyword:
            condition = CaseStatementCondition::WildcardXOrZ;
            break;
        case TokenKind::CaseZKeyword:
            condition = CaseStatementCondition::WildcardJustZ;
            break;
        default:
            SLANG_UNREACHABLE;
    }

    return condition;
}

Statement& CaseStatement::fromSyntax(Compilation& compilation, const CaseStatementSyntax& syntax,
                                     const ASTContext& context, StatementContext& stmtCtx) {
    if (syntax.matchesOrInside.kind == TokenKind::MatchesKeyword)
        return PatternCaseStatement::fromSyntax(compilation, syntax, context, stmtCtx);

    SmallVector<const ExpressionSyntax*> expressions;
    SmallVector<const Statement*> statements;
    const Statement* defStmt = nullptr;
    bool bad = false;

    for (auto item : syntax.items) {
        switch (item->kind) {
            case SyntaxKind::StandardCaseItem: {
                auto& sci = item->as<StandardCaseItemSyntax>();
                auto& stmt = Statement::bind(sci.clause->as<StatementSyntax>(), context, stmtCtx);
                for (auto es : sci.expressions)
                    expressions.push_back(es);

                statements.push_back(&stmt);
                bad |= stmt.bad();
                break;
            }
            case SyntaxKind::DefaultCaseItem:
                // The parser already errored for duplicate defaults,
                // so just ignore if it happens here.
                if (!defStmt) {
                    defStmt = &Statement::bind(
                        item->as<DefaultCaseItemSyntax>().clause->as<StatementSyntax>(), context,
                        stmtCtx);
                    bad |= defStmt->bad();
                }
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    SmallVector<const Expression*> bound;
    TokenKind keyword = syntax.caseKeyword.kind;
    bool isInside = syntax.matchesOrInside.kind == TokenKind::InsideKeyword;
    bool wildcard = !isInside && keyword != TokenKind::CaseKeyword;
    bool allowTypeRefs = !isInside && keyword == TokenKind::CaseKeyword;
    bool allowValueRange = !wildcard;

    bad |= !Expression::bindMembershipExpressions(context, keyword, wildcard, isInside,
                                                  allowTypeRefs, allowValueRange, *syntax.expr,
                                                  expressions, bound);

    auto condition = getCondition(syntax.caseKeyword.kind);
    auto check = getUniquePriority(syntax.uniqueOrPriority.kind);

    if (isInside && condition != CaseStatementCondition::Normal) {
        context.addDiag(diag::CaseInsideKeyword, syntax.matchesOrInside.range())
            << LexerFacts::getTokenKindText(keyword) << syntax.caseKeyword.range();
        bad = true;
    }
    else if (isInside) {
        condition = CaseStatementCondition::Inside;
    }

    SmallVector<ItemGroup, 8> items;
    SmallVector<const Expression*> group;
    auto boundIt = bound.begin();
    auto stmtIt = statements.begin();

    auto expr = *boundIt++;
    bad |= expr->bad();

    for (auto item : syntax.items) {
        switch (item->kind) {
            case SyntaxKind::StandardCaseItem: {
                auto& sci = item->as<StandardCaseItemSyntax>();
                for (size_t i = 0; i < sci.expressions.size(); i++) {
                    bad |= (*boundIt)->bad();
                    group.push_back(*boundIt++);
                }

                items.push_back({group.copy(compilation), *stmtIt++});
                group.clear();
                break;
            }
            default:
                break;
        }
    }

    auto result = compilation.emplace<CaseStatement>(condition, check, *expr,
                                                     items.copy(compilation), defStmt,
                                                     syntax.sourceRange());
    if (bad)
        return badStmt(compilation, result);

    if (!defStmt) {
        context.addDiag(diag::CaseDefault, syntax.caseKeyword.range())
            << LexerFacts::getTokenKindText(keyword);
    }

    return *result;
}

static bool checkMatch(CaseStatementCondition condition, const ConstantValue& cvl,
                       const ConstantValue& cvr) {
    if (condition == CaseStatementCondition::Inside) {
        // Unpacked arrays get unwrapped into their members for comparison.
        if (cvr.isContainer()) {
            for (auto& elem : cvr) {
                if (checkMatch(condition, cvl, elem))
                    return true;
            }
            return false;
        }

        // Otherwise, we do a wildcard comparison if both sides are integers
        // and an equivalence comparison if not.
        if (cvl.isInteger() && cvr.isInteger())
            return (bool)condWildcardEqual(cvl.integer(), cvr.integer());
    }
    else if (condition != CaseStatementCondition::Normal) {
        const SVInt& l = cvl.integer();
        const SVInt& r = cvr.integer();
        if (condition == CaseStatementCondition::WildcardJustZ)
            return caseZWildcardEqual(l, r);
        else
            return caseXWildcardEqual(l, r);
    }

    return cvl == cvr;
}

std::pair<const Statement*, bool> CaseStatement::getKnownBranch(EvalContext& context) const {
    const Type* condType = nullptr;
    auto cv = expr.eval(context);
    if (!cv) {
        if (expr.kind == ExpressionKind::TypeReference)
            condType = &expr.as<TypeReferenceExpression>().targetType;
        else
            return {nullptr, false};
    }

    const Statement* matchedStmt = nullptr;
    SourceRange matchRange;
    bool unique = check == UniquePriorityCheck::Unique || check == UniquePriorityCheck::Unique0;

    for (auto& group : items) {
        for (auto item : group.expressions) {
            bool matched;
            if (item->kind == ExpressionKind::ValueRange) {
                ConstantValue val = item->as<ValueRangeExpression>().checkInside(context, cv);
                if (!val)
                    return {nullptr, false};

                matched = (bool)(logic_t)val.integer();
            }
            else {
                auto val = item->eval(context);
                if (val)
                    matched = checkMatch(condition, cv, val);
                else if (condType && item->kind == ExpressionKind::TypeReference)
                    matched = item->as<TypeReferenceExpression>().targetType.isMatching(*condType);
                else
                    return {nullptr, false};
            }

            if (matched) {
                // If we already matched with a previous item, the only we reason
                // we'd still get here is to check for uniqueness. The presence of
                // another match means we failed the uniqueness check.
                if (matchedStmt) {
                    auto& diag =
                        context.addDiag(diag::ConstEvalCaseItemsNotUnique, item->sourceRange) << cv;
                    diag.addNote(diag::NotePreviousMatch, matchRange);
                    unique = false;
                }
                else {
                    // Always break out of the item group once we find a match -- even when
                    // checking uniqueness, expressions in a single group are not required
                    // to be unique.
                    matchedStmt = group.stmt;
                    matchRange = item->sourceRange;
                }
                break;
            }
        }

        if (matchedStmt && !unique)
            break;
    }

    if (!matchedStmt)
        matchedStmt = defaultCase;

    if (!matchedStmt &&
        (check == UniquePriorityCheck::Priority || check == UniquePriorityCheck::Unique)) {

        auto& diag = context.addDiag(diag::ConstEvalNoCaseItemsMatched, expr.sourceRange);
        diag << (check == UniquePriorityCheck::Priority ? "priority"sv : "unique"sv);
        diag << cv;
    }

    return {matchedStmt, true};
}

ER CaseStatement::evalImpl(EvalContext& context) const {
    auto [matchedStmt, success] = getKnownBranch(context);
    if (!success)
        return ER::Fail;

    if (matchedStmt)
        return matchedStmt->eval(context);

    return ER::Success;
}

void CaseStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("condition", toString(condition));
    serializer.write("check", toString(check));
    serializer.write("expr", expr);
    serializer.startArray("items");
    for (auto const& item : items) {
        serializer.startObject();

        serializer.startArray("expressions");
        for (auto ex : item.expressions) {
            serializer.serialize(*ex);
        }
        serializer.endArray();

        serializer.write("stmt", *item.stmt);

        serializer.endObject();
    }
    serializer.endArray();

    if (defaultCase) {
        serializer.write("defaultCase", *defaultCase);
    }
}

Statement& PatternCaseStatement::fromSyntax(Compilation& compilation,
                                            const CaseStatementSyntax& syntax,
                                            const ASTContext& context, StatementContext& stmtCtx) {
    SLANG_ASSERT(syntax.matchesOrInside.kind == TokenKind::MatchesKeyword);

    auto& expr = Expression::bind(*syntax.expr, context);
    bool bad = expr.bad();

    SmallVector<ItemGroup, 8> items;
    const Statement* defStmt = nullptr;

    for (auto item : syntax.items) {
        switch (item->kind) {
            case SyntaxKind::PatternCaseItem: {
                // We always create an implicit block for each case item.
                auto& pci = item->as<PatternCaseItemSyntax>();
                auto stmt = stmtCtx.tryGetBlock(context, pci);
                SLANG_ASSERT(stmt);
                bad |= stmt->bad();

                const Pattern* pattern = nullptr;
                const Expression* filter = nullptr;

                if (stmt->kind == StatementKind::Block) {
                    auto& block = stmt->as<BlockStatement>();
                    if (block.blockSymbol) {
                        ASTContext blockContext(*block.blockSymbol, LookupLocation::max,
                                                context.flags);
                        pattern = &Pattern::bind(blockContext, *pci.pattern, *expr.type);

                        if (pci.expr) {
                            filter = &Expression::bind(*pci.expr, blockContext);
                            if (!bad && !blockContext.requireBooleanConvertible(*filter))
                                bad = true;
                        }
                    }
                }

                if (!pattern)
                    pattern = compilation.emplace<InvalidPattern>(nullptr);

                bad |= pattern->bad();
                items.push_back({pattern, filter, stmt});
                break;
            }
            case SyntaxKind::DefaultCaseItem:
                // The parser already errored for duplicate defaults,
                // so just ignore if it happens here.
                if (!defStmt) {
                    defStmt = &Statement::bind(
                        item->as<DefaultCaseItemSyntax>().clause->as<StatementSyntax>(), context,
                        stmtCtx);
                    bad |= defStmt->bad();
                }
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    auto condition = getCondition(syntax.caseKeyword.kind);
    auto check = getUniquePriority(syntax.uniqueOrPriority.kind);
    auto result = compilation.emplace<PatternCaseStatement>(condition, check, expr,
                                                            items.copy(compilation), defStmt,
                                                            syntax.sourceRange());
    if (bad)
        return badStmt(compilation, result);

    return *result;
}

ER PatternCaseStatement::evalImpl(EvalContext& context) const {
    auto cv = expr.eval(context);
    if (!cv)
        return ER::Fail;

    const Statement* matchedStmt = nullptr;
    SourceRange matchRange;

    for (auto& item : items) {
        auto val = item.pattern->eval(context, cv, condition);
        if (!val)
            return ER::Fail;

        if (!val.isTrue())
            continue;

        if (item.filter) {
            val = item.filter->eval(context);
            if (!val)
                return ER::Fail;

            if (!val.isTrue())
                continue;
        }

        // If we already matched with a previous item, the only we reason
        // we'd still get here is to check for uniqueness. The presence of
        // another match means we failed the uniqueness check.
        if (matchedStmt) {
            auto& diag =
                context.addDiag(diag::ConstEvalCaseItemsNotUnique, item.pattern->sourceRange) << cv;
            diag.addNote(diag::NotePreviousMatch, matchRange);
            break;
        }

        matchedStmt = item.stmt;
        matchRange = item.pattern->sourceRange;

        if (check != UniquePriorityCheck::Unique && check != UniquePriorityCheck::Unique0)
            break;
    }

    if (!matchedStmt)
        matchedStmt = defaultCase;

    if (matchedStmt)
        return matchedStmt->eval(context);

    if (check == UniquePriorityCheck::Priority || check == UniquePriorityCheck::Unique) {
        auto& diag = context.addDiag(diag::ConstEvalNoCaseItemsMatched, expr.sourceRange);
        diag << (check == UniquePriorityCheck::Priority ? "priority"sv : "unique"sv);
        diag << cv;
    }

    return ER::Success;
}

void PatternCaseStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("condition", toString(condition));
    serializer.write("check", toString(check));
    serializer.write("expr", expr);
    serializer.startArray("items");
    for (auto const& item : items) {
        serializer.startObject();
        serializer.write("pattern", *item.pattern);

        if (item.filter)
            serializer.write("filter", *item.filter);

        serializer.write("stmt", *item.stmt);
        serializer.endObject();
    }
    serializer.endArray();

    if (defaultCase) {
        serializer.write("defaultCase", *defaultCase);
    }
}

} // namespace slang::ast
