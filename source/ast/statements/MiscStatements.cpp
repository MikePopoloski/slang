//------------------------------------------------------------------------------
// MiscStatements.cpp
// Miscellaneous statement definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/statements/MiscStatements.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace syntax;
using namespace parsing;

using ER = Statement::EvalResult;

Statement& DisableStatement::fromSyntax(Compilation& comp, const DisableStatementSyntax& syntax,
                                        const ASTContext& context) {
    auto& targetExpr = ArbitrarySymbolExpression::fromSyntax(comp, *syntax.name, context);
    if (targetExpr.bad())
        return badStmt(comp, nullptr);

    auto symbol = targetExpr.getSymbolReference();
    SLANG_ASSERT(symbol);

    if (symbol->kind != SymbolKind::StatementBlock &&
        (symbol->kind != SymbolKind::Subroutine ||
         symbol->as<SubroutineSymbol>().subroutineKind != SubroutineKind::Task)) {
        context.addDiag(diag::InvalidDisableTarget, syntax.name->sourceRange());
        return badStmt(comp, nullptr);
    }

    return *comp.emplace<DisableStatement>(targetExpr, syntax.sourceRange());
}

ER DisableStatement::evalImpl(EvalContext& context) const {
    // Hierarchical names are disallowed in constant expressions and constant functions
    auto& ase = target.as<ArbitrarySymbolExpression>();
    const bool isHierarchical = ase.hierRef.target != nullptr;
    if (isHierarchical) {
        context.addDiag(diag::ConstEvalHierarchicalName, sourceRange) << ase.symbol->name;
        return ER::Fail;
    }

    SLANG_ASSERT(!context.getDisableTarget());
    context.setDisableTarget(ase.symbol, sourceRange);
    return ER::Disable;
}

void DisableStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("target", target);
}

ER VariableDeclStatement::evalImpl(EvalContext& context) const {
    // Figure out the initial value for the variable.
    ConstantValue initial;
    if (auto initializer = symbol.getInitializer()) {
        // Initialization of static variables is skipped in constant functions.
        // This is confusing so issue a warning.
        if (symbol.lifetime == VariableLifetime::Static && !initializer->bad()) {
            context.addDiag(diag::ConstEvalStaticSkipped, initializer->sourceRange);
        }
        else {
            initial = initializer->eval(context);
            if (!initial)
                return ER::Fail;
        }
    }

    if (!initial)
        initial = symbol.getType().getDefaultValue();

    // Create storage for the variable.
    context.createLocal(&symbol, initial);
    return ER::Success;
}

void VariableDeclStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.writeLink("symbol", symbol);
}

Statement& ExpressionStatement::fromSyntax(Compilation& compilation,
                                           const ExpressionStatementSyntax& syntax,
                                           const ASTContext& context, StatementContext& stmtCtx) {
    bitmask<ASTFlags> extraFlags = ASTFlags::AssignmentAllowed | ASTFlags::TopLevelStatement;
    if (stmtCtx.flags.has(StatementFlags::InForLoop) &&
        BinaryExpressionSyntax::isKind(syntax.expr->kind) &&
        !compilation.hasFlag(CompilationFlags::StrictDriverChecking)) {
        extraFlags |= ASTFlags::NotADriver;
    }

    auto& expr = Expression::bind(*syntax.expr, context, extraFlags);
    auto result = compilation.emplace<ExpressionStatement>(expr, syntax.sourceRange());
    if (expr.bad())
        return badStmt(compilation, result);

    // Only a subset of expressions are allowed as statements.
    bool ok;
    switch (expr.kind) {
        case ExpressionKind::Call: {
            auto subKind = expr.as<CallExpression>().getSubroutineKind();
            if (!expr.type->isVoid() && subKind == SubroutineKind::Function) {
                context.addDiag(diag::UnusedResult, expr.sourceRange)
                    << expr.as<CallExpression>().getSubroutineName();
            }
            ok = true;
            break;
        }
        case ExpressionKind::Assignment: {
            const AssignmentExpression& ae = expr.as<AssignmentExpression>();
            if (ae.isBlocking() && ae.timingControl)
                stmtCtx.observeTiming(*ae.timingControl);

            ok = true;
            break;
        }
        case ExpressionKind::NewClass:
            ok = true;
            break;
        case ExpressionKind::UnaryOp: {
            auto& unary = expr.as<UnaryExpression>();
            ok = unary.op == UnaryOperator::Preincrement ||
                 unary.op == UnaryOperator::Predecrement ||
                 unary.op == UnaryOperator::Postincrement ||
                 unary.op == UnaryOperator::Postdecrement;
            break;
        }
        default:
            ok = false;
            break;
    }

    if (!ok) {
        context.addDiag(diag::ExprNotStatement, expr.sourceRange);
        return badStmt(compilation, result);
    }

    return *result;
}

Statement& ExpressionStatement::fromSyntax(Compilation& compilation,
                                           const VoidCastedCallStatementSyntax& syntax,
                                           const ASTContext& context) {
    auto& expr = Expression::bind(*syntax.expr, context, ASTFlags::TopLevelStatement);
    auto result = compilation.emplace<ExpressionStatement>(expr, syntax.sourceRange());
    if (expr.bad())
        return badStmt(compilation, result);

    if (expr.kind != ExpressionKind::Call ||
        (expr.as<CallExpression>().getSubroutineKind() == SubroutineKind::Task &&
         expr.type->isVoid())) {
        context.addDiag(diag::VoidCastFuncCall, expr.sourceRange);
        return badStmt(compilation, result);
    }

    if (expr.type->isVoid()) {
        context.addDiag(diag::PointlessVoidCast, expr.sourceRange)
            << expr.as<CallExpression>().getSubroutineName();
    }

    return *result;
}

ER ExpressionStatement::evalImpl(EvalContext& context) const {
    // Skip system task invocations.
    if (expr.kind == ExpressionKind::Call && expr.as<CallExpression>().isSystemCall() &&
        expr.as<CallExpression>().getSubroutineKind() == SubroutineKind::Task) {
        context.addDiag(diag::ConstSysTaskIgnored, expr.sourceRange)
            << expr.as<CallExpression>().getSubroutineName();
        return ER::Success;
    }

    return expr.eval(context) ? ER::Success : ER::Fail;
}

void ExpressionStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
}

Statement& TimedStatement::fromSyntax(Compilation& compilation,
                                      const TimingControlStatementSyntax& syntax,
                                      const ASTContext& context, StatementContext& stmtCtx) {
    auto& timing = TimingControl::bind(*syntax.timingControl, context);
    stmtCtx.observeTiming(timing);

    auto& stmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<TimedStatement>(timing, stmt, syntax.sourceRange());

    if (timing.bad() || stmt.bad())
        return badStmt(compilation, result);

    return *result;
}

ER TimedStatement::evalImpl(EvalContext& context) const {
    if (context.flags.has(EvalFlags::IsScript))
        return stmt.eval(context);

    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

void TimedStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("timing", timing);
    serializer.write("stmt", stmt);
}

static void checkDeferredAssertAction(const Statement& stmt, const ASTContext& context) {
    if (stmt.bad() || stmt.kind == StatementKind::Empty)
        return;

    // The statement inside a deferred assertion action block must be a subroutine call.
    if (stmt.kind != StatementKind::ExpressionStatement ||
        stmt.as<ExpressionStatement>().expr.kind != ExpressionKind::Call) {
        context.addDiag(diag::InvalidDeferredAssertAction, stmt.sourceRange);
        return;
    }

    // The subroutine being called has some restrictions:
    // - No output or inout arguments
    // - If a system call, must be a task or void returning
    // - Any ref arguments cannot reference automatic or dynamic variables
    auto& call = stmt.as<ExpressionStatement>().expr.as<CallExpression>();
    AssertionExpr::checkAssertionCall(call, context, diag::DeferredAssertOutArg,
                                      diag::DeferredAssertAutoRefArg, diag::DeferredAssertNonVoid,
                                      stmt.sourceRange, /* isInsideSequence */ false);
}

Statement& ImmediateAssertionStatement::fromSyntax(Compilation& compilation,
                                                   const ImmediateAssertionStatementSyntax& syntax,
                                                   const ASTContext& context,
                                                   StatementContext& stmtCtx) {
    AssertionKind assertKind = SemanticFacts::getAssertKind(syntax.kind);
    auto& cond = Expression::bind(*syntax.expr->expression, context);
    bool bad = cond.bad();

    if (!bad && !context.requireBooleanConvertible(cond))
        bad = true;

    const Statement* ifTrue = nullptr;
    const Statement* ifFalse = nullptr;
    if (syntax.action->statement)
        ifTrue = &Statement::bind(*syntax.action->statement, context, stmtCtx);

    if (syntax.action->elseClause) {
        ifFalse = &Statement::bind(syntax.action->elseClause->clause->as<StatementSyntax>(),
                                   context, stmtCtx);
    }

    bool isDeferred = syntax.delay != nullptr;
    bool isFinal = false;
    if (isDeferred)
        isFinal = syntax.delay->finalKeyword.valid();

    bool isCover = assertKind == AssertionKind::CoverProperty ||
                   assertKind == AssertionKind::CoverSequence;
    if (isCover && ifFalse) {
        context.addDiag(diag::CoverStmtNoFail, syntax.action->elseClause->sourceRange());
        bad = true;
    }

    if (isDeferred) {
        if (ifTrue)
            checkDeferredAssertAction(*ifTrue, context);
        if (ifFalse)
            checkDeferredAssertAction(*ifFalse, context);
    }

    auto result = compilation.emplace<ImmediateAssertionStatement>(assertKind, cond, ifTrue,
                                                                   ifFalse, isDeferred, isFinal,
                                                                   syntax.sourceRange());
    if (bad || (ifTrue && ifTrue->bad()) || (ifFalse && ifFalse->bad()))
        return badStmt(compilation, result);

    return *result;
}

ER ImmediateAssertionStatement::evalImpl(EvalContext& context) const {
    auto result = cond.eval(context);
    if (result.bad())
        return ER::Fail;

    if (isDeferred) {
        context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
        return ER::Fail;
    }

    if (result.isTrue()) {
        if (ifTrue)
            return ifTrue->eval(context);
        return ER::Success;
    }

    if (ifFalse)
        return ifFalse->eval(context);

    bool isCover = assertionKind == AssertionKind::CoverProperty ||
                   assertionKind == AssertionKind::CoverSequence;
    if (isCover)
        return ER::Success;

    context.addDiag(diag::ConstEvalAssertionFailed, sourceRange);
    return ER::Fail;
}

void ImmediateAssertionStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("cond", cond);
    if (ifTrue)
        serializer.write("ifTrue", *ifTrue);
    if (ifFalse)
        serializer.write("ifFalse", *ifFalse);
    serializer.write("assertionKind", toString(assertionKind));
    serializer.write("isDeferred", isDeferred);
    serializer.write("isFinal", isFinal);
}

Statement& ConcurrentAssertionStatement::fromSyntax(
    Compilation& compilation, const ConcurrentAssertionStatementSyntax& syntax,
    const ASTContext& context, StatementContext& stmtCtx) {

    if (context.flags.has(ASTFlags::ConcurrentAssertActionBlock)) {
        context.addDiag(diag::ConcurrentAssertActionBlock, syntax.sourceRange())
            << syntax.keyword.valueText();
        return badStmt(compilation, nullptr);
    }

    ASTContext ctx = context;
    ctx.clearInstanceAndProc();

    AssertionKind assertKind = SemanticFacts::getAssertKind(syntax.kind);
    auto& prop = AssertionExpr::bind(*syntax.propertySpec, ctx);
    bool bad = prop.bad();

    ctx.flags |= ASTFlags::ConcurrentAssertActionBlock;
    const Statement* ifTrue = nullptr;
    const Statement* ifFalse = nullptr;
    if (syntax.action->statement)
        ifTrue = &Statement::bind(*syntax.action->statement, ctx, stmtCtx);

    if (syntax.action->elseClause) {
        ifFalse = &Statement::bind(syntax.action->elseClause->clause->as<StatementSyntax>(), ctx,
                                   stmtCtx);
    }

    const bool isCover = assertKind == AssertionKind::CoverProperty ||
                         assertKind == AssertionKind::CoverSequence;
    if (isCover && ifFalse) {
        ctx.addDiag(diag::CoverStmtNoFail, syntax.action->elseClause->sourceRange());
        bad = true;
    }
    else if (assertKind == AssertionKind::Restrict &&
             (ifFalse || (ifTrue && ifTrue->kind != StatementKind::Empty))) {
        ctx.addDiag(diag::RestrictStmtNoFail, syntax.action->sourceRange());
        bad = true;
    }

    auto result = compilation.emplace<ConcurrentAssertionStatement>(assertKind, prop, ifTrue,
                                                                    ifFalse, syntax.sourceRange());
    if (bad || (ifTrue && ifTrue->bad()) || (ifFalse && ifFalse->bad()))
        return badStmt(compilation, result);

    if (assertKind == AssertionKind::Expect && !context.requireTimingAllowed(result->sourceRange))
        return badStmt(compilation, result);

    return *result;
}

ER ConcurrentAssertionStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

void ConcurrentAssertionStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("propertySpec", propertySpec);
    if (ifTrue)
        serializer.write("ifTrue", *ifTrue);
    if (ifFalse)
        serializer.write("ifFalse", *ifFalse);
    serializer.write("assertionKind", toString(assertionKind));
}

Statement& DisableForkStatement::fromSyntax(Compilation& compilation,
                                            const DisableForkStatementSyntax& syntax) {
    return *compilation.emplace<DisableForkStatement>(syntax.sourceRange());
}

ER DisableForkStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

Statement& WaitStatement::fromSyntax(Compilation& compilation, const WaitStatementSyntax& syntax,
                                     const ASTContext& context, StatementContext& stmtCtx) {
    auto& cond = Expression::bind(*syntax.expr, context);
    auto& stmt = Statement::bind(*syntax.statement, context, stmtCtx);
    auto result = compilation.emplace<WaitStatement>(cond, stmt, syntax.sourceRange());
    if (cond.bad() || stmt.bad())
        return badStmt(compilation, result);

    if (!context.requireBooleanConvertible(cond))
        return badStmt(compilation, result);

    if (!context.requireTimingAllowed(result->sourceRange))
        return badStmt(compilation, result);

    return *result;
}

ER WaitStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

void WaitStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("cond", cond);
    serializer.write("stmt", stmt);
}

Statement& WaitForkStatement::fromSyntax(Compilation& compilation,
                                         const WaitForkStatementSyntax& syntax,
                                         const ASTContext& context) {
    auto result = compilation.emplace<WaitForkStatement>(syntax.sourceRange());

    if (!context.requireTimingAllowed(result->sourceRange))
        return badStmt(compilation, result);

    return *result;
}

ER WaitForkStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

Statement& WaitOrderStatement::fromSyntax(Compilation& compilation,
                                          const WaitOrderStatementSyntax& syntax,
                                          const ASTContext& context, StatementContext& stmtCtx) {
    SmallVector<const Expression*> events;
    for (auto name : syntax.names) {
        auto& ev = Expression::bind(*name, context);
        if (ev.bad())
            return badStmt(compilation, nullptr);

        if (!ev.type->isEvent()) {
            context.addDiag(diag::NotAnEvent, name->sourceRange());
            return badStmt(compilation, nullptr);
        }

        events.push_back(&ev);
    }

    const Statement* ifTrue = nullptr;
    const Statement* ifFalse = nullptr;
    if (syntax.action->statement)
        ifTrue = &Statement::bind(*syntax.action->statement, context, stmtCtx);

    if (syntax.action->elseClause) {
        ifFalse = &Statement::bind(syntax.action->elseClause->clause->as<StatementSyntax>(),
                                   context, stmtCtx);
    }

    auto result = compilation.emplace<WaitOrderStatement>(events.copy(compilation), ifTrue, ifFalse,
                                                          syntax.sourceRange());

    if (!context.requireTimingAllowed(result->sourceRange))
        return badStmt(compilation, result);

    return *result;
}

ER WaitOrderStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

void WaitOrderStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("events");
    for (auto ev : events) {
        serializer.startObject();
        serializer.write("target", *ev);
        serializer.endObject();
    }
    serializer.endArray();

    if (ifTrue)
        serializer.write("ifTrue", *ifTrue);
    if (ifFalse)
        serializer.write("ifFalse", *ifFalse);
}

Statement& EventTriggerStatement::fromSyntax(Compilation& compilation,
                                             const EventTriggerStatementSyntax& syntax,
                                             const ASTContext& context, StatementContext& stmtCtx) {
    auto& target = Expression::bindLValue(*syntax.name, context);
    if (target.bad())
        return badStmt(compilation, nullptr);

    if (!target.type->isEvent()) {
        context.addDiag(diag::NotAnEvent, syntax.name->sourceRange());
        return badStmt(compilation, nullptr);
    }

    const TimingControl* timing = nullptr;
    if (syntax.timing) {
        timing = &TimingControl::bind(*syntax.timing, context);
        stmtCtx.observeTiming(*timing);
    }

    bool isNonBlocking = syntax.kind == SyntaxKind::NonblockingEventTriggerStatement;

    return *compilation.emplace<EventTriggerStatement>(target, timing, isNonBlocking,
                                                       syntax.sourceRange());
}

ER EventTriggerStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
    return ER::Fail;
}

void EventTriggerStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("target", target);
    serializer.write("isNonBlocking", isNonBlocking);
    if (timing)
        serializer.write("timing", *timing);
}

static bool isValidAssignLVal(const Expression& expr) {
    switch (expr.kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue:
            if (auto sym = expr.getSymbolReference()) {
                if (!VariableSymbol::isKind(sym->kind))
                    return false;
            }
            return true;
        case ExpressionKind::Concatenation:
            for (auto op : expr.as<ConcatenationExpression>().operands()) {
                if (!isValidAssignLVal(*op))
                    return false;
            }
            return true;
        default:
            return false;
    }
}

static bool isValidForceLVal(const Expression& expr, const ASTContext& context, bool inSelect) {
    switch (expr.kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue:
            if (auto sym = expr.getSymbolReference()) {
                if (inSelect && VariableSymbol::isKind(sym->kind))
                    return false;

                if (sym->kind == SymbolKind::Net && !sym->as<NetSymbol>().netType.isBuiltIn())
                    context.addDiag(diag::BadForceNetType, expr.sourceRange);
            }
            return true;
        case ExpressionKind::MemberAccess:
            return isValidForceLVal(expr.as<MemberAccessExpression>().value(), context, true);
        case ExpressionKind::ElementSelect:
            return isValidForceLVal(expr.as<ElementSelectExpression>().value(), context, true);
        case ExpressionKind::RangeSelect:
            return isValidForceLVal(expr.as<RangeSelectExpression>().value(), context, true);
        case ExpressionKind::Concatenation:
            for (auto op : expr.as<ConcatenationExpression>().operands()) {
                if (!isValidForceLVal(*op, context, false))
                    return false;
            }
            return true;
        default:
            return false;
    }
}

Statement& ProceduralAssignStatement::fromSyntax(Compilation& compilation,
                                                 const ProceduralAssignStatementSyntax& syntax,
                                                 const ASTContext& context) {
    bool isForce = syntax.keyword.kind == TokenKind::ForceKeyword;
    bitmask<ASTFlags> astFlags = ASTFlags::NonProcedural | ASTFlags::AssignmentAllowed;
    if (isForce)
        astFlags |= ASTFlags::ProceduralForceRelease;
    else
        astFlags |= ASTFlags::ProceduralAssign;

    auto& assign = Expression::bind(*syntax.expr, context, astFlags);
    auto result = compilation.emplace<ProceduralAssignStatement>(assign, isForce,
                                                                 syntax.sourceRange());
    if (assign.bad())
        return badStmt(compilation, result);

    if (assign.kind == ExpressionKind::Assignment) {
        auto& lval = assign.as<AssignmentExpression>().left();
        if (isForce) {
            if (!isValidForceLVal(lval, context, false)) {
                context.addDiag(diag::BadProceduralForce, lval.sourceRange);
                return badStmt(compilation, result);
            }
        }
        else {
            if (!isValidAssignLVal(lval)) {
                context.addDiag(diag::BadProceduralAssign, lval.sourceRange);
                return badStmt(compilation, result);
            }
        }
    }

    return *result;
}

ER ProceduralAssignStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalProceduralAssign, sourceRange);
    return ER::Fail;
}

void ProceduralAssignStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("assignment", assignment);
    serializer.write("isForce", isForce);
}

Statement& ProceduralDeassignStatement::fromSyntax(Compilation& compilation,
                                                   const ProceduralDeassignStatementSyntax& syntax,
                                                   const ASTContext& context) {
    auto ctx = context.resetFlags(ASTFlags::NonProcedural | ASTFlags::ProceduralForceRelease);
    auto& lvalue = Expression::bindLValue(*syntax.variable, ctx);

    bool isRelease = syntax.keyword.kind == TokenKind::ReleaseKeyword;
    auto result = compilation.emplace<ProceduralDeassignStatement>(lvalue, isRelease,
                                                                   syntax.sourceRange());
    if (lvalue.bad())
        return badStmt(compilation, result);

    if (isRelease) {
        if (!isValidForceLVal(lvalue, ctx, false)) {
            ctx.addDiag(diag::BadProceduralForce, lvalue.sourceRange);
            return badStmt(compilation, result);
        }
    }
    else {
        if (!isValidAssignLVal(lvalue)) {
            ctx.addDiag(diag::BadProceduralAssign, lvalue.sourceRange);
            return badStmt(compilation, result);
        }
    }

    return *result;
}

ER ProceduralDeassignStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalProceduralAssign, sourceRange);
    return ER::Fail;
}

void ProceduralDeassignStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.write("lvalue", lvalue);
    serializer.write("isRelease", isRelease);
}

Statement& RandCaseStatement::fromSyntax(Compilation& compilation,
                                         const RandCaseStatementSyntax& syntax,
                                         const ASTContext& context, StatementContext& stmtCtx) {
    bool bad = false;
    SmallVector<Item, 8> items;
    for (auto item : syntax.items) {
        auto& expr = Expression::bind(*item->expr, context);
        auto& stmt = Statement::bind(*item->statement, context, stmtCtx);
        items.push_back({&expr, &stmt});

        if (stmt.bad() || !context.requireIntegral(expr)) {
            bad = true;
        }
    }

    auto result = compilation.emplace<RandCaseStatement>(items.copy(compilation),
                                                         syntax.sourceRange());
    if (bad)
        return badStmt(compilation, result);

    return *result;
}

ER RandCaseStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalRandValue, sourceRange);
    return ER::Fail;
}

void RandCaseStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("items");
    for (auto& item : items) {
        serializer.startObject();
        serializer.write("expr", *item.expr);
        serializer.write("stmt", *item.stmt);
        serializer.endObject();
    }
    serializer.endArray();
}

Statement& RandSequenceStatement::fromSyntax(Compilation& compilation,
                                             const RandSequenceStatementSyntax& syntax,
                                             const ASTContext& context) {
    SourceRange firstProdRange;
    const RandSeqProductionSymbol* firstProd = nullptr;
    if (syntax.firstProduction) {
        firstProdRange = syntax.firstProduction.range();
        firstProd = RandSeqProductionSymbol::findProduction(syntax.firstProduction.valueText(),
                                                            firstProdRange, context);
    }
    else {
        auto prodRange = context.scope->membersOfType<RandSeqProductionSymbol>();
        if (prodRange.begin() != prodRange.end()) {
            firstProd = &*prodRange.begin();
            firstProdRange = {syntax.randsequence.location(), syntax.closeParen.range().end()};
        }
    }

    if (firstProd) {
        // Make sure the first production doesn't require arguments.
        SmallVector<const Expression*> args;
        CallExpression::bindArgs(nullptr, firstProd->arguments, firstProd->name, firstProdRange,
                                 context, args, /* isBuiltInMethod */ false);
    }

    // All of the logic for creating productions is in the RandSeqProduction symbol.
    return *compilation.emplace<RandSequenceStatement>(firstProd, syntax.sourceRange());
}

ER RandSequenceStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalRandValue, sourceRange);
    return ER::Fail;
}

void RandSequenceStatement::serializeTo(ASTSerializer& serializer) const {
    if (firstProduction)
        serializer.writeLink("firstProduction", *firstProduction);
}

Statement& ProceduralCheckerStatement::fromSyntax(Compilation& comp,
                                                  const CheckerInstanceStatementSyntax& syntax,
                                                  const ASTContext& context) {
    // Find all of the checkers that were pre-created for this syntax node.
    // It's possible to not find them if there were errors in the declaration,
    // so we don't issue errors here -- they are already handled.
    SmallVector<const Symbol*> instances;
    for (auto instSyntax : syntax.instance->instances) {
        if (auto decl = instSyntax->decl) {
            if (auto sym = context.scope->find(decl->name.valueText())) {
                auto nestedSym = sym;
                while (nestedSym->kind == SymbolKind::InstanceArray) {
                    auto& array = nestedSym->as<InstanceArraySymbol>();
                    if (array.elements.empty())
                        break;

                    nestedSym = array.elements[0];
                }

                if (nestedSym->kind == SymbolKind::CheckerInstance)
                    instances.push_back(sym);
            }
        }
    }

    return *comp.emplace<ProceduralCheckerStatement>(instances.copy(comp), syntax.sourceRange());
}

ER ProceduralCheckerStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalCheckers, sourceRange);
    return ER::Fail;
}

void ProceduralCheckerStatement::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("instances");
    for (auto inst : instances) {
        serializer.startObject();
        serializer.writeLink("instance", *inst);
        serializer.endObject();
    }
    serializer.endArray();
}

} // namespace slang::ast
