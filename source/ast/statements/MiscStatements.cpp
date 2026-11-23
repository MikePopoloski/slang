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
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/DeclarationsDiags.h"
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
    // Check the size limit up front to avoid running out of memory on huge variables.
    if (!context.checkBitCount(symbol.getType().getBitstreamWidth(), sourceRange))
        return ER::Fail;

    // Static variables retain their values across calls at runtime, which
    // constant evaluation doesn't model (their initializers are skipped).
    // That's the defined behavior for constant function calls, but when
    // we're only speculatively evaluating an expression that isn't required
    // to be constant, the result would not match the runtime value, so
    // give up instead.
    if (symbol.lifetime == VariableLifetime::Static) {
        if (!context.flags.has(EvalFlags::RequireConstant))
            return ER::Fail;

        // Without the flag this would have failed; see CallExpression::canMemoize.
        context.preventMemoization();
    }

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
    auto& expr = Expression::bind(*syntax.expr, context,
                                  ASTFlags::AssignmentAllowed | ASTFlags::TopLevelStatement);
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
    const bool isDeferred = syntax.delay != nullptr;
    if (!isDeferred) {
        // Immediate (non-deferred) assertions require a procedural context.
        // The isFromAssertion flag identifies synthetic procedural blocks created for
        // module-level assertion members, which are not valid for immediate assertions.
        // The action blocks of concurrent assertions can also contain them [16.14.1].
        auto proc = context.getProceduralBlock();
        bool inRealProcBlock = proc && !proc->isFromAssertion;
        if (!context.scope->isProceduralContext() && !inRealProcBlock &&
            !context.flags.has(ASTFlags::ConcurrentAssertActionBlock)) {
            context.addDiag(diag::ImmediateAssertNotInProc, syntax.sourceRange());
            return badStmt(compilation, nullptr);
        }
    }

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

    bool isFinal = false;
    if (isDeferred)
        isFinal = syntax.delay->finalKeyword.valid();

    AssertionKind assertKind = SemanticFacts::getAssertKind(syntax.kind);
    const bool isCover = assertKind == AssertionKind::CoverProperty ||
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

    AssertionKind assertKind = SemanticFacts::getAssertKind(syntax.kind);

    auto proc = context.getProceduralBlock();
    if (assertKind != AssertionKind::Expect &&
        (!proc || proc->procedureKind == ProceduralBlockKind::Final)) {
        context.addDiag(diag::ConcurrentAssertNotInProc, syntax.sourceRange());
        return badStmt(compilation, nullptr);
    }

    ASTContext ctx = context;
    ctx.clearSymbolCtx();

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

    if (assertKind == AssertionKind::CoverProperty && prop.canSucceedVacuously())
        ctx.addDiag(diag::VacuousCover, syntax.propertySpec->sourceRange());

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

    if ((ifTrue && ifTrue->bad()) || (ifFalse && ifFalse->bad()) ||
        !context.requireTimingAllowed(result->sourceRange)) {
        return badStmt(compilation, result);
    }

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
    auto& target = Expression::bind(*syntax.name, context);
    if (target.bad() || !target.requireLValue(context))
        return badStmt(compilation, nullptr);

    if (!target.type->isEvent()) {
        context.addDiag(diag::NotAnEvent, syntax.name->sourceRange());
        return badStmt(compilation, nullptr);
    }

    if (auto sym = target.getSymbolReference())
        compilation.noteReference(*sym, /* isLValue */ true);

    // The timing control on a nonblocking event trigger doesn't block the
    // statement [15.5.1], so like a nonblocking assignment's it isn't counted
    // as a blocking timing control.
    bool isNonBlocking = syntax.kind == SyntaxKind::NonblockingEventTriggerStatement;
    const TimingControl* timing = nullptr;
    if (syntax.timing) {
        ASTContext timingCtx = context;
        if (isNonBlocking)
            timingCtx.flags |= ASTFlags::NonBlockingTimingControl;

        timing = &TimingControl::bind(*syntax.timing, timingCtx);
        if (!isNonBlocking)
            stmtCtx.observeTiming(*timing);
    }

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
        case ExpressionKind::Assignment:
            if (auto sym = expr.getSymbolReference())
                return VariableSymbol::isKind(sym->kind);
            return false;
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

// [10.6.2] disallows a select of a variable or of a net with a user-defined nettype
// as a force / release target; a whole net of a user-defined nettype is fine [6.6.7].
// Selects of such nets are already reported as partial drivers when the target is
// checked as an lvalue, so only variable selects are diagnosed here. That doesn't
// leave the statement unusable, so the statement is kept.
static bool isValidForceLVal(const Expression& expr, const ASTContext& context,
                             const Expression* select) {
    switch (expr.kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue:
            if (auto sym = expr.getSymbolReference()) {
                if (select && VariableSymbol::isKind(sym->kind))
                    context.addDiag(diag::BadProceduralForce, select->sourceRange);
            }
            return true;
        case ExpressionKind::MemberAccess:
            return isValidForceLVal(expr.as<MemberAccessExpression>().value(), context,
                                    select ? select : &expr);
        case ExpressionKind::ElementSelect:
            return isValidForceLVal(expr.as<ElementSelectExpression>().value(), context,
                                    select ? select : &expr);
        case ExpressionKind::RangeSelect:
            return isValidForceLVal(expr.as<RangeSelectExpression>().value(), context,
                                    select ? select : &expr);
        case ExpressionKind::Concatenation:
            for (auto op : expr.as<ConcatenationExpression>().operands()) {
                if (!isValidForceLVal(*op, context, nullptr))
                    return false;
            }
            return true;
        case ExpressionKind::Assignment: {
            auto& assign = expr.as<AssignmentExpression>();
            if (assign.isLValueArg())
                return isValidForceLVal(assign.left(), context, select);
            return false;
        }
        default:
            return false;
    }
}

Statement& ProceduralAssignStatement::fromSyntax(Compilation& compilation,
                                                 const ProceduralAssignStatementSyntax& syntax,
                                                 const ASTContext& context) {
    bool isForce = syntax.keyword.kind == TokenKind::ForceKeyword;
    auto& assign = Expression::bind(*syntax.expr, context,
                                    ASTFlags::NonProcedural | ASTFlags::AssignmentAllowed);
    auto result = compilation.emplace<ProceduralAssignStatement>(assign, isForce,
                                                                 syntax.sourceRange());
    if (assign.bad())
        return badStmt(compilation, result);

    if (assign.kind == ExpressionKind::Assignment) {
        auto& lval = assign.as<AssignmentExpression>().left();
        if (isForce) {
            if (!isValidForceLVal(lval, context, nullptr)) {
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
    auto ctx = context.resetFlags(ASTFlags::NonProcedural);
    auto& lvalue = Expression::bind(*syntax.variable, ctx);

    bool isRelease = syntax.keyword.kind == TokenKind::ReleaseKeyword;
    auto result = compilation.emplace<ProceduralDeassignStatement>(lvalue, isRelease,
                                                                   syntax.sourceRange());
    if (lvalue.bad() || !lvalue.requireLValue(ctx))
        return badStmt(compilation, result);

    if (isRelease) {
        if (!isValidForceLVal(lvalue, ctx, nullptr)) {
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

Statement& RandSequenceStatement::fromSyntax(Compilation& comp,
                                             const RandSequenceStatementSyntax& syntax,
                                             const ASTContext& context) {
    // The rules of each production are bound here, with the context of the statement,
    // since code blocks in them are nested in the enclosing procedure [18.17.7].
    SmallVector<Production> productions;
    for (auto& prod : context.scope->membersOfType<RandSeqProductionSymbol>())
        productions.push_back({&prod, createRules(prod, context)});

    SourceRange firstProdRange;
    const RandSeqProductionSymbol* firstProd = nullptr;
    if (syntax.firstProduction) {
        firstProdRange = syntax.firstProduction.range();
        firstProd = RandSeqProductionSymbol::findProduction(syntax.firstProduction.valueText(),
                                                            firstProdRange, context);
    }
    else if (!productions.empty()) {
        firstProd = productions[0].symbol;
        firstProdRange = {syntax.randsequence.location(), syntax.closeParen.range().end()};
    }

    if (firstProd) {
        // Make sure the first production doesn't require arguments.
        SmallVector<const Expression*> args;
        CallExpression::bindArgs(nullptr, firstProd->arguments, firstProd->name, firstProdRange,
                                 context, args);
    }

    // All of the logic for creating productions is in the RandSeqProduction symbol.
    return *comp.emplace<RandSequenceStatement>(firstProd, productions.copy(comp),
                                                syntax.sourceRange());
}

std::span<const RandSequenceStatement::Rule> RandSequenceStatement::createRules(
    const RandSeqProductionSymbol& production, const ASTContext& parentContext) {
    auto syntax = production.getSyntax();
    SLANG_ASSERT(syntax);

    ASTContext context = parentContext;
    context.scope = &production;
    context.lookupIndex = SymbolIndex(UINT32_MAX);

    auto blocks = production.membersOfType<StatementBlockSymbol>();
    auto blockIt = blocks.begin();

    SmallVector<Rule, 8> buffer;
    for (auto rule : syntax->as<ProductionSyntax>().rules) {
        SLANG_ASSERT(blockIt != blocks.end());
        buffer.push_back(createRule(*rule, context, *blockIt++));
    }

    return buffer.copy(context.getCompilation());
}

RandSequenceStatement::ProdItem RandSequenceStatement::createProdItem(
    const RsProdItemSyntax& syntax, const ASTContext& context) {

    auto symbol = RandSeqProductionSymbol::findProduction(syntax.name.valueText(),
                                                          syntax.name.range(), context);
    if (!symbol)
        return ProdItem(nullptr, {});

    SmallVector<const Expression*> args;
    CallExpression::bindArgs(syntax.argList, symbol->arguments, symbol->name, syntax.sourceRange(),
                             context, args);

    return ProdItem(symbol, args.copy(context.getCompilation()));
}

const RandSequenceStatement::CaseProd& RandSequenceStatement::createCaseProd(
    const RsCaseSyntax& syntax, const ASTContext& context) {

    SmallVector<const ExpressionSyntax*> expressions;
    SmallVector<ProdItem, 8> prods;
    std::optional<ProdItem> defItem;

    for (auto item : syntax.items) {
        switch (item->kind) {
            case SyntaxKind::StandardRsCaseItem: {
                auto& sci = item->as<StandardRsCaseItemSyntax>();
                prods.push_back(createProdItem(*sci.item, context));
                for (auto es : sci.expressions)
                    expressions.push_back(es);
                break;
            }
            case SyntaxKind::DefaultRsCaseItem:
                // The parser already errored for duplicate defaults,
                // so just ignore if it happens here.
                if (!defItem)
                    defItem = createProdItem(*item->as<DefaultRsCaseItemSyntax>().item, context);
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    SmallVector<const Expression*> bound;
    Expression::bindMembershipExpressions(context, TokenKind::CaseKeyword,
                                          /* requireIntegral */ false,
                                          /* unwrapUnpacked */ false,
                                          /* allowTypeReferences */ true,
                                          /* allowValueRange */ true, *syntax.expr, expressions,
                                          bound);

    SmallVector<CaseItem, 8> items;
    SmallVector<const Expression*> group;
    auto& comp = context.getCompilation();
    auto boundIt = bound.begin();
    auto prodIt = prods.begin();
    auto expr = *boundIt++;

    for (auto item : syntax.items) {
        switch (item->kind) {
            case SyntaxKind::StandardRsCaseItem: {
                auto& sci = item->as<StandardRsCaseItemSyntax>();
                for (size_t i = 0; i < sci.expressions.size(); i++)
                    group.push_back(*boundIt++);

                items.push_back({group.copy(comp), *prodIt++});
                group.clear();
                break;
            }
            default:
                break;
        }
    }

    return *comp.emplace<CaseProd>(*expr, items.copy(comp), defItem);
}

RandSequenceStatement::Rule RandSequenceStatement::createRule(
    const RsRuleSyntax& syntax, const ASTContext& context, const StatementBlockSymbol& ruleBlock) {

    auto blockRange = ruleBlock.membersOfType<StatementBlockSymbol>();
    auto blockIt = blockRange.begin();

    auto& comp = context.getCompilation();
    SmallVector<const ProdBase*> prods;
    for (auto p : syntax.prods) {
        switch (p->kind) {
            case SyntaxKind::RsProdItem:
                prods.push_back(
                    comp.emplace<ProdItem>(createProdItem(p->as<RsProdItemSyntax>(), context)));
                break;
            case SyntaxKind::RsCodeBlock: {
                SLANG_ASSERT(blockIt != blockRange.end());
                prods.push_back(comp.emplace<CodeBlockProd>(*blockIt++));
                break;
            }
            case SyntaxKind::RsIfElse: {
                auto& ries = p->as<RsIfElseSyntax>();
                auto& expr = Expression::bind(*ries.condition, context);
                auto ifItem = createProdItem(*ries.ifItem, context);

                std::optional<ProdItem> elseItem;
                if (ries.elseClause)
                    elseItem = createProdItem(*ries.elseClause->item, context);

                if (!expr.bad())
                    context.requireBooleanConvertible(expr);

                prods.push_back(comp.emplace<IfElseProd>(expr, ifItem, elseItem));
                break;
            }
            case SyntaxKind::RsRepeat: {
                auto& rrs = p->as<RsRepeatSyntax>();
                auto& expr = Expression::bind(*rrs.expr, context);
                auto item = createProdItem(*rrs.item, context);
                prods.push_back(comp.emplace<RepeatProd>(expr, item));

                context.requireIntegral(expr);
                break;
            }
            case SyntaxKind::RsCase:
                prods.push_back(&createCaseProd(p->as<RsCaseSyntax>(), context));
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    const Expression* weightExpr = nullptr;
    std::optional<CodeBlockProd> codeBlock;
    if (auto wc = syntax.weightClause) {
        weightExpr = &Expression::bind(*wc->weight, context);
        if (context.requireIntegral(*weightExpr)) {
            // Weights must be non-negative [18.17.1]; check it when the value is constant.
            auto cv = context.tryEval(*weightExpr);
            if (cv.isInteger() && cv.integer().isSigned() && cv.integer().isNegative())
                context.addDiag(diag::RandSeqNegativeWeight, weightExpr->sourceRange) << cv;
        }

        if (wc->codeBlock) {
            SLANG_ASSERT(blockIt != blockRange.end());
            codeBlock = CodeBlockProd(*blockIt++);
        }
    }

    bool isRandJoin = false;
    const Expression* randJoinExpr = nullptr;
    if (syntax.randJoin) {
        isRandJoin = true;
        if (syntax.randJoin->expr) {
            randJoinExpr = &Expression::bind(*syntax.randJoin->expr, context);

            if (!randJoinExpr->bad() && !randJoinExpr->type->isNumeric()) {
                context.addDiag(diag::RandJoinNotNumeric, randJoinExpr->sourceRange)
                    << *randJoinExpr->type;
            }
            else if (!randJoinExpr->bad()) {
                // The bias must be in the range 0.0 to 1.0 [18.17.5]; check it when
                // the value is constant.
                auto cv = context.tryEval(*randJoinExpr);
                if (cv.isInteger() || cv.isReal() || cv.isShortReal()) {
                    double value = cv.convertToReal().real();
                    if (value < 0.0 || value > 1.0)
                        context.addDiag(diag::RandJoinOutOfRange, randJoinExpr->sourceRange) << cv;
                }
            }
        }
    }

    for (auto& block : blockRange) {
        Statement::StatementContext stmtCtx(context);
        stmtCtx.flags = StatementFlags::InRandSeq;
        block.getStatement(context, stmtCtx);
    }

    return {ruleBlock, prods.copy(comp), weightExpr, randJoinExpr, codeBlock, isRandJoin};
}

ER RandSequenceStatement::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalRandValue, sourceRange);
    return ER::Fail;
}

void RandSequenceStatement::serializeTo(ASTSerializer& serializer) const {
    auto writeItem = [&](std::string_view propName, const ProdItem& item) {
        serializer.writeProperty(propName);
        serializer.startObject();
        if (item.target)
            serializer.writeLink("target", *item.target);

        serializer.startArray("args");
        for (auto arg : item.args)
            serializer.serialize(*arg);
        serializer.endArray();

        serializer.endObject();
    };

    auto writeCodeBlock = [&](std::string_view propName, const CodeBlockProd& codeBlock) {
        if (auto stmt = codeBlock.block->tryGetStatement())
            serializer.write(propName, *stmt);
    };

    if (firstProduction)
        serializer.writeLink("firstProduction", *firstProduction);

    serializer.startArray("productions");
    for (auto& production : productions) {
        serializer.startObject();
        serializer.writeLink("symbol", *production.symbol);

        serializer.startArray("rules");
        for (auto& rule : production.rules) {
            serializer.startObject();

            serializer.startArray("prods");
            for (auto prod : rule.prods) {
                serializer.startObject();
                switch (prod->kind) {
                    case ProdKind::Item:
                        serializer.write("kind", "Item"sv);
                        writeItem("item", *(const ProdItem*)prod);
                        break;
                    case ProdKind::CodeBlock:
                        serializer.write("kind", "CodeBlock"sv);
                        writeCodeBlock("body", *(const CodeBlockProd*)prod);
                        break;
                    case ProdKind::IfElse: {
                        auto& iep = *(const IfElseProd*)prod;
                        serializer.write("kind", "IfElse"sv);
                        serializer.write("expr", *iep.expr);

                        writeItem("ifItem", iep.ifItem);
                        if (iep.elseItem)
                            writeItem("elseItem", *iep.elseItem);
                        break;
                    }
                    case ProdKind::Repeat: {
                        auto& rp = *(const RepeatProd*)prod;
                        serializer.write("kind", "Repeat"sv);
                        serializer.write("expr", *rp.expr);
                        writeItem("item", rp.item);
                        break;
                    }
                    case ProdKind::Case: {
                        auto& cp = *(const CaseProd*)prod;
                        serializer.write("kind", "Case"sv);
                        serializer.write("expr", *cp.expr);
                        if (cp.defaultItem)
                            writeItem("defaultItem", *cp.defaultItem);

                        serializer.startArray("items");
                        for (auto& item : cp.items) {
                            serializer.startObject();
                            serializer.startArray("expressions");
                            for (auto expr : item.expressions)
                                serializer.serialize(*expr);
                            serializer.endArray();

                            writeItem("item", item.item);
                            serializer.endObject();
                        }
                        serializer.endArray();
                        break;
                    }
                }
                serializer.endObject();
            }
            serializer.endArray();

            if (rule.weightExpr)
                serializer.write("weightExpr", *rule.weightExpr);

            if (rule.codeBlock)
                writeCodeBlock("codeBlock", *rule.codeBlock);

            serializer.write("isRandJoin", rule.isRandJoin);
            if (rule.randJoinExpr)
                serializer.write("randJoinExpr", *rule.randJoinExpr);

            serializer.endObject();
        }
        serializer.endArray();
        serializer.endObject();
    }
    serializer.endArray();
}

Statement& ProceduralCheckerStatement::fromSyntax(Compilation& comp,
                                                  const CheckerInstanceStatementSyntax& syntax,
                                                  const ASTContext& context,
                                                  StatementContext& stmtCtx) {
    auto proc = context.getProceduralBlock();
    if (!proc || proc->procedureKind == ProceduralBlockKind::Final) {
        context.addDiag(diag::CheckerNotInProc, syntax.sourceRange());
        return badStmt(comp, nullptr);
    }

    if (stmtCtx.flags.has(StatementFlags::InForkJoin)) {
        context.addDiag(diag::CheckerInForkJoin, syntax.sourceRange());
        return badStmt(comp, nullptr);
    }

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
