//------------------------------------------------------------------------------
// TimingControl.cpp
// Timing control creation and analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/TimingControl.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/Expression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/types/Type.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

TimingControl& TimingControl::bind(const TimingControlSyntax& syntax, const ASTContext& context) {
    auto& comp = context.getCompilation();
    if (context.flags.has(ASTFlags::Function | ASTFlags::Final) || context.inAlwaysCombLatch()) {
        context.addDiag(diag::TimingInFuncNotAllowed, syntax.sourceRange());
        return badCtrl(comp, nullptr);
    }

    TimingControl* result;
    switch (syntax.kind) {
        case SyntaxKind::DelayControl:
            result = &DelayControl::fromSyntax(comp, syntax.as<DelaySyntax>(), context);
            break;
        case SyntaxKind::Delay3:
            result = &Delay3Control::fromSyntax(comp, syntax.as<Delay3Syntax>(), context);
            break;
        case SyntaxKind::EventControl:
            result = &SignalEventControl::fromSyntax(comp, syntax.as<EventControlSyntax>(),
                                                     context);
            break;
        case SyntaxKind::EventControlWithExpression:
            result = &EventListControl::fromSyntax(
                comp, *syntax.as<EventControlWithExpressionSyntax>().expr, context);
            break;
        case SyntaxKind::ImplicitEventControl:
            result = &ImplicitEventControl::fromSyntax(comp,
                                                       syntax.as<ImplicitEventControlSyntax>(),
                                                       context);
            break;
        case SyntaxKind::RepeatedEventControl:
            result = &RepeatedEventControl::fromSyntax(comp,
                                                       syntax.as<RepeatedEventControlSyntax>(),
                                                       context);
            break;
        case SyntaxKind::OneStepDelay:
            result = comp.emplace<OneStepDelayControl>(syntax.sourceRange());
            break;
        case SyntaxKind::CycleDelay:
            result = &CycleDelayControl::fromSyntax(comp, syntax.as<DelaySyntax>(), context);
            break;
        default:
            SLANG_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

// This function is called when creating event expression arguments for a sequence or
// property instantiation. We don't know enough information at parse time to parse this
// into an actual EventExpressionSyntax, so instead we end up with a PropertyExprSyntax
// that we need to try to fit into an event expression (or report an error if we cannot).
TimingControl& TimingControl::bind(const PropertyExprSyntax& syntax, const ASTContext& context) {
    auto& comp = context.getCompilation();
    if (context.flags.has(ASTFlags::Function | ASTFlags::Final) || context.inAlwaysCombLatch()) {
        context.addDiag(diag::TimingInFuncNotAllowed, syntax.sourceRange());
        return badCtrl(comp, nullptr);
    }

    TimingControl* result;
    switch (syntax.kind) {
        case SyntaxKind::SimplePropertyExpr:
            return bind(*syntax.as<SimplePropertyExprSyntax>().expr, context);
        case SyntaxKind::ParenthesizedPropertyExpr:
            result = &EventListControl::fromSyntax(comp,
                                                   syntax.as<ParenthesizedPropertyExprSyntax>(),
                                                   context);
            break;
        case SyntaxKind::OrPropertyExpr:
            result = &EventListControl::fromSyntax(comp, syntax.as<BinaryPropertyExprSyntax>(),
                                                   context);
            break;
        case SyntaxKind::IffPropertyExpr:
            result = &SignalEventControl::fromSyntax(comp, syntax.as<BinaryPropertyExprSyntax>(),
                                                     context);
            break;
        default:
            context.addDiag(diag::InvalidSyntaxInEventExpr, syntax.sourceRange());
            return badCtrl(comp, nullptr);
    }

    result->syntax = &syntax;
    return *result;
}

TimingControl& TimingControl::bind(const SequenceExprSyntax& syntax, const ASTContext& context) {
    auto& comp = context.getCompilation();
    TimingControl* result;
    switch (syntax.kind) {
        case SyntaxKind::SimpleSequenceExpr:
            result = &SignalEventControl::fromSyntax(comp, syntax.as<SimpleSequenceExprSyntax>(),
                                                     context);
            break;
        case SyntaxKind::ParenthesizedSequenceExpr:
            result = &EventListControl::fromSyntax(comp,
                                                   syntax.as<ParenthesizedSequenceExprSyntax>(),
                                                   context);
            break;
        case SyntaxKind::OrSequenceExpr:
            result = &EventListControl::fromSyntax(comp, syntax.as<BinarySequenceExprSyntax>(),
                                                   context);
            break;
        case SyntaxKind::SignalEventExpression:
            result = &SignalEventControl::fromSyntax(comp, syntax.as<SignalEventExpressionSyntax>(),
                                                     context);
            break;
        default:
            context.addDiag(diag::InvalidSyntaxInEventExpr, syntax.sourceRange());
            return badCtrl(comp, nullptr);
    }

    result->syntax = &syntax;
    return *result;
}

TimingControl& TimingControl::badCtrl(Compilation& compilation, const TimingControl* ctrl) {
    return *compilation.emplace<InvalidTimingControl>(ctrl);
}

void InvalidTimingControl::serializeTo(ASTSerializer& serializer) const {
    if (child)
        serializer.write("child", *child);
}

TimingControl& DelayControl::fromSyntax(Compilation& compilation, const DelaySyntax& syntax,
                                        const ASTContext& context) {
    auto& expr = Expression::bind(*syntax.delayValue, context);
    auto result = compilation.emplace<DelayControl>(expr, syntax.sourceRange());
    if (expr.bad())
        return badCtrl(compilation, result);

    if (!expr.type->isNumeric()) {
        context.addDiag(diag::DelayNotNumeric, expr.sourceRange) << *expr.type;
        return badCtrl(compilation, result);
    }

    return *result;
}

TimingControl& DelayControl::fromParams(Compilation& compilation,
                                        const ParameterValueAssignmentSyntax& exprs,
                                        const ASTContext& context) {
    auto& items = exprs.parameters;
    if (items.size() != 1 || items[0]->kind != SyntaxKind::OrderedParamAssignment) {
        context.addDiag(diag::ExpectedNetDelay, exprs.sourceRange());
        return badCtrl(compilation, nullptr);
    }

    auto& expr = Expression::bind(*items[0]->as<OrderedParamAssignmentSyntax>().expr, context);
    auto result = compilation.emplace<DelayControl>(expr, expr.sourceRange);
    if (expr.bad())
        return badCtrl(compilation, result);

    if (!expr.type->isNumeric()) {
        context.addDiag(diag::DelayNotNumeric, expr.sourceRange) << *expr.type;
        return badCtrl(compilation, result);
    }

    return *result;
}

void DelayControl::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
}

TimingControl& Delay3Control::fromSyntax(Compilation& compilation, const Delay3Syntax& syntax,
                                         const ASTContext& context) {
    auto& expr1 = Expression::bind(*syntax.delay1, context);

    const Expression* expr2 = nullptr;
    if (syntax.delay2)
        expr2 = &Expression::bind(*syntax.delay2, context);

    const Expression* expr3 = nullptr;
    if (syntax.delay3)
        expr3 = &Expression::bind(*syntax.delay3, context);

    auto result = compilation.emplace<Delay3Control>(expr1, expr2, expr3, syntax.sourceRange());
    if (expr1.bad() || (expr2 && expr2->bad()) || (expr3 && expr3->bad()))
        return badCtrl(compilation, result);

    auto checkType = [&](const Expression& expr) {
        if (!expr.type->isNumeric()) {
            context.addDiag(diag::DelayNotNumeric, expr.sourceRange) << *expr.type;
            return false;
        }
        return true;
    };

    if (!checkType(expr1) || (expr2 && !checkType(*expr2)) || (expr3 && !checkType(*expr3)))
        return badCtrl(compilation, result);

    return *result;
}

TimingControl& Delay3Control::fromParams(Compilation& compilation,
                                         const ParameterValueAssignmentSyntax& exprs,
                                         const ASTContext& context) {
    auto& items = exprs.parameters;
    if (items.size() < 1 || items.size() > 3) {
        context.addDiag(diag::ExpectedNetDelay, exprs.sourceRange());
        return badCtrl(compilation, nullptr);
    }

    const Expression* delays[3] = {nullptr};
    for (size_t i = 0; i < items.size(); i++) {
        if (items[i]->kind != SyntaxKind::OrderedParamAssignment) {
            context.addDiag(diag::ExpectedNetDelay, items[i]->sourceRange());
            return badCtrl(compilation, nullptr);
        }

        delays[i] = &Expression::bind(*items[i]->as<OrderedParamAssignmentSyntax>().expr, context);

        if (!delays[i]->type->isNumeric()) {
            context.addDiag(diag::DelayNotNumeric, delays[i]->sourceRange) << *delays[i]->type;
            return badCtrl(compilation, nullptr);
        }
    }

    SLANG_ASSERT(delays[0]);
    return *compilation.emplace<Delay3Control>(*delays[0], delays[1], delays[2],
                                               items.sourceRange());
}

void Delay3Control::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr1", expr1);
    if (expr2)
        serializer.write("expr2", *expr2);
    if (expr3)
        serializer.write("expr3", *expr3);
}

TimingControl& SignalEventControl::fromSyntax(Compilation& compilation,
                                              const SignalEventExpressionSyntax& syntax,
                                              const ASTContext& context) {
    auto edge = SemanticFacts::getEdgeKind(syntax.edge.kind);
    auto& expr = Expression::bind(*syntax.expr, context,
                                  ASTFlags::EventExpression | ASTFlags::AllowClockingBlock);

    const Expression* iffCond = nullptr;
    if (syntax.iffClause)
        iffCond = &Expression::bind(*syntax.iffClause->expr, context, ASTFlags::EventExpression);

    return fromExpr(compilation, edge, expr, iffCond, context, syntax.sourceRange());
}

TimingControl& SignalEventControl::fromSyntax(Compilation& compilation,
                                              const EventControlSyntax& syntax,
                                              const ASTContext& context) {
    auto& expr = Expression::bind(*syntax.eventName, context,
                                  ASTFlags::EventExpression | ASTFlags::AllowClockingBlock);
    return fromExpr(compilation, EdgeKind::None, expr, nullptr, context, syntax.sourceRange());
}

TimingControl& SignalEventControl::fromSyntax(Compilation& compilation,
                                              const BinaryPropertyExprSyntax& syntax,
                                              const ASTContext& context) {
    // We can hit this case for 'iff' binary property expressions that are actually
    // just a signal event with an 'iff' clause.
    SLANG_ASSERT(syntax.kind == SyntaxKind::IffPropertyExpr);

    auto left = context.requireSimpleExpr(*syntax.left, diag::InvalidSyntaxInEventExpr);
    auto right = context.requireSimpleExpr(*syntax.right, diag::InvalidSyntaxInEventExpr);
    if (!left || !right)
        return badCtrl(compilation, nullptr);

    auto& expr = Expression::bind(*left, context,
                                  ASTFlags::EventExpression | ASTFlags::AllowClockingBlock);

    auto& iffCond = Expression::bind(*right, context, ASTFlags::EventExpression);

    return fromExpr(compilation, EdgeKind::None, expr, &iffCond, context, syntax.sourceRange());
}

TimingControl& SignalEventControl::fromSyntax(Compilation& compilation,
                                              const SimpleSequenceExprSyntax& syntax,
                                              const ASTContext& context) {
    if (syntax.repetition) {
        context.addDiag(diag::InvalidSyntaxInEventExpr, syntax.sourceRange());
        return badCtrl(compilation, nullptr);
    }

    auto& expr = Expression::bind(*syntax.expr, context,
                                  ASTFlags::EventExpression | ASTFlags::AllowClockingBlock);

    return fromExpr(compilation, EdgeKind::None, expr, nullptr, context, syntax.sourceRange());
}

TimingControl& SignalEventControl::fromExpr(Compilation& compilation, EdgeKind edge,
                                            const Expression& expr, const Expression* iffCondition,
                                            const ASTContext& context, SourceRange sourceRange) {
    auto result = compilation.emplace<SignalEventControl>(edge, expr, iffCondition, sourceRange);
    if (expr.bad())
        return badCtrl(compilation, result);

    // Note: `expr` here can be a void-typed ArbitrarySymbolExpression if it's
    // referring to a clocking block.
    auto symRef = expr.getSymbolReference();
    const bool isClocking = (symRef && symRef->kind == SymbolKind::ClockingBlock) ||
                            expr.kind == ExpressionKind::ClockingEvent;

    if (edge == EdgeKind::None) {
        if (expr.type->isAggregate() || expr.type->isPropertyType() ||
            (expr.type->isVoid() && !isClocking)) {
            context.addDiag(diag::InvalidEventExpression, expr.sourceRange) << *expr.type;
            return badCtrl(compilation, result);
        }
    }
    else if (!expr.type->isIntegral()) {
        if (isClocking)
            context.addDiag(diag::ClockingBlockEventEdge, expr.sourceRange);
        else
            context.addDiag(diag::ExprMustBeIntegral, expr.sourceRange) << *expr.type;
        return badCtrl(compilation, result);
    }
    else if (expr.type->getBitWidth() > 1) {
        context.addDiag(diag::MultiBitEdge, expr.sourceRange) << *expr.type;
    }

    if (iffCondition) {
        if (!context.requireBooleanConvertible(*iffCondition))
            return badCtrl(compilation, result);
    }

    // Warn if the expression is constant, since it'll never change to trigger off.
    if (context.tryEval(expr))
        context.addDiag(diag::EventExpressionConstant, expr.sourceRange);

    return *result;
}

void SignalEventControl::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
    serializer.write("edge", toString(edge));

    if (iffCondition)
        serializer.write("iff", *iffCondition);
}

static void collectEvents(const ASTContext& context, const SyntaxNode& expr,
                          SmallVectorBase<TimingControl*>& results) {
    switch (expr.kind) {
        case SyntaxKind::ParenthesizedEventExpression:
            collectEvents(context, *expr.as<ParenthesizedEventExpressionSyntax>().expr, results);
            break;
        case SyntaxKind::BinaryEventExpression: {
            auto& bin = expr.as<BinaryEventExpressionSyntax>();
            collectEvents(context, *bin.left, results);
            collectEvents(context, *bin.right, results);
            break;
        }
        case SyntaxKind::OrPropertyExpr: {
            auto& bin = expr.as<BinaryPropertyExprSyntax>();
            collectEvents(context, *bin.left, results);
            collectEvents(context, *bin.right, results);
            break;
        }
        case SyntaxKind::OrSequenceExpr: {
            auto& bin = expr.as<BinarySequenceExprSyntax>();
            collectEvents(context, *bin.left, results);
            collectEvents(context, *bin.right, results);
            break;
        }
        case SyntaxKind::SimplePropertyExpr:
        case SyntaxKind::IffPropertyExpr:
            results.push_back(&TimingControl::bind(expr.as<PropertyExprSyntax>(), context));
            break;
        case SyntaxKind::SimpleSequenceExpr:
        case SyntaxKind::SignalEventExpression:
            results.push_back(&TimingControl::bind(expr.as<SequenceExprSyntax>(), context));
            break;
        case SyntaxKind::ParenthesizedPropertyExpr: {
            auto& ppe = expr.as<ParenthesizedPropertyExprSyntax>();
            collectEvents(context, *ppe.expr, results);
            if (ppe.matchList) {
                for (auto item : ppe.matchList->items)
                    collectEvents(context, *item, results);
            }
            break;
        }
        case SyntaxKind::ParenthesizedSequenceExpr: {
            auto& pse = expr.as<ParenthesizedSequenceExprSyntax>();
            if (pse.repetition) {
                context.addDiag(diag::InvalidSyntaxInEventExpr, expr.sourceRange());
                results.push_back(context.getCompilation().emplace<InvalidTimingControl>(nullptr));
            }
            else {
                collectEvents(context, *pse.expr, results);
                if (pse.matchList) {
                    for (auto item : pse.matchList->items)
                        collectEvents(context, *item, results);
                }
            }
            break;
        }
        default:
            SLANG_UNREACHABLE;
    }
}

TimingControl& EventListControl::fromSyntax(Compilation& compilation, const SyntaxNode& syntax,
                                            const ASTContext& context) {
    SmallVector<TimingControl*> events;
    collectEvents(context, syntax, events);

    if (events.size() == 1)
        return *events[0];

    auto result = compilation.emplace<EventListControl>(events.ccopy(compilation),
                                                        syntax.sourceRange());
    for (auto ev : events) {
        if (ev->bad())
            return badCtrl(compilation, result);
    }

    return *result;
}

void EventListControl::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("events");
    for (auto const event : events) {
        serializer.serialize(*event);
    }
    serializer.endArray();
}

TimingControl& ImplicitEventControl::fromSyntax(Compilation& compilation,
                                                const ImplicitEventControlSyntax& syntax,
                                                const ASTContext&) {
    // Nothing to do here except return the object.
    return *compilation.emplace<ImplicitEventControl>(syntax.sourceRange());
}

TimingControl& RepeatedEventControl::fromSyntax(Compilation& compilation,
                                                const RepeatedEventControlSyntax& syntax,
                                                const ASTContext& context) {
    if (!syntax.eventControl) {
        context.addDiag(diag::RepeatControlNotEvent, syntax.sourceRange());
        return badCtrl(compilation, nullptr);
    }

    auto& expr = Expression::bind(*syntax.expr, context);
    auto& event = TimingControl::bind(*syntax.eventControl, context);
    auto result = compilation.emplace<RepeatedEventControl>(expr, event, syntax.sourceRange());
    if (expr.bad())
        return badCtrl(compilation, result);

    if (!expr.type->isNumeric()) {
        context.addDiag(diag::RepeatNotNumeric, expr.sourceRange) << *expr.type;
        return badCtrl(compilation, result);
    }

    if (event.kind != TimingControlKind::SignalEvent &&
        event.kind != TimingControlKind::EventList &&
        event.kind != TimingControlKind::ImplicitEvent) {
        context.addDiag(diag::RepeatControlNotEvent, syntax.eventControl->sourceRange());
        return badCtrl(compilation, result);
    }

    return *result;
}

void RepeatedEventControl::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
    serializer.write("event", event);
}

TimingControl& CycleDelayControl::fromSyntax(Compilation& compilation, const DelaySyntax& syntax,
                                             const ASTContext& context) {
    auto& expr = Expression::bind(*syntax.delayValue, context);
    auto result = compilation.emplace<CycleDelayControl>(expr, syntax.sourceRange());

    if (!context.requireIntegral(expr))
        return badCtrl(compilation, result);

    if (!context.flags.has(ASTFlags::LValue) && !context.scope->isUninstantiated() &&
        !compilation.getDefaultClocking(*context.scope)) {
        context.addDiag(diag::NoDefaultClocking, syntax.sourceRange());
    }

    return *result;
}

void CycleDelayControl::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
}

TimingControl& BlockEventListControl::fromSyntax(const BlockEventExpressionSyntax& syntax,
                                                 const ASTContext& context) {
    auto& comp = context.getCompilation();
    SmallVector<Event, 4> events;

    auto addEvent = [&](const PrimaryBlockEventExpressionSyntax& evSyntax) {
        auto& expr = ArbitrarySymbolExpression::fromSyntax(comp, *evSyntax.name, context);
        if (auto symbol = expr.getSymbolReference()) {
            if (symbol->kind != SymbolKind::StatementBlock &&
                symbol->kind != SymbolKind::Subroutine) {
                context.addDiag(diag::InvalidBlockEventTarget, evSyntax.name->sourceRange());
                return false;
            }

            events.push_back({&expr, evSyntax.keyword.kind == TokenKind::BeginKeyword});
            return true;
        }

        return false;
    };

    const BlockEventExpressionSyntax* curr = &syntax;
    while (curr->kind == SyntaxKind::BinaryBlockEventExpression) {
        auto& bin = curr->as<BinaryBlockEventExpressionSyntax>();
        if (!addEvent(bin.left->as<PrimaryBlockEventExpressionSyntax>()))
            return badCtrl(comp, nullptr);

        curr = bin.right;
    }

    if (!addEvent(curr->as<PrimaryBlockEventExpressionSyntax>()))
        return badCtrl(comp, nullptr);

    return *comp.emplace<BlockEventListControl>(events.copy(comp), syntax.sourceRange());
}

void BlockEventListControl::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("events");
    for (auto& event : events) {
        SLANG_ASSERT(event.target);
        serializer.startObject();
        serializer.write("target", *event.target);
        serializer.write("isBegin", event.isBegin);
        serializer.endObject();
    }
    serializer.endArray();
}

} // namespace slang::ast
