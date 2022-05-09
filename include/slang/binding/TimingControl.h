//------------------------------------------------------------------------------
//! @file TimingControl.h
//! @brief Timing control creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/util/Util.h"

namespace slang {

// clang-format off
#define CONTROL(x) \
    x(Invalid) \
    x(Delay) \
    x(SignalEvent) \
    x(EventList) \
    x(ImplicitEvent) \
    x(RepeatedEvent) \
    x(Delay3) \
    x(OneStepDelay) \
    x(CycleDelay) \
    x(BlockEventList)
ENUM(TimingControlKind, CONTROL)
#undef CONTROL
// clang-format on

class BindContext;
class Compilation;
struct PropertyExprSyntax;
struct SequenceExprSyntax;
struct TimingControlSyntax;

class TimingControl {
public:
    TimingControlKind kind;

    const SyntaxNode* syntax = nullptr;

    SourceRange sourceRange;

    bool bad() const { return kind == TimingControlKind::Invalid; }

    static TimingControl& bind(const TimingControlSyntax& syntax, const BindContext& context);
    static TimingControl& bind(const PropertyExprSyntax& syntax, const BindContext& context);
    static TimingControl& bind(const SequenceExprSyntax& syntax, const BindContext& context);

    template<typename T>
    T& as() {
        ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    template<typename T>
    const T& as() const {
        ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

protected:
    TimingControl(TimingControlKind kind, SourceRange sourceRange) :
        kind(kind), sourceRange(sourceRange) {}

    static TimingControl& badCtrl(Compilation& compilation, const TimingControl* ctrl);
};

class InvalidTimingControl : public TimingControl {
public:
    const TimingControl* child;

    explicit InvalidTimingControl(const TimingControl* child) :
        TimingControl(TimingControlKind::Invalid, SourceRange()), child(child) {}

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;
};

struct DelaySyntax;
struct ParameterValueAssignmentSyntax;

class DelayControl : public TimingControl {
public:
    const Expression& expr;

    DelayControl(const Expression& expr, SourceRange sourceRange) :
        TimingControl(TimingControlKind::Delay, sourceRange), expr(expr) {}

    static TimingControl& fromSyntax(Compilation& compilation, const DelaySyntax& syntax,
                                     const BindContext& context);

    static TimingControl& fromParams(Compilation& compilation,
                                     const ParameterValueAssignmentSyntax& exprs,
                                     const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::Delay; }

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
    }
};

struct Delay3Syntax;

class Delay3Control : public TimingControl {
public:
    const Expression& expr1;
    const Expression* expr2;
    const Expression* expr3;

    Delay3Control(const Expression& expr1, const Expression* expr2, const Expression* expr3,
                  SourceRange sourceRange) :
        TimingControl(TimingControlKind::Delay3, sourceRange),
        expr1(expr1), expr2(expr2), expr3(expr3) {}

    static TimingControl& fromSyntax(Compilation& compilation, const Delay3Syntax& syntax,
                                     const BindContext& context);

    static TimingControl& fromParams(Compilation& compilation,
                                     const ParameterValueAssignmentSyntax& exprs,
                                     const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::Delay3; }

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr1.visit(visitor);
        if (expr2)
            expr2->visit(visitor);
        if (expr3)
            expr3->visit(visitor);
    }
};

struct BinaryPropertyExprSyntax;
struct EventControlSyntax;
struct SignalEventExpressionSyntax;
struct SimpleSequenceExprSyntax;

class SignalEventControl : public TimingControl {
public:
    const Expression& expr;
    const Expression* iffCondition;
    EdgeKind edge;

    SignalEventControl(EdgeKind edge, const Expression& expr, const Expression* iffCondition,
                       SourceRange sourceRange) :
        TimingControl(TimingControlKind::SignalEvent, sourceRange),
        expr(expr), iffCondition(iffCondition), edge(edge) {}

    static TimingControl& fromSyntax(Compilation& compilation,
                                     const SignalEventExpressionSyntax& syntax,
                                     const BindContext& context);

    static TimingControl& fromSyntax(Compilation& compilation, const EventControlSyntax& syntax,
                                     const BindContext& context);

    static TimingControl& fromSyntax(Compilation& compilation,
                                     const BinaryPropertyExprSyntax& syntax,
                                     const BindContext& context);

    static TimingControl& fromSyntax(Compilation& compilation,
                                     const SimpleSequenceExprSyntax& syntax,
                                     const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::SignalEvent; }

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
        if (iffCondition)
            iffCondition->visit(visitor);
    }

private:
    static TimingControl& fromExpr(Compilation& compilation, EdgeKind edge, const Expression& expr,
                                   const Expression* iffCondition, const BindContext& context,
                                   SourceRange sourceRange);
};

struct EventExpressionSyntax;

class EventListControl : public TimingControl {
public:
    span<const TimingControl* const> events;

    EventListControl(span<const TimingControl* const> events, SourceRange sourceRange) :
        TimingControl(TimingControlKind::EventList, sourceRange), events(events) {}

    static TimingControl& fromSyntax(Compilation& compilation, const SyntaxNode& syntax,
                                     const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::EventList; }

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto ev : events)
            ev->visit(visitor);
    }
};

struct ImplicitEventControlSyntax;

class ImplicitEventControl : public TimingControl {
public:
    explicit ImplicitEventControl(SourceRange sourceRange) :
        TimingControl(TimingControlKind::ImplicitEvent, sourceRange) {}

    static TimingControl& fromSyntax(Compilation& compilation,
                                     const ImplicitEventControlSyntax& syntax,
                                     const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::ImplicitEvent; }

    void serializeTo(ASTSerializer&) const {}
};

struct RepeatedEventControlSyntax;

class RepeatedEventControl : public TimingControl {
public:
    const Expression& expr;
    const TimingControl& event;

    RepeatedEventControl(const Expression& expr, const TimingControl& event,
                         SourceRange sourceRange) :
        TimingControl(TimingControlKind::RepeatedEvent, sourceRange),
        expr(expr), event(event) {}

    static TimingControl& fromSyntax(Compilation& compilation,
                                     const RepeatedEventControlSyntax& syntax,
                                     const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::RepeatedEvent; }

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
        event.visit(visitor);
    }
};

class OneStepDelayControl : public TimingControl {
public:
    explicit OneStepDelayControl(SourceRange sourceRange) :
        TimingControl(TimingControlKind::OneStepDelay, sourceRange) {}

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::OneStepDelay; }

    void serializeTo(ASTSerializer&) const {}
};

class CycleDelayControl : public TimingControl {
public:
    const Expression& expr;

    CycleDelayControl(const Expression& expr, SourceRange sourceRange) :
        TimingControl(TimingControlKind::CycleDelay, sourceRange), expr(expr) {}

    static TimingControl& fromSyntax(Compilation& compilation, const DelaySyntax& syntax,
                                     const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::CycleDelay; }

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
    }
};

struct BlockEventExpressionSyntax;

class BlockEventListControl : public TimingControl {
public:
    struct Event {
        const Symbol* target = nullptr;
        bool isBegin = false;
    };

    span<const Event> events;

    BlockEventListControl(span<const Event> events, SourceRange sourceRange) :
        TimingControl(TimingControlKind::BlockEventList, sourceRange), events(events) {}

    static TimingControl& fromSyntax(const BlockEventExpressionSyntax& syntax,
                                     const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::BlockEventList; }

    void serializeTo(ASTSerializer& serializer) const;
};

} // namespace slang
