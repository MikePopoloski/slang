//------------------------------------------------------------------------------
//! @file TimingControl.h
//! @brief Timing control creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

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
    x(Delay3)
ENUM(TimingControlKind, CONTROL);
#undef CONTROL
// clang-format on

class BindContext;
class Compilation;
class Expression;
struct TimingControlSyntax;

class TimingControl {
public:
    TimingControlKind kind;

    const TimingControlSyntax* syntax = nullptr;

    bool bad() const { return kind == TimingControlKind::Invalid; }

    static const TimingControl& bind(const TimingControlSyntax& syntax, const BindContext& context);

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
    explicit TimingControl(TimingControlKind kind) : kind(kind) {}

    static TimingControl& badCtrl(Compilation& compilation, const TimingControl* ctrl);
};

class InvalidTimingControl : public TimingControl {
public:
    const TimingControl* child;

    explicit InvalidTimingControl(const TimingControl* child) :
        TimingControl(TimingControlKind::Invalid), child(child) {}

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;
};

struct ArgumentListSyntax;
struct DelaySyntax;

class DelayControl : public TimingControl {
public:
    const Expression& expr;

    explicit DelayControl(const Expression& expr) :
        TimingControl(TimingControlKind::Delay), expr(expr) {}

    static TimingControl& fromSyntax(Compilation& compilation, const DelaySyntax& syntax,
                                     const BindContext& context);

    static TimingControl& fromArguments(Compilation& compilation, const ArgumentListSyntax& exprs,
                                        const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::Delay; }

    void serializeTo(ASTSerializer& serializer) const;
};

struct Delay3Syntax;

class Delay3Control : public TimingControl {
public:
    const Expression& expr1;
    const Expression* expr2;
    const Expression* expr3;

    Delay3Control(const Expression& expr1, const Expression* expr2, const Expression* expr3) :
        TimingControl(TimingControlKind::Delay3), expr1(expr1), expr2(expr2), expr3(expr3) {}

    static TimingControl& fromSyntax(Compilation& compilation, const Delay3Syntax& syntax,
                                     const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::Delay3; }

    void serializeTo(ASTSerializer& serializer) const;
};

struct EventControlSyntax;
struct SignalEventExpressionSyntax;

class SignalEventControl : public TimingControl {
public:
    const Expression& expr;
    const Expression* iffCondition;
    EdgeKind edge;

    SignalEventControl(EdgeKind edge, const Expression& expr, const Expression* iffCondition) :
        TimingControl(TimingControlKind::SignalEvent), expr(expr), iffCondition(iffCondition),
        edge(edge) {}

    static TimingControl& fromSyntax(Compilation& compilation,
                                     const SignalEventExpressionSyntax& syntax,
                                     const BindContext& context);

    static TimingControl& fromSyntax(Compilation& compilation, const EventControlSyntax& syntax,
                                     const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::SignalEvent; }

    void serializeTo(ASTSerializer& serializer) const;

private:
    static TimingControl& fromExpr(Compilation& compilation, EdgeKind edge, const Expression& expr,
                                   const Expression* iffCondition, const BindContext& context);
};

struct EventExpressionSyntax;

class EventListControl : public TimingControl {
public:
    span<const TimingControl* const> events;

    explicit EventListControl(span<const TimingControl* const> events) :
        TimingControl(TimingControlKind::EventList), events(events) {}

    static TimingControl& fromSyntax(Compilation& compilation, const EventExpressionSyntax& syntax,
                                     const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::EventList; }

    void serializeTo(ASTSerializer& serializer) const;
};

struct ImplicitEventControlSyntax;

class ImplicitEventControl : public TimingControl {
public:
    ImplicitEventControl() : TimingControl(TimingControlKind::ImplicitEvent) {}

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

    RepeatedEventControl(const Expression& expr, const TimingControl& event) :
        TimingControl(TimingControlKind::RepeatedEvent), expr(expr), event(event) {}

    static TimingControl& fromSyntax(Compilation& compilation,
                                     const RepeatedEventControlSyntax& syntax,
                                     const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::RepeatedEvent; }

    void serializeTo(ASTSerializer& serializer) const;
};

} // namespace slang
