//------------------------------------------------------------------------------
//! @file TimingControl.h
//! @brief Timing control creation and analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Expression.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Util.h"

namespace slang::ast {

class ASTContext;
class ASTSerializer;
enum class EdgeKind : int;

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
SLANG_ENUM(TimingControlKind, CONTROL)
#undef CONTROL
// clang-format on

class SLANG_EXPORT TimingControl {
public:
    TimingControlKind kind;

    const syntax::SyntaxNode* syntax = nullptr;

    SourceRange sourceRange;

    TimingControl(const TimingControl&) = delete;
    TimingControl& operator=(const TimingControl&) = delete;

    bool bad() const { return kind == TimingControlKind::Invalid; }

    static TimingControl& bind(const syntax::TimingControlSyntax& syntax,
                               const ASTContext& context);
    static TimingControl& bind(const syntax::PropertyExprSyntax& syntax, const ASTContext& context);
    static TimingControl& bind(const syntax::SequenceExprSyntax& syntax, const ASTContext& context);

    template<typename T>
    T& as() {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    template<typename T>
    const T& as() const {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    template<typename T>
    T* as_if() {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<T*>(this);
    }

    template<typename T>
    const T* as_if() const {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<const T*>(this);
    }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

protected:
    TimingControl(TimingControlKind kind, SourceRange sourceRange) :
        kind(kind), sourceRange(sourceRange) {}

    static TimingControl& badCtrl(Compilation& compilation, const TimingControl* ctrl);
};

class SLANG_EXPORT InvalidTimingControl : public TimingControl {
public:
    const TimingControl* child;

    explicit InvalidTimingControl(const TimingControl* child) :
        TimingControl(TimingControlKind::Invalid, SourceRange()), child(child) {}

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;
};

class SLANG_EXPORT DelayControl : public TimingControl {
public:
    const Expression& expr;

    DelayControl(const Expression& expr, SourceRange sourceRange) :
        TimingControl(TimingControlKind::Delay, sourceRange), expr(expr) {}

    static TimingControl& fromSyntax(Compilation& compilation, const syntax::DelaySyntax& syntax,
                                     const ASTContext& context);

    static TimingControl& fromParams(Compilation& compilation,
                                     const syntax::ParameterValueAssignmentSyntax& exprs,
                                     const ASTContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::Delay; }

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return expr.visit(visitor);
    }
};

class SLANG_EXPORT Delay3Control : public TimingControl {
public:
    const Expression& expr1;
    const Expression* expr2;
    const Expression* expr3;

    Delay3Control(const Expression& expr1, const Expression* expr2, const Expression* expr3,
                  SourceRange sourceRange) :
        TimingControl(TimingControlKind::Delay3, sourceRange),
        expr1(expr1), expr2(expr2), expr3(expr3) {}

    static TimingControl& fromSyntax(Compilation& compilation, const syntax::Delay3Syntax& syntax,
                                     const ASTContext& context);

    static TimingControl& fromParams(Compilation& compilation,
                                     const syntax::ParameterValueAssignmentSyntax& exprs,
                                     const ASTContext& context);

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

class SLANG_EXPORT SignalEventControl : public TimingControl {
public:
    const Expression& expr;
    const Expression* iffCondition;
    EdgeKind edge;

    SignalEventControl(EdgeKind edge, const Expression& expr, const Expression* iffCondition,
                       SourceRange sourceRange) :
        TimingControl(TimingControlKind::SignalEvent, sourceRange),
        expr(expr), iffCondition(iffCondition), edge(edge) {}

    static TimingControl& fromSyntax(Compilation& compilation,
                                     const syntax::SignalEventExpressionSyntax& syntax,
                                     const ASTContext& context);

    static TimingControl& fromSyntax(Compilation& compilation,
                                     const syntax::EventControlSyntax& syntax,
                                     const ASTContext& context);

    static TimingControl& fromSyntax(Compilation& compilation,
                                     const syntax::BinaryPropertyExprSyntax& syntax,
                                     const ASTContext& context);

    static TimingControl& fromSyntax(Compilation& compilation,
                                     const syntax::SimpleSequenceExprSyntax& syntax,
                                     const ASTContext& context);

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
                                   const Expression* iffCondition, const ASTContext& context,
                                   SourceRange sourceRange);
};

class SLANG_EXPORT EventListControl : public TimingControl {
public:
    std::span<const TimingControl* const> events;

    EventListControl(std::span<const TimingControl* const> events, SourceRange sourceRange) :
        TimingControl(TimingControlKind::EventList, sourceRange), events(events) {}

    static TimingControl& fromSyntax(Compilation& compilation, const syntax::SyntaxNode& syntax,
                                     const ASTContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::EventList; }

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        for (auto ev : events)
            ev->visit(visitor);
    }
};

class SLANG_EXPORT ImplicitEventControl : public TimingControl {
public:
    explicit ImplicitEventControl(SourceRange sourceRange) :
        TimingControl(TimingControlKind::ImplicitEvent, sourceRange) {}

    static TimingControl& fromSyntax(Compilation& compilation,
                                     const syntax::ImplicitEventControlSyntax& syntax,
                                     const ASTContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::ImplicitEvent; }

    void serializeTo(ASTSerializer&) const {}
};

class SLANG_EXPORT RepeatedEventControl : public TimingControl {
public:
    const Expression& expr;
    const TimingControl& event;

    RepeatedEventControl(const Expression& expr, const TimingControl& event,
                         SourceRange sourceRange) :
        TimingControl(TimingControlKind::RepeatedEvent, sourceRange),
        expr(expr), event(event) {}

    static TimingControl& fromSyntax(Compilation& compilation,
                                     const syntax::RepeatedEventControlSyntax& syntax,
                                     const ASTContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::RepeatedEvent; }

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        expr.visit(visitor);
        event.visit(visitor);
    }
};

class SLANG_EXPORT OneStepDelayControl : public TimingControl {
public:
    explicit OneStepDelayControl(SourceRange sourceRange) :
        TimingControl(TimingControlKind::OneStepDelay, sourceRange) {}

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::OneStepDelay; }

    void serializeTo(ASTSerializer&) const {}
};

class SLANG_EXPORT CycleDelayControl : public TimingControl {
public:
    const Expression& expr;

    CycleDelayControl(const Expression& expr, SourceRange sourceRange) :
        TimingControl(TimingControlKind::CycleDelay, sourceRange), expr(expr) {}

    static TimingControl& fromSyntax(Compilation& compilation, const syntax::DelaySyntax& syntax,
                                     const ASTContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::CycleDelay; }

    void serializeTo(ASTSerializer& serializer) const;

    template<typename TVisitor>
    decltype(auto) visitExprs(TVisitor&& visitor) const {
        return expr.visit(visitor);
    }
};

class SLANG_EXPORT BlockEventListControl : public TimingControl {
public:
    struct Event {
        const Symbol* target = nullptr;
        bool isBegin = false;
    };

    std::span<const Event> events;

    BlockEventListControl(std::span<const Event> events, SourceRange sourceRange) :
        TimingControl(TimingControlKind::BlockEventList, sourceRange), events(events) {}

    static TimingControl& fromSyntax(const syntax::BlockEventExpressionSyntax& syntax,
                                     const ASTContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::BlockEventList; }

    void serializeTo(ASTSerializer& serializer) const;
};

} // namespace slang::ast
