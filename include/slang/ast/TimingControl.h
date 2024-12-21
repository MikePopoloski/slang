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

/// The base class for SystemVerilog timing controls (delay, event, etc).
class SLANG_EXPORT TimingControl {
public:
    /// The kind of timing control; indicates the type of derived class.
    TimingControlKind kind;

    /// The syntax used to create the timing control, if any.
    const syntax::SyntaxNode* syntax = nullptr;

    /// The source range of this timing control, if it originated from source code.
    SourceRange sourceRange;

    TimingControl(const TimingControl&) = delete;
    TimingControl& operator=(const TimingControl&) = delete;

    /// Indicates whether the timing control is invalid.
    bool bad() const { return kind == TimingControlKind::Invalid; }

    /// Binds a timing control from the given syntax node.
    static TimingControl& bind(const syntax::TimingControlSyntax& syntax,
                               const ASTContext& context);

    /// Binds a timing control from the given syntax node.
    static TimingControl& bind(const syntax::PropertyExprSyntax& syntax, const ASTContext& context);

    /// Binds a timing control from the given syntax node.
    static TimingControl& bind(const syntax::SequenceExprSyntax& syntax, const ASTContext& context);

    /// @brief Casts this timing control to the given concrete derived type.
    ///
    /// Asserts that the type is appropriate given this timing control's kind.
    template<typename T>
    T& as() {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    /// @brief Casts this timing control to the given concrete derived type.
    ///
    /// Asserts that the type is appropriate given this timing control's kind.
    template<typename T>
    const T& as() const {
        SLANG_ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    /// @brief Tries to cast this timing control to the given concrete derived type.
    ///
    /// If the type is not appropriate given this timing control's kind, returns nullptr.
    template<typename T>
    T* as_if() {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<T*>(this);
    }

    /// @brief Tries to cast this timing control to the given concrete derived type.
    ///
    /// If the type is not appropriate given this timing control's kind, returns nullptr.
    template<typename T>
    const T* as_if() const {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<const T*>(this);
    }

    /// Visits this timing control's concrete derived type via the provided visitor object.
    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

protected:
    TimingControl(TimingControlKind kind, SourceRange sourceRange) :
        kind(kind), sourceRange(sourceRange) {}

    static TimingControl& badCtrl(Compilation& compilation, const TimingControl* ctrl);
};

/// @brief Represents an invalid timing control.
///
/// Usually generated and return as a timing control due
/// to violation of language semantics or type checking.
class SLANG_EXPORT InvalidTimingControl : public TimingControl {
public:
    const TimingControl* child;

    explicit InvalidTimingControl(const TimingControl* child) :
        TimingControl(TimingControlKind::Invalid, SourceRange()), child(child) {}

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::Invalid; }

    void serializeTo(ASTSerializer& serializer) const;
};

/// Represents a delay time control.
class SLANG_EXPORT DelayControl : public TimingControl {
public:
    /// An expression denoting the length of time to delay.
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

/// Represents multiple delays associated with a single gate primitive.
class SLANG_EXPORT Delay3Control : public TimingControl {
public:
    /// The first delay (the rise delay).
    const Expression& expr1;

    /// The second delay (the fall delay).
    const Expression* expr2;

    /// The third delay (the turn-off delay).
    const Expression* expr3;

    Delay3Control(const Expression& expr1, const Expression* expr2, const Expression* expr3,
                  SourceRange sourceRange) :
        TimingControl(TimingControlKind::Delay3, sourceRange), expr1(expr1), expr2(expr2),
        expr3(expr3) {}

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

/// Represents a signal event control.
class SLANG_EXPORT SignalEventControl : public TimingControl {
public:
    /// The expression denoting the event on which to trigger.
    const Expression& expr;

    /// An optional condition controlling triggering.
    const Expression* iffCondition;

    /// An optional edge (posedge, negedge) of the expression to trigger on.
    EdgeKind edge;

    SignalEventControl(EdgeKind edge, const Expression& expr, const Expression* iffCondition,
                       SourceRange sourceRange) :
        TimingControl(TimingControlKind::SignalEvent, sourceRange), expr(expr),
        iffCondition(iffCondition), edge(edge) {}

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

/// Represents a list of timing controls to wait on.
class SLANG_EXPORT EventListControl : public TimingControl {
public:
    /// The list of child timing controls.
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

/// Represents an implicit event control (i.e. the @* construct).
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

/// Represents a `repeat` event control.
class SLANG_EXPORT RepeatedEventControl : public TimingControl {
public:
    /// An expression denoting the number of times to repeat.
    const Expression& expr;

    /// The child timing control.
    const TimingControl& event;

    RepeatedEventControl(const Expression& expr, const TimingControl& event,
                         SourceRange sourceRange) :
        TimingControl(TimingControlKind::RepeatedEvent, sourceRange), expr(expr), event(event) {}

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

/// Represents the built-in `1step` delay.
class SLANG_EXPORT OneStepDelayControl : public TimingControl {
public:
    explicit OneStepDelayControl(SourceRange sourceRange) :
        TimingControl(TimingControlKind::OneStepDelay, sourceRange) {}

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::OneStepDelay; }

    void serializeTo(ASTSerializer&) const {}
};

/// Represents a cycle-based delay control.
class SLANG_EXPORT CycleDelayControl : public TimingControl {
public:
    /// An expression denoting the number of cycles to delay.
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

/// Represents a list of block events (used within coverage events).
class SLANG_EXPORT BlockEventListControl : public TimingControl {
public:
    /// A single block event.
    struct Event {
        /// The target block.
        const Expression* target = nullptr;

        /// True if this is a `begin` event and false if it's an `end` event.
        bool isBegin = false;
    };

    /// The list of block events.
    std::span<const Event> events;

    BlockEventListControl(std::span<const Event> events, SourceRange sourceRange) :
        TimingControl(TimingControlKind::BlockEventList, sourceRange), events(events) {}

    static TimingControl& fromSyntax(const syntax::BlockEventExpressionSyntax& syntax,
                                     const ASTContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::BlockEventList; }

    void serializeTo(ASTSerializer& serializer) const;
};

} // namespace slang::ast
