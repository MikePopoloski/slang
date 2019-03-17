//------------------------------------------------------------------------------
// TimingControl.h
// Timing control creation and analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang {

// clang-format off
#define CONTROL(x) \
    x(Invalid) \
    x(Delay)
ENUM(TimingControlKind, CONTROL);
#undef CONTROL
// clang-format on

class BindContext;
class Compilation;
class Expression;
struct DelaySyntax;
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
};

class DelayControl : public TimingControl {
public:
    const Expression& expr;

    explicit DelayControl(const Expression& expr) : TimingControl(TimingControlKind::Delay), expr(expr) {}

    static TimingControl& fromSyntax(Compilation& compilation, const DelaySyntax& syntax,
                                     const BindContext& context);

    static bool isKind(TimingControlKind kind) { return kind == TimingControlKind::Delay; }
};

} // namespace slang