//------------------------------------------------------------------------------
//! @file Time.h
//! @brief Contains various time-related utilities and functions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/text/SourceLocation.h"
#include "slang/util/Util.h"

namespace slang {

// clang-format off
#define TU(x) \
    x(Seconds) \
    x(Milliseconds) \
    x(Microseconds) \
    x(Nanoseconds) \
    x(Picoseconds) \
    x(Femtoseconds)
/// Scale unit for a time value.
ENUM_SIZED(TimeUnit, uint8_t, TU)
#undef TU
// clang-format on

bool suffixToTimeUnit(string_view timeSuffix, TimeUnit& unit);
string_view timeUnitToSuffix(TimeUnit unit);

/// As allowed by SystemVerilog, time scales can be expressed
/// in one of only a few magnitudes.
enum class TimeScaleMagnitude : uint8_t { One = 1, Ten = 10, Hundred = 100 };

/// A combination of a unit and magnitude for a time scale value.
struct TimeScaleValue {
    TimeUnit unit = TimeUnit::Seconds;
    TimeScaleMagnitude magnitude = TimeScaleMagnitude::One;

    TimeScaleValue() = default;
    TimeScaleValue(TimeUnit unit, TimeScaleMagnitude magnitude) :
        unit(unit), magnitude(magnitude) {}
    TimeScaleValue(string_view str);

    template<size_t N>
    TimeScaleValue(const char (&str)[N]) : TimeScaleValue(string_view(str)) {}

    std::string toString() const;

    static optional<TimeScaleValue> fromLiteral(double value, TimeUnit unit);

    bool operator>(const TimeScaleValue& rhs) const;
    bool operator==(const TimeScaleValue& rhs) const;
    bool operator!=(const TimeScaleValue& rhs) const { return !(*this == rhs); }

    friend std::ostream& operator<<(std::ostream& os, const TimeScaleValue& tv);
};

/// A collection of a base time and a precision value that
/// determines the scale of simulation time steps.
struct TimeScale {
    TimeScaleValue base;
    TimeScaleValue precision;

    TimeScale() = default;
    TimeScale(TimeScaleValue base, TimeScaleValue precision) : base(base), precision(precision) {}

    double apply(double value, TimeUnit unit) const;

    std::string toString() const;

    bool operator==(const TimeScale& rhs) const;
    bool operator!=(const TimeScale& rhs) const { return !(*this == rhs); }

    friend std::ostream& operator<<(std::ostream& os, const TimeScale& ts);
};

} // namespace slang
