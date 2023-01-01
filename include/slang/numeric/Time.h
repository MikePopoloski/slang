//------------------------------------------------------------------------------
//! @file Time.h
//! @brief Contains various time-related utilities and functions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <optional>

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

SLANG_EXPORT std::optional<TimeUnit> suffixToTimeUnit(string_view timeSuffix,
                                                      size_t& lengthConsumed);
SLANG_EXPORT string_view timeUnitToSuffix(TimeUnit unit);

/// As allowed by SystemVerilog, time scales can be expressed
/// in one of only a few magnitudes.
enum class SLANG_EXPORT TimeScaleMagnitude : uint8_t { One = 1, Ten = 10, Hundred = 100 };

/// A combination of a unit and magnitude for a time scale value.
struct SLANG_EXPORT TimeScaleValue {
    TimeUnit unit = TimeUnit::Nanoseconds;
    TimeScaleMagnitude magnitude = TimeScaleMagnitude::One;

    TimeScaleValue() = default;
    TimeScaleValue(TimeUnit unit, TimeScaleMagnitude magnitude) :
        unit(unit), magnitude(magnitude) {}

    std::string toString() const;

    static std::optional<TimeScaleValue> fromLiteral(double value, TimeUnit unit);
    static std::optional<TimeScaleValue> fromString(string_view str);

    bool operator>(const TimeScaleValue& rhs) const;
    bool operator==(const TimeScaleValue& rhs) const;
    bool operator!=(const TimeScaleValue& rhs) const { return !(*this == rhs); }

    SLANG_EXPORT friend std::ostream& operator<<(std::ostream& os, const TimeScaleValue& tv);
};

/// A collection of a base time and a precision value that
/// determines the scale of simulation time steps.
struct SLANG_EXPORT TimeScale {
    TimeScaleValue base;
    TimeScaleValue precision;

    TimeScale() = default;
    TimeScale(TimeScaleValue base, TimeScaleValue precision) : base(base), precision(precision) {}

    double apply(double value, TimeUnit unit) const;

    std::string toString() const;

    static std::optional<TimeScale> fromString(string_view str);

    bool operator==(const TimeScale& rhs) const;
    bool operator!=(const TimeScale& rhs) const { return !(*this == rhs); }

    SLANG_EXPORT friend std::ostream& operator<<(std::ostream& os, const TimeScale& ts);
};

} // namespace slang
