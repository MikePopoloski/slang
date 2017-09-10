//------------------------------------------------------------------------------
// Time.h
// Contains various time-related utilities and functions.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

namespace slang {

/// Scale unit for a time value.
enum class TimeUnit : uint8_t {
    Seconds,
    Milliseconds,
    Microseconds,
    Nanoseconds,
    Picoseconds,
    Femtoseconds
};

bool suffixToTimeUnit(string_view timeSuffix, TimeUnit& unit);
string_view timeUnitToSuffix(TimeUnit unit);

/// As allowed by SystemVerilog, time scales can be expressed
/// in one of only a few magnitudes.
enum class TimescaleMagnitude : uint8_t {
    One = 1,
    Ten = 10,
    Hundred = 100
};

/// A combination of a unit and magnitude for a timescale value.
struct TimescaleValue {
    TimeUnit unit;
    TimescaleMagnitude magnitude;

    TimescaleValue() = default;
    TimescaleValue(TimeUnit unit, TimescaleMagnitude magnitude) :
        unit(unit), magnitude(magnitude) {}
};

/// A collection of a base time and a precision value that
/// determines the scale of simulation time steps.
struct Timescale {
    TimescaleValue base;
    TimescaleValue precision;

    Timescale() = default;
    Timescale(TimescaleValue base, TimescaleValue precision) :
        base(base), precision(precision) {}
};

}