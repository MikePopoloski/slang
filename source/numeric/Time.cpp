//------------------------------------------------------------------------------
// Time.cpp
// Contains various time-related utilities and functions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/numeric/Time.h"

#include <fmt/core.h>
#include <ostream>

#include "slang/util/String.h"
#include "slang/util/StringTable.h"

namespace slang {

const static StringTable<TimeUnit> strToUnit = {
    {"s", TimeUnit::Seconds},      {"ms", TimeUnit::Milliseconds}, {"us", TimeUnit::Microseconds},
    {"ns", TimeUnit::Nanoseconds}, {"ps", TimeUnit::Picoseconds},  {"fs", TimeUnit::Femtoseconds}};

bool suffixToTimeUnit(string_view timeSuffix, TimeUnit& unit) {
    return strToUnit.lookup(timeSuffix, unit);
}

string_view timeUnitToSuffix(TimeUnit unit) {
    switch (unit) {
        case TimeUnit::Seconds:
            return "s";
        case TimeUnit::Milliseconds:
            return "ms";
        case TimeUnit::Microseconds:
            return "us";
        case TimeUnit::Nanoseconds:
            return "ns";
        case TimeUnit::Picoseconds:
            return "ps";
        case TimeUnit::Femtoseconds:
            return "fs";
    }
    ASSUME_UNREACHABLE;
}

TimeScaleValue::TimeScaleValue(string_view str) {
    size_t idx;
    auto i = strToInt(str, &idx);
    if (!i)
        throw std::invalid_argument("Not a valid timescale magnitude");

    while (idx < str.size() && str[idx] == ' ')
        idx++;

    TimeUnit u;
    if (idx >= str.size() || !suffixToTimeUnit(str.substr(idx), u))
        throw std::invalid_argument("Time value suffix is missing or invalid");

    auto tv = fromLiteral(double(*i), u);
    if (!tv)
        throw std::invalid_argument("Invalid time scale value");

    *this = *tv;
}

std::optional<TimeScaleValue> TimeScaleValue::fromLiteral(double value, TimeUnit unit) {
    if (value == 1)
        return TimeScaleValue(unit, TimeScaleMagnitude::One);
    if (value == 10)
        return TimeScaleValue(unit, TimeScaleMagnitude::Ten);
    if (value == 100)
        return TimeScaleValue(unit, TimeScaleMagnitude::Hundred);

    return std::nullopt;
}

std::string TimeScaleValue::toString() const {
    std::string result = std::to_string(int(magnitude));
    result.append(timeUnitToSuffix(unit));
    return result;
}

bool TimeScaleValue::operator>(const TimeScaleValue& rhs) const {
    // Unit enum is specified in reverse order, so check in the opposite direction.
    if (unit < rhs.unit)
        return true;
    if (unit > rhs.unit)
        return false;
    return magnitude > rhs.magnitude;
}

bool TimeScaleValue::operator==(const TimeScaleValue& rhs) const {
    return unit == rhs.unit && magnitude == rhs.magnitude;
}

std::ostream& operator<<(std::ostream& os, const TimeScaleValue& tv) {
    return os << tv.toString();
}

double TimeScale::apply(double value, TimeUnit unit) const {
    // First scale the value by the difference between our base and the provided unit.
    // TimeUnits are from 0-5, so we need 11 entries.
    static constexpr double scales[] = {1e15, 1e12, 1e9,  1e6,   1e3,  1e0,
                                        1e-3, 1e-6, 1e-9, 1e-12, 1e-15};
    int diff = int(unit) - int(base.unit);
    double scale = scales[diff + int(TimeUnit::Femtoseconds)] / int(base.magnitude);
    value *= scale;

    // Round the result to the number of decimals implied by the magnitude
    // difference between our base and our precision.
    diff = int(base.unit) - int(precision.unit);
    scale = scales[diff + int(TimeUnit::Femtoseconds)] * int(base.magnitude);
    scale /= int(precision.magnitude);
    value = std::round(value * scale) / scale;

    return value;
}

std::string TimeScale::toString() const {
    return fmt::format("{} / {}", base.toString(), precision.toString());
}

bool TimeScale::operator==(const TimeScale& rhs) const {
    return base == rhs.base && precision == rhs.precision;
}

std::ostream& operator<<(std::ostream& os, const TimeScale& ts) {
    return os << ts.toString();
}

} // namespace slang
