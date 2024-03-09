//------------------------------------------------------------------------------
// Time.cpp
// Contains various time-related utilities and functions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/numeric/Time.h"

#include <cmath>
#include <fmt/core.h>
#include <ostream>

#include "slang/util/String.h"

namespace slang {

std::optional<TimeUnit> suffixToTimeUnit(std::string_view timeSuffix, size_t& lengthConsumed) {
    if (timeSuffix.empty())
        return {};

    auto checkRet = [&](TimeUnit unit) -> std::optional<TimeUnit> {
        if (timeSuffix.length() < 2 || timeSuffix[1] != 's')
            return std::nullopt;

        lengthConsumed = 2;
        return unit;
    };

    switch (timeSuffix[0]) {
        case 's':
            lengthConsumed = 1;
            return TimeUnit::Seconds;
        case 'm':
            return checkRet(TimeUnit::Milliseconds);
        case 'u':
            return checkRet(TimeUnit::Microseconds);
        case 'n':
            return checkRet(TimeUnit::Nanoseconds);
        case 'p':
            return checkRet(TimeUnit::Picoseconds);
        case 'f':
            return checkRet(TimeUnit::Femtoseconds);
        default:
            return {};
    }
}

std::string_view timeUnitToSuffix(TimeUnit unit) {
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
    SLANG_UNREACHABLE;
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

static std::optional<TimeScaleValue> parseValue(std::string_view str, size_t& lengthConsumed) {
    size_t idx;
    auto i = strToInt(str, &idx);
    if (!i)
        return {};

    while (idx < str.size() && str[idx] == ' ')
        idx++;

    if (idx >= str.size())
        return {};

    size_t unitConsumed;
    auto unit = suffixToTimeUnit(str.substr(idx), unitConsumed);
    if (!unit)
        return {};

    lengthConsumed = idx + unitConsumed;
    return TimeScaleValue::fromLiteral(double(*i), *unit);
}

std::optional<TimeScaleValue> TimeScaleValue::fromString(std::string_view str) {
    size_t lengthConsumed;
    auto result = parseValue(str, lengthConsumed);
    if (!result || lengthConsumed != str.size())
        return {};

    return result;
}

std::string TimeScaleValue::toString() const {
    std::string result = std::to_string(int(magnitude));
    result.append(timeUnitToSuffix(unit));
    return result;
}

std::strong_ordering TimeScaleValue::operator<=>(const TimeScaleValue& rhs) const {
    // Unit enum is specified in reverse order, so check in the opposite direction.
    if (auto cmp = rhs.unit <=> unit; cmp != 0) // NOLINT
        return cmp;
    return magnitude <=> rhs.magnitude;
}

std::ostream& operator<<(std::ostream& os, const TimeScaleValue& tv) {
    return os << tv.toString();
}

std::optional<TimeScale> TimeScale::fromString(std::string_view str) {
    size_t idx;
    auto base = parseValue(str, idx);
    if (!base)
        return {};

    while (idx < str.size() && str[idx] == ' ')
        idx++;

    if (idx >= str.size() || str[idx] != '/')
        return {};

    do {
        idx++;
    } while (idx < str.size() && str[idx] == ' ');

    if (idx >= str.size())
        return {};

    str = str.substr(idx);
    auto precision = parseValue(str, idx);
    if (!precision || idx != str.length())
        return {};

    // Precision can't be a larger unit of time than the base.
    if (*precision > *base)
        return {};

    return TimeScale(*base, *precision);
}

double TimeScale::apply(double value, TimeUnit unit, bool roundToPrecision) const {
    // First scale the value by the difference between our base and the provided unit.
    // TimeUnits are from 0-5, so we need 11 entries.
    static constexpr double scales[] = {1e15, 1e12, 1e9,  1e6,   1e3,  1e0,
                                        1e-3, 1e-6, 1e-9, 1e-12, 1e-15};
    int diff = int(unit) - int(base.unit);
    double scale = scales[diff + int(TimeUnit::Femtoseconds)] / int(base.magnitude);
    value *= scale;

    if (roundToPrecision) {
        // Round the result to the number of decimals implied by the magnitude
        // difference between our base and our precision.
        diff = int(base.unit) - int(precision.unit);
        scale = scales[diff + int(TimeUnit::Femtoseconds)] * int(base.magnitude);
        scale /= int(precision.magnitude);
        value = std::round(value * scale) / scale;
    }

    return value;
}

std::string TimeScale::toString() const {
    return fmt::format("{} / {}", base.toString(), precision.toString());
}

std::ostream& operator<<(std::ostream& os, const TimeScale& ts) {
    return os << ts.toString();
}

} // namespace slang
