//------------------------------------------------------------------------------
// Time.cpp
// Contains various time-related utilities and functions.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/numeric/Time.h"

#include "slang/util/StringTable.h"

namespace slang {

const static StringTable<TimeUnit> strToUnit = {
    { "s", TimeUnit::Seconds },       { "ms", TimeUnit::Milliseconds },
    { "us", TimeUnit::Microseconds }, { "ns", TimeUnit::Nanoseconds },
    { "ps", TimeUnit::Picoseconds },  { "fs", TimeUnit::Femtoseconds }
};

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
    THROW_UNREACHABLE;
}

optional<TimescaleValue> TimescaleValue::fromLiteral(double value, TimeUnit unit) {
    if (value == 1)
        return TimescaleValue(unit, TimescaleMagnitude::One);
    if (value == 10)
        return TimescaleValue(unit, TimescaleMagnitude::Ten);
    if (value == 100)
        return TimescaleValue(unit, TimescaleMagnitude::Hundred);

    return std::nullopt;
}

bool TimescaleValue::operator>(const TimescaleValue& rhs) const {
    // Unit enum is specified in reverse order, so check in the opposite direction.
    if (unit < rhs.unit)
        return true;
    if (unit > rhs.unit)
        return false;
    return magnitude > rhs.magnitude;
}

} // namespace slang
