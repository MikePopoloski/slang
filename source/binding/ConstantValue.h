//------------------------------------------------------------------------------
// ConstantValue.h
// Compile-time constant representation.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "diagnostics/Diagnostics.h"
#include "numeric/SVInt.h"

namespace slang {

class Type;

/// Represents a constant (compile-time evaluated) value, of one of a few possible types.
/// By default the value is indeterminate, or "bad". Expressions involving bad
/// values result in bad values, as you might expect.
///
class ConstantValue {
public:
    ConstantValue() {}
    ConstantValue(nullptr_t) {}

    ConstantValue(const SVInt& integer) : value(integer) {}
    ConstantValue(SVInt&& integer) : value(std::move(integer)) {}
    ConstantValue(double real) : value(real) {}

    ConstantValue(const ConstantValue& other) = default;
    ConstantValue(ConstantValue&& other) noexcept = default;
    ConstantValue& operator=(const ConstantValue& other) = default;
    ConstantValue& operator=(ConstantValue&& other) noexcept = default;

    bool bad() const { return value.index() == 0; }
    explicit operator bool() const { return !bad(); }

    bool isInteger() const { return value.index() == 1; }
    bool isReal() const { return value.index() == 2; }

    const SVInt& integer() const { return std::get<1>(value); }
    double real() const { return std::get<2>(value); }

    /// Tries to interpret the constant value as an integer, with no unknown bits,
    /// and which fits in the given number of bits. If it does, the value is returned.
    /// Otherwise, a diagnostic is issued.
    optional<int> coerceInteger(uint32_t maxBits, Diagnostics* diagnostics = nullptr,
                                SourceLocation location = SourceLocation());

    static const ConstantValue Invalid;

private:
    std::variant<std::monostate, SVInt, double> value;
};

/// Represents a simple constant range, fully inclusive. SystemVerilog allows negative
/// indices, and for the left side to be less, equal, or greater than the right.
///
/// Note that this class makes no attempt to handle overflow of the underlying integer;
/// SystemVerilog places tighter bounds on possible ranges anyway so it shouldn't be an issue.
///
struct ConstantRange {
    int left;
    int right;

    /// Gets the width of the range, regardless of the order in which
    /// the bounds are specified.
    uint32_t width() const {
        int diff = left - right;
        return uint32_t(diff < 0 ? -diff : diff) + 1;
    }

    /// Gets the lower bound of the range, regardless of the order in which
    /// the bounds are specified.
    int lower() const { return std::min(left, right); }

    /// Gets the upper bound of the range, regardless of the order in which
    /// the bounds are specified.
    int upper() const { return std::max(left, right); }

    /// "Little endian" bit order is when the msb is >= the lsb.
    bool isLittleEndian() const { return left >= right; }

    /// Normalizes the range so that it's of the form [msb-lsb, 0] and in little endian bit order.
    ConstantRange normalize() const { return { upper() - lower(), 0 }; }

    bool operator==(const ConstantRange& rhs) const {
        return left == rhs.left && right == rhs.right;
    }

    bool operator!=(const ConstantRange& rhs) const {
        return !(*this == rhs);
    }
};

}
