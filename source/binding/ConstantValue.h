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

/// Represents a constant (compile-time evaluated) value, of one of a few possible types.
/// By default the value is indeterminate, or "bad". Expressions involving bad
/// values result in bad values, as you might expect.
///
class ConstantValue {
public:
    /// This type represents the null value (class handles, etc) in expressions.
    struct NullPlaceholder : std::monostate {};

    ConstantValue() = default;
    ConstantValue(nullptr_t) {}

    ConstantValue(const SVInt& integer) : value(integer) {}
    ConstantValue(SVInt&& integer) : value(std::move(integer)) {}
    ConstantValue(double real) : value(real) {}
    ConstantValue(NullPlaceholder nul) : value(nul) {}

    ConstantValue(const ConstantValue& other) = default;
    ConstantValue(ConstantValue&& other) noexcept = default;
    ConstantValue& operator=(const ConstantValue& other) = default;
    ConstantValue& operator=(ConstantValue&& other) noexcept = default;

    bool bad() const { return std::holds_alternative<std::monostate>(value); }
    explicit operator bool() const { return !bad(); }

    bool isInteger() const { return std::holds_alternative<SVInt>(value); }
    bool isReal() const { return std::holds_alternative<double>(value); }
    bool isNullHandle() const { return std::holds_alternative<NullPlaceholder>(value); }

    SVInt& integer() & { return std::get<SVInt>(value); }
    const SVInt& integer() const & { return std::get<SVInt>(value); }
    SVInt integer() && { return std::get<SVInt>(std::move(value)); }
    SVInt integer() const && { return std::get<SVInt>(std::move(value)); }

    double real() const { return std::get<double>(value); }

    static const ConstantValue Invalid;

    friend void to_json(json& j, const ConstantValue& cv);

private:
    std::variant<std::monostate, SVInt, double, NullPlaceholder> value;
};

/// Represents a simple constant range, fully inclusive. SystemVerilog allows negative
/// indices, and for the left side to be less, equal, or greater than the right.
///
/// Note that this class makes no attempt to handle overflow of the underlying integer;
/// SystemVerilog places tighter bounds on possible ranges anyway so it shouldn't be an issue.
///
struct ConstantRange {
    int32_t left;
    int32_t right;

    /// Gets the width of the range, regardless of the order in which
    /// the bounds are specified.
    bitwidth_t width() const {
        int32_t diff = left - right;
        return bitwidth_t(diff < 0 ? -diff : diff) + 1;
    }

    /// Gets the lower bound of the range, regardless of the order in which
    /// the bounds are specified.
    int32_t lower() const { return std::min(left, right); }

    /// Gets the upper bound of the range, regardless of the order in which
    /// the bounds are specified.
    int32_t upper() const { return std::max(left, right); }

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
