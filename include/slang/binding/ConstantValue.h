//------------------------------------------------------------------------------
// ConstantValue.h
// Compile-time constant representation.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <string>

#include "slang/numeric/SVInt.h"

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
    ConstantValue(NullPlaceholder nul) : value(nul) {}

    template<typename T, typename = std::enable_if_t<std::is_floating_point_v<T>>>
    ConstantValue(T real) : value(double(real)) {}

    bool bad() const { return std::holds_alternative<std::monostate>(value); }
    explicit operator bool() const { return !bad(); }

    bool isInteger() const { return std::holds_alternative<SVInt>(value); }
    bool isReal() const { return std::holds_alternative<double>(value); }
    bool isNullHandle() const { return std::holds_alternative<NullPlaceholder>(value); }

    SVInt& integer() & { return std::get<SVInt>(value); }
    const SVInt& integer() const& { return std::get<SVInt>(value); }
    SVInt integer() && { return std::get<SVInt>(std::move(value)); }
    SVInt integer() const&& { return std::get<SVInt>(std::move(value)); }

    double real() const { return std::get<double>(value); }

    std::string toString() const;

    static const ConstantValue Invalid;

    friend void to_json(json& j, const ConstantValue& cv);
    friend std::ostream& operator<<(std::ostream& os, const ConstantValue& cv);

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
    int32_t left = 0;
    int32_t right = 0;

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

    /// Reverses the bit ordering of the range.
    ConstantRange reverse() const { return { right, left }; }

    /// Selects a subrange of this range, correctly handling both forms of
    /// bit endianness. This will assert that the given subrange is not wider.
    ConstantRange subrange(ConstantRange select) const;

    /// Translates the given index to be relative to the range.
    /// For example, if the range is [7:2] and you pass in 3, the result will be 1.
    /// If the range is [2:7] and you pass in 3, the result will be 2.
    int32_t translateIndex(int32_t index) const;

    /// Determines whether the given point is within the range.
    bool containsPoint(int32_t index) const;

    std::string toString() const;

    bool operator==(const ConstantRange& rhs) const {
        return left == rhs.left && right == rhs.right;
    }

    bool operator!=(const ConstantRange& rhs) const { return !(*this == rhs); }
    friend std::ostream& operator<<(std::ostream& os, const ConstantRange& cr);
};

/// An lvalue is anything that can appear on the left hand side of an assignment
/// expression. It represents some storage location in memory that can be read
/// from and written to.
///
class LValue {
public:
    /// A concatenation of lvalues is also an lvalue and can be assigned to.
    using Concat = std::vector<LValue>;

    LValue() = default;
    LValue(nullptr_t) {}
    explicit LValue(Concat&& concat) : value(std::move(concat)) {}
    explicit LValue(ConstantValue& base) : value(&base) {}

    bool bad() const { return std::holds_alternative<std::monostate>(value); }
    explicit operator bool() const { return !bad(); }

    ConstantValue load() const;
    void store(const ConstantValue& value);

    LValue selectRange(ConstantRange range) const;

private:
    LValue(ConstantValue& base, ConstantRange range) : value(CVRange{ &base, range }) {}

    struct CVRange {
        ConstantValue* cv;
        ConstantRange range;
    };

    std::variant<std::monostate, Concat, ConstantValue*, CVRange> value;
};

} // namespace slang
