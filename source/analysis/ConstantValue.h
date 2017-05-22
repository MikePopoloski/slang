//------------------------------------------------------------------------------
// ConstantValue.h
// Compile-time constant representation.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include <variant>

#include "numeric/SVInt.h"

namespace slang {

/// Represents a constant (compile-time evaluated) value, of one of a few possible types.
/// By default the value is indeterminate, or "bad". Expressions involving bad
/// values result in bad values, as you might expect.
class ConstantValue {
public:
	ConstantValue() {}
	ConstantValue(std::nullptr_t) {}

	ConstantValue(const SVInt& integer) : value(integer) {}
    ConstantValue(SVInt&& integer) : value(std::move(integer)) {}
    ConstantValue(double real) : value(real) {}

	ConstantValue(const ConstantValue& other) = default;
	ConstantValue(ConstantValue&& other) noexcept = default;
	ConstantValue& operator=(const ConstantValue& other) = default;
	ConstantValue& operator=(ConstantValue&& other) noexcept = default;

	bool bad() const { return value.index() == 0; }
    explicit operator bool() const { return !bad(); }

    const SVInt& integer() const { return std::get<1>(value); }
    double real() const { return std::get<2>(value); }

private:
	std::variant<std::monostate, SVInt, double> value;
};

/// Represents a simple constant range.
struct ConstantRange {
	SVInt left;
	SVInt right;

	SVInt width() {
		auto diff = left - right;
		return (diff.isNegative() ? -diff : diff) + SVInt(1);
	}
};

}
