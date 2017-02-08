//------------------------------------------------------------------------------
// ConstantValue.h
// Compile-time constant representation.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include <variant>

#include "SVInt.h"

namespace slang {

using ConstantValueBase = std::variant<std::monostate, SVInt, double>;

struct ConstantValue : ConstantValueBase {
    ConstantValue() : ConstantValueBase() {}
    ConstantValue(std::nullptr_t) : ConstantValueBase() {}

    ConstantValue(const SVInt& integer) : ConstantValueBase(integer) {}
    ConstantValue(SVInt&& integer) : ConstantValueBase(std::move(integer)) {}
    ConstantValue(double real) : ConstantValueBase(real) {}

    ConstantValue(const ConstantValue& other) : ConstantValueBase(other) {}
    ConstantValue(ConstantValue&& other) noexcept : ConstantValueBase(std::move(other)) {}

    ConstantValue& operator=(const ConstantValue& other) {
        ConstantValueBase::operator=(other);
        return *this;
    }

    ConstantValue& operator=(ConstantValue&& other) noexcept {
        ConstantValueBase::operator=(std::move(other));
        return *this;
    }

    bool bad() const { return index() == 0; }
    explicit operator bool() const { return !bad(); }

    const SVInt& integer() const { return std::get<1>(*this); }
    double real() const { return std::get<2>(*this); }
};

}
