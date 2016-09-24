#pragma once

#include <cstdint>
#include <ostream>

#include "BitVector.h"

namespace slang {

class ConstantValue {
public:
    ConstantValue() {}
    explicit ConstantValue(int32_t integer) : sint(integer) {}

    friend ConstantValue operator+(const ConstantValue& lhs, const ConstantValue& rhs);
    friend ConstantValue operator-(const ConstantValue& lhs, const ConstantValue& rhs);
    friend ConstantValue operator*(const ConstantValue& lhs, const ConstantValue& rhs);
    friend ConstantValue operator/(const ConstantValue& lhs, const ConstantValue& rhs);
    friend ConstantValue operator%(const ConstantValue& lhs, const ConstantValue& rhs);

    friend bool operator==(const ConstantValue& lhs, const ConstantValue& rhs);

    template<typename T>
    friend bool operator==(const ConstantValue& lhs, const T& rhs) { return lhs.sint == rhs; }

    template<typename T>
    friend bool operator==(const T& lhs, const ConstantValue& rhs) { return operator==(rhs, lhs); }

    friend std::ostream& operator<<(std::ostream& os, const ConstantValue& rhs) {
        os << rhs.getInt();
        return os;
    }

    int32_t getInt() const { return sint; }

private:
    union {
        LogicVector vector;
        uint64_t uint;
        int64_t sint;
        double real;
    };

    enum class Kind {
        Vector,
        UInt,
        SInt,
        Real
    } kind;
};

}