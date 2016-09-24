#include "ConstantValue.h"

namespace slang {

ConstantValue operator+(const ConstantValue& lhs, const ConstantValue& rhs) {
    return ConstantValue(lhs.getInt() + rhs.getInt());
}

ConstantValue operator-(const ConstantValue& lhs, const ConstantValue& rhs) {
    return ConstantValue();
}

ConstantValue operator*(const ConstantValue& lhs, const ConstantValue& rhs) {
    return ConstantValue();
}

ConstantValue operator/(const ConstantValue& lhs, const ConstantValue& rhs) {
    return ConstantValue();
}

ConstantValue operator%(const ConstantValue& lhs, const ConstantValue& rhs) {
    return ConstantValue();
}

}