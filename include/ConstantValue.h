#pragma once

namespace slang {

class ConstantValue {
public:
    ConstantValue() {}
    explicit ConstantValue(int32_t integer) : sint(integer) {}

    friend bool operator==(const ConstantValue& lhs, const ConstantValue& rhs);

    template<typename T>
    friend bool operator==(const ConstantValue& lhs, const T& rhs) { return lhs.sint == rhs; }

    template<typename T>
    friend bool operator==(const T& lhs, const ConstantValue& rhs) { return operator==(rhs, lhs); }

    int32_t getInt() { return sint; }

private:
    union {
        LogicVector vector;
        uint64_t uint;
        int64_t sint;
        double real;
    };
};

}