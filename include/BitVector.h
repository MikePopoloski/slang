#pragma once

namespace slang {

struct logic_t {
    // limited from 0 to 15, plus x or z
    uint8_t value;

    logic_t() : value(0) {}
    logic_t(uint8_t value) : value(value) {}

    enum {
        x = (1 << 7),
        z = (1 << 6)
    };
};

class LogicVector {
public:
};

class VectorBuilder {
public:
    void start(uint32_t size, bool isSigned) {}
    void addDigit(logic_t digit) {}

    LogicVector toVector() const { return LogicVector(); }
};

}