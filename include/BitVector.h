#pragma once

#include "Buffer.h"

namespace slang {

class Diagnostics;

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
    VectorBuilder(Diagnostics& diagnostics);

    void start(uint32_t size);
    void startUnsized();

    void addBinaryDigit(logic_t digit);
    void addOctalDigit(logic_t digit);
    void addDecimalDigit(logic_t digit);
    void addHexDigit(logic_t digit);

    bool haveError() const { return error; }

    LogicVector toVector() const { return LogicVector(); }

private:
    Diagnostics& diagnostics;
    Buffer<logic_t> digits;
    bool error = false;
};

}