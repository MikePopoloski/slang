#pragma once

#include "Buffer.h"
#include "SourceLocation.h"

namespace slang {

class BumpAllocator;
class Diagnostics;

enum class LiteralBase : uint8_t {
    Binary,
    Octal,
    Decimal,
    Hex
};

struct logic_t {
    // limited from 0 to 15, plus x or z
    uint8_t value;

    logic_t() : value(0) {}
    logic_t(uint8_t value) : value(value) {}

    bool isUnknown() const {
        return value == x.value || value == z.value;
    }

    static const logic_t x;
    static const logic_t z;
};

/// LogicVector is an arbitrary precision integer type that implements SystemVerilog
/// semantics for its operations. In addition to the actual bits it also tracks
/// 4-state X and Z values.
class LogicVector {
public:
    union {
        ArrayRef<logic_t> digits;
        uint64_t value;
    };
    int bits;
    bool hasValue;

    LogicVector(int bits, ArrayRef<logic_t> digits) :
        digits(digits), bits(bits), hasValue(false)
    {
    }

    LogicVector(int bits, uint64_t value) :
        value(value), bits(bits), hasValue(true)
    {
    }
};

// note that this class mostly expects that you've checked errors
// elsewhere and that input is sanitized
class VectorBuilder {
public:
    VectorBuilder(BumpAllocator& alloc, Diagnostics& diagnostics);

    void start();
    void addBinaryDigit(logic_t digit);
    void addOctalDigit(logic_t digit);
    void addDecimalDigit(logic_t digit);
    void addHexDigit(logic_t digit);
    LogicVector finish(LiteralBase base, uint32_t size, SourceLocation location);

private:
    void commonAddDigit(logic_t digit, int maxValue);

    uint64_t calcBinary() const;
    uint64_t calcOctal() const;
    uint64_t calcHex() const;
    uint64_t calcDecimal(SourceLocation location) const;

    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    Buffer<logic_t> digits;
    bool hasUnknown;
};

}