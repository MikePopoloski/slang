//------------------------------------------------------------------------------
// SVInt.h
// Arbitrary precision integer support.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>
#include <climits>
#include <ostream>
#include <string>

#include "ArrayRef.h"

namespace slang {

struct logic_t;

/// SystemVerilog arbitrary precision integer type.
/// This type is designed to implement all of the operations supported by SystemVerilog
/// expressions involving integer vectors. Each value has an arbitrary (but constant) size in bits,
/// up to a maximum of 64k.
///
/// Additionally, SVInt can represent a 4-state value, where each bit can take on additional
/// states of X and Z.
///
class SVInt {
public:
    /// Simple default constructor for convenience, results in a 1 bit zero value.
    SVInt() :
        val(0), bitWidth(1), signFlag(false), unknownFlag(false)
    {
    }

    SVInt(logic_t digit);

    /// Construct from a given 64-bit value. Uses only the bits necessary to hold the value.
    SVInt(uint64_t value, bool isSigned = false);
    SVInt(uint16_t bits, uint64_t value, bool isSigned = false);
    SVInt(uint16_t bits, ArrayRef<logic_t> digits);
    ~SVInt() {
        if (!isSingleWord())
            delete[] pVal;
    }

    SVInt(const SVInt& other);
    SVInt(SVInt&& other);

    bool isSigned() const { return signFlag; }
    bool hasUnknown() const { return unknownFlag; }
    bool isNegative() const;
    uint16_t getBitWidth() const;
    uint16_t getActiveBits() const;

    void setSigned(bool isSigned);
    void setWidth(uint16_t bits);

    size_t hash(size_t seed = Seed) const;
    std::string toString() const;

    SVInt pow(const SVInt& rhs) const;
    SVInt xnor(const SVInt& rhs) const;
    SVInt ashr(const SVInt& rhs) const;
    SVInt lshr(const SVInt& rhs) const;

    SVInt partSelect(const SVInt& msb, const SVInt& lsb) const;

    bool fullyEqual(const SVInt& rhs) const;
    bool fullyNotEqual(const SVInt& rhs) const;
    bool wildcardEqual(const SVInt& rhs) const;
    bool wildcardNotEqual(const SVInt& rhs) const;
    
    logic_t logicalImplication(const SVInt& rhs) const;
    logic_t logicalEquivalence(const SVInt& rhs) const;

    logic_t reductionOr() const;
    logic_t reductionAnd() const;
    logic_t reductionXor() const;

    SVInt& operator=(const SVInt& rhs);
    SVInt& operator=(SVInt&& rhs);

    SVInt& operator&=(const SVInt& rhs);
    SVInt& operator|=(const SVInt& rhs);
    SVInt& operator^=(const SVInt& rhs);
    SVInt& operator+=(const SVInt& rhs);
    SVInt& operator-=(const SVInt& rhs);
    SVInt& operator*=(const SVInt& rhs);
    SVInt& operator/=(const SVInt& rhs);
    SVInt& operator%(const SVInt& rhs);
    SVInt& operator<<=(const SVInt& rhs);

    SVInt operator++(int);
    SVInt& operator++();
    SVInt operator--(int);
    SVInt& operator--();

    SVInt operator-() const;
    SVInt operator~() const;
    SVInt operator!() const;

    SVInt operator+(const SVInt& rhs) const;
    SVInt operator-(const SVInt& rhs) const;
    SVInt operator*(const SVInt& rhs) const;
    SVInt operator/(const SVInt& rhs) const;
    SVInt operator%(const SVInt& rhs) const;
    SVInt operator&(const SVInt& rhs) const;
    SVInt operator|(const SVInt& rhs) const;
    SVInt operator^(const SVInt& rhs) const;
    SVInt operator<<(const SVInt& rhs) const;

    logic_t operator==(const SVInt& rhs) const;
    logic_t operator!=(const SVInt& rhs) const;
    logic_t operator<(const SVInt& rhs) const;
    logic_t operator<=(const SVInt& rhs) const;
    logic_t operator>(const SVInt& rhs) const;
    logic_t operator>=(const SVInt& rhs) const;
    logic_t operator&&(const SVInt& rhs) const;
    logic_t operator||(const SVInt& rhs) const;

    logic_t operator[](int index) const;

    friend std::ostream& operator<<(std::ostream& os, const SVInt& rhs);

private:
    bool isSingleWord() const { return bitWidth <= BITS_PER_WORD; }

    static constexpr uint64_t Seed = 0x3765936aa9a6c480; // chosen by fair dice roll

    // 64 bits of value data; if bits > 64, we allocate words on the heap to hold
    // the values. If we have unknown values (X or Z) we allocate double the number
    // of data words, with the extra set indicating X or Z for each particular bit.
    union {
        uint64_t val;   // value used when bits <= 64
        uint64_t* pVal; // value used when bits > 64
    };

    // 32-bits of control data
    uint16_t bitWidth;  // number of bits in the integer
    bool signFlag;      // whether the number should be treated as signed
    bool unknownFlag;   // whether we have at least one X or Z value in the number

    enum {
        BITS_PER_WORD = sizeof(uint64_t) * CHAR_BIT,
        WORD_SIZE = sizeof(uint64_t)
    };
};

}

namespace std {

template<>
struct hash<slang::SVInt> {
    size_t operator()(const slang::SVInt& sv) const {
        return sv.hash();
    }
};

}