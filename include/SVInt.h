//------------------------------------------------------------------------------
// SVInt.h
// Arbitrary precision integer support.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <ostream>
#include <string>

#include "ArrayRef.h"
#include "Buffer.h"
#include "MathUtils.h"

namespace slang {

enum class LiteralBase : uint8_t {
    Binary,
    Octal,
    Decimal,
    Hex
};

/// Represents a single 4-state bit. The typical values of 0 and 1 are
/// augmented with X (unknown) and Z (high impedance). Both X and Z are
/// considred "unknown" for most computation purposes.
struct logic_t {
    // limited from 0 to 15, plus x or z
    uint8_t value;

    constexpr logic_t() : value(0) {}
    constexpr logic_t(uint8_t value) : value(value) {}

    bool isUnknown() const { return value == x.value || value == z.value; }

    logic_t operator!() const {
        if (isUnknown())
            return logic_t::x;
        return value == 0;
    }

    logic_t operator&(const logic_t& rhs) const {
        if (value == 0 || rhs.value == 0)
            return 0;
        if (value == 1 && rhs.value == 1)
            return 1;
        return logic_t::x;
    }

    logic_t operator|(const logic_t& rhs) const {
        if (value == 1 || rhs.value == 1)
            return 1;
        if (value == 0 && rhs.value == 0)
            return 0;
        return logic_t::x;
    }

    logic_t operator^(const logic_t& rhs) const {
        if (isUnknown() || rhs.isUnknown())
            return logic_t::x;
        return value ^ rhs.value;
    }

    logic_t operator==(const logic_t& rhs) const {
        if (isUnknown() || rhs.isUnknown())
            return logic_t::x;
        return value == rhs.value;
    }

    logic_t operator~() const { return !(*this); }
    logic_t operator!=(const logic_t& rhs) const { return !((*this) == rhs); }
    logic_t operator&&(const logic_t& rhs) const { return (bool)*this && (bool)rhs; }
    logic_t operator||(const logic_t& rhs) const { return (bool)*this != 0 || (bool)rhs; }

    explicit operator bool() const { return !isUnknown() && value != 0; }

    static const logic_t x;
    static const logic_t z;
};

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

    /// Construct from a single bit that can be unknown.
    SVInt(logic_t bit) :
        bitWidth(1), signFlag(false), unknownFlag(bit.isUnknown())
    {
        if (isSingleWord())
            val = bit.value;
        else
            initSlowCase(bit);
    }

    /// Construct from a given 64-bit value. Uses only the bits necessary to hold the value.
    SVInt(uint64_t value, bool isSigned = false) :
        val(value), bitWidth((uint16_t)clog2(value+1)), signFlag(isSigned), unknownFlag(false)
    {
        if (bitWidth == 0)
            bitWidth = 1;
        clearUnusedBits();
    }

    /// Construct from a 64-bit value that can be given an arbitrarily large number of bits (sign
    /// extended if necessary).
    SVInt(uint16_t bits, uint64_t value, bool isSigned) :
        bitWidth(bits), signFlag(isSigned), unknownFlag(false)
    {
        ASSERT(bitWidth);
        if (isSingleWord())
            val = value;
        else
            initSlowCase(value);
        clearUnusedBits();
    }

    SVInt(uint16_t bits, ArrayRef<logic_t> digits);

    /// Destructor.
    ~SVInt() {
        if (!isSingleWord())
            delete[] pVal;
    }

    /// Copy constructor.
    SVInt(const SVInt& other) :
        bitWidth(other.bitWidth), signFlag(other.signFlag), unknownFlag(other.unknownFlag)
    {
        if (isSingleWord())
            val = other.val;
        else
            initSlowCase(other);
    }

    /// Move constructor.
    SVInt(SVInt&& other) noexcept :
        val(other.val), bitWidth(other.bitWidth),
        signFlag(other.signFlag), unknownFlag(other.unknownFlag)
    {
        // zero-ing out the bitwidth of the other object will cause it to not release memory
        other.bitWidth = 0;
    }

    bool isSigned() const { return signFlag; }
    bool hasUnknown() const { return unknownFlag; }
    uint16_t getBitWidth() const { return bitWidth; }
    bool isNegative() const;

    void setSigned(bool isSigned) { signFlag = isSigned; }
    void setWidth(uint16_t bits);

    size_t hash(size_t seed = Seed) const;
    void writeTo(Buffer<char>& buffer, LiteralBase base) const;
    std::string toString(LiteralBase base) const;

    SVInt pow(const SVInt& rhs) const;
    SVInt xnor(const SVInt& rhs) const;
    SVInt ashr(const SVInt& rhs) const;
    SVInt lshr(const SVInt& rhs) const;

    SVInt signExtend(uint16_t bits) const;

    SVInt partSelect(const SVInt& msb, const SVInt& lsb) const;

    bool fullyEqual(const SVInt& rhs) const;
    bool fullyNotEqual(const SVInt& rhs) const;
    bool wildcardEqual(const SVInt& rhs) const;
    bool wildcardNotEqual(const SVInt& rhs) const;

    logic_t reductionOr() const;
    logic_t reductionAnd() const;
    logic_t reductionXor() const;

    SVInt& operator=(const SVInt& rhs);
    SVInt& operator=(SVInt&& rhs) noexcept;

    SVInt& operator&=(const SVInt& rhs);
    SVInt& operator|=(const SVInt& rhs);
    SVInt& operator^=(const SVInt& rhs);
    SVInt& operator+=(const SVInt& rhs);
    SVInt& operator-=(const SVInt& rhs);
    SVInt& operator*=(const SVInt& rhs);
    SVInt& operator/=(const SVInt& rhs);
    SVInt& operator%(const SVInt& rhs);

    SVInt operator++(int) {
        SVInt sv(*this);
        ++(*this);
        return sv;
    }

    SVInt operator--(int) {
        SVInt sv(*this);
        --(*this);
        return sv;
    }

    SVInt& operator++();
    SVInt& operator--();

    SVInt operator-() const;
    SVInt operator~() const;
    logic_t operator!() const { return *this == 0; }

    SVInt operator+(const SVInt& rhs) const;
    SVInt operator-(const SVInt& rhs) const;
    SVInt operator*(const SVInt& rhs) const;
    SVInt operator/(const SVInt& rhs) const;
    SVInt operator%(const SVInt& rhs) const;
    SVInt operator&(const SVInt& rhs) const;
    SVInt operator|(const SVInt& rhs) const;
    SVInt operator^(const SVInt& rhs) const;

    /// Equality operator; if either value is unknown the result is unknown.
    /// Otherwise, if bit lengths are unequal we extend the smaller one and then compare.
    logic_t operator==(const SVInt& rhs) const {
        if (isSingleWord() && rhs.isSingleWord())
            return val == rhs.val;
        return equalsSlowCase(rhs);
    }

    logic_t operator!=(const SVInt& rhs) const { return !((*this) == rhs); }

    logic_t operator<(const SVInt& rhs) const;
    logic_t operator<=(const SVInt& rhs) const { return (*this < rhs) || (*this == rhs); }
    logic_t operator>(const SVInt& rhs) const { return !(*this <= rhs); }
    logic_t operator>=(const SVInt& rhs) const { return !(*this < rhs); }
    logic_t operator&&(const SVInt& rhs) const { return *this != 0 && rhs != 0; }
    logic_t operator||(const SVInt& rhs) const { return *this != 0 || rhs != 0; }

    logic_t operator[](int index) const;

    explicit operator logic_t() const;

    /// Stream formatting operator. Guesses a nice base to use and writes the string representation
    /// into the stream.
    friend std::ostream& operator<<(std::ostream& os, const SVInt& rhs) {
        // guess the base to use
        LiteralBase base;
        if (rhs.bitWidth < 8)
            base = LiteralBase::Binary;
        else if (!rhs.unknownFlag && (rhs.bitWidth == 32 || rhs.signFlag))
            base = LiteralBase::Decimal;
        else
            base = LiteralBase::Hex;

        os << rhs.toString(base);
        return os;
    }

private:
    // fast internal constructor to just set fields on new values
    SVInt(uint64_t* data, uint16_t bits, bool signFlag, bool unknownFlag) :
        pVal(data), bitWidth(bits), signFlag(signFlag), unknownFlag(unknownFlag)
    {
    }

    // slow cases for various initialization paths
    void initSlowCase(logic_t bit);
    void initSlowCase(uint64_t value);
    void initSlowCase(const SVInt& other);

    // slow cases for various other routines
    logic_t equalsSlowCase(const SVInt& rhs) const;
    uint32_t countLeadingZerosSlowCase() const;

    // word and bit manipulation
    bool isSingleWord() const { return bitWidth <= BITS_PER_WORD && !unknownFlag; }
    uint32_t getNumWords() const { return getNumWords(bitWidth, unknownFlag); }
    uint64_t getWord(int bitIndex) const { return isSingleWord() ? val : pVal[whichWord(bitIndex)]; }
    int whichUnknownWord(int bitIndex) const { return whichWord(bitIndex) + getNumWords(bitWidth, false); }
    uint32_t getActiveBits() const { return bitWidth - countLeadingZeros(); }

    const uint64_t* getRawData() const { return isSingleWord() ? &val : pVal; }

    uint32_t countLeadingZeros() const {
        if (isSingleWord())
            return slang::countLeadingZeros(val) - (BITS_PER_WORD - bitWidth);
        return countLeadingZerosSlowCase();
    }

    // other helpers
    static void signExtendCopy(uint64_t* output,  const uint64_t* input, uint16_t oldBits, uint16_t newBits);
    void setUnknownBit(int index, logic_t bit);
    void clearUnusedBits();

    static constexpr int whichWord(int bitIndex) { return bitIndex / BITS_PER_WORD; }
    static constexpr int whichBit(int bitIndex) { return bitIndex % BITS_PER_WORD; }
    static constexpr uint64_t maskBit(int bitIndex) { return 1ULL << whichBit(bitIndex); }

    static int getNumWords(uint16_t bitWidth, bool unknown) {
        uint32_t value = ((uint64_t)bitWidth + BITS_PER_WORD - 1) / BITS_PER_WORD;
        return unknown ? value * 2 : value;
    }

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

inline logic_t operator||(const SVInt& lhs, logic_t rhs) { return lhs != 0 || rhs; }
inline logic_t operator||(logic_t lhs, const SVInt& rhs) { return lhs || rhs != 0; }
inline logic_t operator&&(const SVInt& lhs, logic_t rhs) { return lhs != 0 && rhs; }
inline logic_t operator&&(logic_t lhs, const SVInt& rhs) { return lhs && rhs != 0; }

inline bool operator||(bool lhs, logic_t rhs) { return lhs || (bool)rhs; }
inline bool operator||(logic_t lhs, bool rhs) { return (bool)lhs || rhs; }
inline bool operator&&(bool lhs, logic_t rhs) { return lhs && (bool)rhs; }
inline bool operator&&(logic_t lhs, bool rhs) { return (bool)lhs && rhs; }

/// Implements logical implication: lhs -> rhs. This is equivalent to (!lhs || rhs).
inline logic_t logicalImplication(const SVInt& lhs, const SVInt& rhs) { return !lhs || rhs; }

/// Implements logical equivalence: lhs <-> rhs. This is equivalent to ((lhs -> rhs) && (rhs -> lhs)).
inline logic_t logicalEquivalence(const SVInt& lhs, const SVInt& rhs) {
    return logicalImplication(lhs, rhs) && logicalImplication(rhs, lhs);
}

}

namespace std {

template<>
struct hash<slang::SVInt> {
    size_t operator()(const slang::SVInt& sv) const {
        return sv.hash();
    }
};

}