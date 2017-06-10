//------------------------------------------------------------------------------
// SVInt.h
// Arbitrary precision integer support.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <optional>
#include <ostream>
#include <string>

#include "util/ArrayRef.h"
#include "util/SmallVector.h"
#include "util/StringRef.h"

#include "MathUtils.h"

namespace slang {

/// Specifies the base of an integer (for converting to/from a string)
enum class LiteralBase : uint8_t {
    Binary,
    Octal,
    Decimal,
    Hex
};

bool literalBaseFromChar(char base, LiteralBase& result);

/// Represents a single 4-state bit. The usual bit values of 0 and 1 are
/// augmented with X (unknown) and Z (high impedance). Both X and Z are
/// considered "unknown" for most computation purposes.
struct logic_t {
    // limited from 0 to 15, plus x or z
    uint8_t value;

    /// Default construct; zero value
    constexpr logic_t() : value(0) {}

    /// Construct from a single bit value
    constexpr explicit logic_t(uint8_t value) : value(value) {}

    /// Returns true if the bit is either X or Z
    bool isUnknown() const { return value == x.value || value == z.value; }

    logic_t operator!() const {
        if (isUnknown())
            return logic_t::x;
        return logic_t(value == 0);
    }

    logic_t operator&(const logic_t& rhs) const {
        if (value == 0 || rhs.value == 0)
            return logic_t(0);
        if (value == 1 && rhs.value == 1)
            return logic_t(1);
        return logic_t::x;
    }

    logic_t operator|(const logic_t& rhs) const {
        if (value == 1 || rhs.value == 1)
            return logic_t(1);
        if (value == 0 && rhs.value == 0)
            return logic_t(0);
        return logic_t::x;
    }

    logic_t operator^(const logic_t& rhs) const {
        if (isUnknown() || rhs.isUnknown())
            return logic_t::x;
        return logic_t(value ^ rhs.value);
    }

    logic_t operator==(const logic_t& rhs) const {
        if (isUnknown() || rhs.isUnknown())
            return logic_t::x;
        return logic_t(value == rhs.value);
    }

    logic_t operator~() const { return !(*this); }
    logic_t operator!=(const logic_t& rhs) const { return !((*this) == rhs); }
    logic_t operator&&(const logic_t& rhs) const { return logic_t((bool)*this && (bool)rhs); }
    logic_t operator||(const logic_t& rhs) const { return logic_t((bool)*this != 0 || (bool)rhs); }

    explicit operator bool() const { return !isUnknown() && value != 0; }

    friend bool exactlyEqual(logic_t lhs, logic_t rhs) { return lhs.value == rhs.value; }

    friend std::ostream& operator<<(std::ostream& os, const logic_t& rhs) {
        if (rhs.value == x.value)
            os << "x";
        else if (rhs.value == z.value)
            os << "z";
        else
            os << rhs.value;
        return os;
    }

    static constexpr uint8_t X_VALUE = 1 << 7;
    static constexpr uint8_t Z_VALUE = 1 << 6;
    static const logic_t x;
    static const logic_t z;
};

// TODO:
// - Correct behavior when indexing outside the bounds of the value
// - Use a 32-bit value for bitWidth to allow for full sized intermediaries

///
/// SystemVerilog arbitrary precision integer type.
/// This type is designed to implement all of the operations supported by SystemVerilog
/// expressions involving integer vectors. Each value has an arbitrary (but constant) size in bits,
/// up to a maximum of 2**16.
///
/// Additionally, SVInt can represent a 4-state value, where each bit can take on additional
/// states of X and Z.
///
/// Small integer values that fit within 64 bits are kept in a simple native integer. Otherwise,
/// space is allocated on the heap. If there are any unknown bits in the number, an extra set of
/// words are allocated adjacent in memory. The bits in these extra words indicate whether the
/// corresponding bits in the low words are unknown or normal.
///
class SVInt {
public:
    /// Simple default constructor for convenience, results in a 1 bit zero value.
    SVInt() : val(0), bitWidth(1), signFlag(false), unknownFlag(false) {}

    /// Construct from a single bit that can be unknown.
    explicit SVInt(logic_t bit) :
        bitWidth(1), signFlag(false), unknownFlag(bit.isUnknown())
    {
        if (isSingleWord())
            val = bit.value;
        else
            initSlowCase(bit);
    }

    /// Construct from a given signed 64-bit value. Uses only the bits necessary to hold the value.
    explicit SVInt(int64_t value) :
        val(value), signFlag(true), unknownFlag(false)
    {
        if (value < 0)
            bitWidth = uint16_t(64 - slang::countLeadingOnes(value) + 1);
        else
            bitWidth = uint16_t(64 - slang::countLeadingZeros(value) + 1);
        clearUnusedBits();
    }

    /// Construct from a given 64-bit value. Uses only the bits necessary to hold the value.
    explicit SVInt(uint64_t value, bool isSigned) :
        val(value), bitWidth((uint16_t)clog2(value+1)), signFlag(isSigned), unknownFlag(false)
    {
        if (bitWidth == 0) {
            if (value == 0)
                bitWidth = 1;
            else
                bitWidth = 64;
        }
        clearUnusedBits();
    }

    /// Construct from a 64-bit value that can be given an arbitrarily large number of bits (sign
    /// extended if necessary).
    SVInt(uint16_t bits, uint64_t value, bool isSigned) :
        bitWidth(bits), signFlag(isSigned), unknownFlag(false)
    {
        // 0-bit SVInts are valid only as the result of a zero-width concatenation, which is only
        // valid within another concatenation. For nwo we drop this check altogehter, but it
        // might be a good check to have in general
        //ASSERT(bitWidth);
        if (isSingleWord())
            val = value;
        else
            initSlowCase(value);
        clearUnusedBits();
    }

    /// Constructs from a string (in SystemVerilog syntax). This is mostly for convenience;
    /// any errors will assert instead of being handled gracefully.
    explicit SVInt(StringRef str);

    SVInt(uint16_t bits, LiteralBase base, bool isSigned, bool anyUnknown, ArrayRef<logic_t> digits);

    ~SVInt() {
        if (!isSingleWord())
            delete[] pVal;
    }

    SVInt(const SVInt& other) :
        bitWidth(other.bitWidth), signFlag(other.signFlag), unknownFlag(other.unknownFlag)
    {
        if (isSingleWord())
            val = other.val;
        else
            initSlowCase(other);
    }

    SVInt(SVInt&& other) noexcept :
        val(other.val), bitWidth(other.bitWidth),
        signFlag(other.signFlag), unknownFlag(other.unknownFlag)
    {
        // prevent the other object from releasing memory
        other.pVal = 0;
    }

    bool isSigned() const { return signFlag; }
    bool hasUnknown() const { return unknownFlag; }
    uint16_t getBitWidth() const { return bitWidth; }

    /// Assert that the integer value can fit into a single integer and return it.
    uint16_t getAssertUInt16() const;
    uint32_t getAssertUInt32() const;
    uint64_t getAssertUInt64() const;

    int64_t getAssertInt64() const;

	/// Checks whether it's possible to convert the value to a simple built-in
	/// integer type and if so returns it.
	template<typename T>
	std::optional<T> as() const {
		if (unknownFlag || getMinRepresentedBits() > std::numeric_limits<T>::digits)
			return std::nullopt;

        uint64_t word = getRawData()[0];
        if (signFlag && isNegative()) {
            // If we're a negative value, make sure the top "unused" bits
            // have ones in them, so that when we cast to an int it correctly
            // appears to be negative.
            uint32_t wordBits = bitWidth % BITS_PER_WORD;
            if (wordBits > 0)
                word |= ~uint64_t(0ULL) << wordBits;
        }

		return static_cast<T>(word);
	}

    /// Check whether the number is negative. Note that this doesn't care about
    /// the sign flag; it simply looks at the highest bit to determine whether it is set.
    bool isNegative() const { return (bool)(*this)[bitWidth - 1]; }

    /// Check whether a number is odd or even. Ignores the unknown flag.
    bool isOdd() const { return getRawData()[0] & 0x1; }
    bool isEven() const { return !isOdd(); }

    /// Reinterpret the integer as a signed or unsigned value. This doesn't
    /// change the bits, only the representation.
    void setSigned(bool isSigned) { signFlag = isSigned; }

    /// Set all of the bits in the integer to 1, zero, X, or Z.
    void setAllOnes();
    void setAllZeros();
    void setAllX();
    void setAllZ();

    // Create an integer of the given bit width filled with X's.
    static SVInt createFillX(uint16_t bitWidth, bool isSigned);
    static SVInt createFillZ(uint16_t bitWidth, bool isSigned);

    size_t hash(size_t seed = Seed) const;
    void writeTo(SmallVector<char>& buffer, LiteralBase base) const;
    std::string toString(LiteralBase base) const;

    /// Power function. Note that the result will have the same bitwidth
    /// as this object. The value will be modulo the bit width.
    SVInt pow(const SVInt& rhs) const;

    /// Left shifting.
    SVInt shl(const SVInt& rhs) const;
    SVInt shl(uint32_t amount) const;

    /// Arithmetic right shifting.
    SVInt ashr(const SVInt& rhs) const;
    SVInt ashr(uint32_t amount) const;

    /// Logical right shifting.
    SVInt lshr(const SVInt& rhs) const;
    SVInt lshr(uint32_t amount) const;

    /// Bitwise xnor.
    SVInt xnor(const SVInt& rhs) const;

    /// The operation SV applies for 'x ? lhs : rhs
    SVInt ambiguousConditionalCombination(const SVInt& rhs) const;

    /// Multiple concatenation/replication
    SVInt replicate(const SVInt& times) const;

    /// Returns the bit-selected range from lsb to msb, inclusive both ends
    /// indexes based on SVInts having lsb = 0. Must have msb >= lsb.
    SVInt bitSelect(int16_t lsb, int16_t msb) const;

    logic_t reductionOr() const;
    logic_t reductionAnd() const;
    logic_t reductionXor() const;

    /// Get the number of "active bits". An SVInt might have a large bit width but be set
    /// to a very small value, in which case it will have a low number of active bits.
    uint32_t getActiveBits() const { return bitWidth - countLeadingZeros(); }

    /// Get the minimum number of bits required to hold this value, taking into account
    /// the sign flag and whether or not the value would be considered positive.
    uint32_t getMinRepresentedBits() const {
        if (!signFlag)
            return getActiveBits();
        else if (isNegative())
            return bitWidth - countLeadingOnes() + 1;
        else
            return getActiveBits() + 1;
    }

    /// Count the number of leading zeros. This doesn't do anything special for
    /// unknown values, so make sure you know what you're doing with it.
    uint32_t countLeadingZeros() const {
        if (isSingleWord())
            return slang::countLeadingZeros(val) - (BITS_PER_WORD - bitWidth);
        return countLeadingZerosSlowCase();
    }

    /// Count the number of leading ones. This doesn't do anything special for
    /// unknown values, so make sure you know what you're doing with it.
    uint32_t countLeadingOnes() const {
        if (isSingleWord())
            return slang::countLeadingOnes(val << (BITS_PER_WORD - bitWidth));
        return countLeadingOnesSlowCase();
    }

    SVInt& operator=(const SVInt& rhs) {
        if (isSingleWord() && rhs.isSingleWord()) {
            val = rhs.val;
            bitWidth = rhs.bitWidth;
            signFlag = rhs.signFlag;
            unknownFlag = rhs.unknownFlag;
            return *this;
        }
        return assignSlowCase(rhs);
    }

    SVInt& operator=(SVInt&& rhs) noexcept {
        if (this == &rhs)
            return *this;

        if (!isSingleWord())
            delete[] pVal;

        val = rhs.val;
        bitWidth = rhs.bitWidth;
        signFlag = rhs.signFlag;
        unknownFlag = rhs.unknownFlag;

        // prevent the other object from releasing memory
        rhs.pVal = 0;
        return *this;
    }

    SVInt& operator&=(const SVInt& rhs);
    SVInt& operator|=(const SVInt& rhs);
    SVInt& operator^=(const SVInt& rhs);
    SVInt& operator+=(const SVInt& rhs);
    SVInt& operator-=(const SVInt& rhs);
    SVInt& operator*=(const SVInt& rhs);
    SVInt& operator/=(const SVInt& rhs);
    SVInt& operator%=(const SVInt& rhs);

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
            return logic_t(as<uint64_t>() == rhs.as<uint64_t>());
        return equalsSlowCase(rhs);
    }

    logic_t operator!=(const SVInt& rhs) const { return !((*this) == rhs); }

    logic_t operator<(const SVInt& rhs) const;
    logic_t operator<=(const SVInt& rhs) const { return (*this < rhs) || (*this == rhs); }
    logic_t operator>(const SVInt& rhs) const { return !(*this <= rhs); }
    logic_t operator>=(const SVInt& rhs) const { return !(*this < rhs); }
    logic_t operator&&(const SVInt& rhs) const { return *this != 0 && rhs != 0; }
    logic_t operator||(const SVInt& rhs) const { return *this != 0 || rhs != 0; }

    logic_t operator[](uint32_t index) const;
    SVInt operator()(const SVInt& msb, const SVInt& lsb) const;
    SVInt operator()(uint16_t msb, uint16_t lsb) const;

    explicit operator logic_t() const { return *this != 0; }

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

    friend SVInt signExtend(const SVInt& value, uint16_t bits);
    friend SVInt zeroExtend(const SVInt& value, uint16_t bits);
    friend SVInt extend(const SVInt& value, uint16_t bits, bool sign);
    friend bool exactlyEqual(const SVInt& lhs, const SVInt& rhs);
    friend logic_t wildcardEqual(const SVInt& lhs, const SVInt& rhs);

    /// Concatenation operator
    friend SVInt concatenate(ArrayRef<SVInt> operands);

    /// Optimized operators that work with direct integer values.
    friend logic_t operator==(const SVInt& lhs, int64_t rhs) {
        if (lhs.hasUnknown())
            return logic_t::x;
        auto l = lhs.as<int64_t>();
        return l ? logic_t(*l == rhs) : logic_t(false);
    }

    friend logic_t operator==(int64_t lhs, const SVInt& rhs) { return rhs == lhs; }
    friend logic_t operator!=(const SVInt& lhs, int64_t rhs) { return !(lhs == rhs); }
    friend logic_t operator!=(int64_t lhs, const SVInt& rhs) { return !(rhs == lhs); }

    friend logic_t operator<(const SVInt& lhs, int64_t rhs) {
        if (lhs.hasUnknown())
            return logic_t::x;
        auto l = lhs.as<int64_t>();
        return l ? logic_t(*l < rhs) : logic_t(false);
    }

    friend logic_t operator<=(const SVInt& lhs, int64_t rhs) { return (lhs < rhs) || (lhs == rhs); }
    friend logic_t operator>(const SVInt& lhs, int64_t rhs) { return !(lhs <= rhs); }
    friend logic_t operator>=(const SVInt& lhs, int64_t rhs) { return !(lhs < rhs); }

    friend logic_t operator<(int64_t lhs, const SVInt& rhs) { return rhs >= lhs; }
    friend logic_t operator<=(int64_t lhs, const SVInt& rhs) { return rhs > lhs; }
    friend logic_t operator>(int64_t lhs, const SVInt& rhs) { return rhs <= lhs; }
    friend logic_t operator>=(int64_t lhs, const SVInt& rhs) { return rhs < lhs; }

    enum {
        MAX_BITS = UINT16_MAX,
        BITS_PER_WORD = sizeof(uint64_t) * CHAR_BIT,
        WORD_SIZE = sizeof(uint64_t)
    };

	static SVInt Zero;
	static SVInt One;

private:
    // fast internal constructors to just set fields on new values
    SVInt(uint64_t* data, uint16_t bits, bool signFlag, bool unknownFlag) :
        pVal(data), bitWidth(bits), signFlag(signFlag), unknownFlag(unknownFlag)
    {
    }

    // Initialization routines for various cases.
    void initSlowCase(logic_t bit);
    void initSlowCase(uint64_t value);
    void initSlowCase(const SVInt& other);

    // Slow cases for assignment, equality checking, and counting leading zeros.
    SVInt& assignSlowCase(const SVInt& other);
    logic_t equalsSlowCase(const SVInt& rhs) const;
    uint32_t countLeadingZerosSlowCase() const;
    uint32_t countLeadingOnesSlowCase() const;
    uint32_t countPopulation() const;

    // Specialized shift left routine that doesn't remove the unknown flag.
    SVInt shl(uint32_t amount, bool doCheckUnknown) const;

    // Check if we can fit the integer into a single word.
    bool isSingleWord() const { return bitWidth <= BITS_PER_WORD && !unknownFlag; }

    // Get the number of words required to hold the integer, including the unknown bits.
    uint32_t getNumWords() const { return getNumWords(bitWidth, unknownFlag); }

    // Get a specific word holding the given bit index.
    uint64_t getWord(int bitIndex) const { return isSingleWord() ? val : pVal[whichWord(bitIndex)]; }

    // Get a specific unknown control word holding the given bit index.
    int whichUnknownWord(int bitIndex) const { return whichWord(bitIndex) + getNumWords(bitWidth, false); }

    // Get the number of bits that are useful in the top word
    void getTopWordMask(uint32_t& bitsInMsw, uint64_t& mask) const;

    // Get a pointer to the data, either pVal or val depending on whether we have a single word.
    const uint64_t* getRawData() const { return isSingleWord() ? &val : pVal; }

    // Set a specific bit to be a specific 4-state value.
    void setUnknownBit(int index, logic_t bit);

    // Clear out any unused bits in the topmost word if our bit width
    // is not an even multiple of the word size.
    void clearUnusedBits();

    // Check if we still need to have the unknownFlag set after doing an
    // operation that might have removed the unknown bits in the number.
    void checkUnknown();

    static constexpr int whichWord(int bitIndex) { return bitIndex / BITS_PER_WORD; }
    static constexpr int whichBit(int bitIndex) { return bitIndex % BITS_PER_WORD; }
    static constexpr uint64_t maskBit(int bitIndex) { return 1ULL << whichBit(bitIndex); }

    // Split an integer's data into 32-bit words.
    static void splitWords(const SVInt& value, uint32_t* dest, uint32_t numWords);

    // Build the output result of a divide (used for both quotients and remainders).
    static void buildDivideResult(SVInt* result, uint32_t* value, uint16_t bitWidth,
                                  bool signFlag, uint32_t numWords);

    // Entry point for Knuth divide that handles corner cases and splitting the integers into 32-bit words.
    static void divide(const SVInt& lhs, uint32_t lhsWords, const SVInt& rhs, uint32_t rhsWords,
                       SVInt* quotient, SVInt* remainder);

    // Unsigned division algorithm.
    static SVInt udiv(const SVInt& lhs, const SVInt& rhs, bool bothSigned);

    // Unsigned remainder algorithm.
    static SVInt urem(const SVInt& lhs, const SVInt& rhs, bool bothSigned);

    // Unsigned modular exponentiation algorithm.
    static SVInt modPow(const SVInt& base, const SVInt& exponent, bool bothSigned);

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

/// Returns the ceiling of the log_2 of the value. If value is zero, returns zero.
inline uint32_t clog2(const SVInt& v) {
    if (v == 0)
        return 0;
    return v.getBitWidth() - (v - SVInt(1)).countLeadingZeros();
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
