//-----------------------------------------------------------------------------
//! @file SVInt.h
//! @brief Arbitrary precision integer support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//-----------------------------------------------------------------------------
#pragma once

#include <bit>
#include <climits>
#include <concepts>
#include <iosfwd>
#include <optional>

#include "slang/util/SmallVector.h"

namespace slang {

/// A type that can represent the largest possible bit width of a SystemVerilog integer.
using bitwidth_t = uint32_t;

// clang-format off
#define LB(x) \
    x(Binary) \
    x(Octal) \
    x(Decimal) \
    x(Hex)
// clang-format on

/// Specifies the base of an integer (for converting to/from a string)
SLANG_ENUM_SIZED(LiteralBase, uint8_t, LB)
#undef LB

bool literalBaseFromChar(char base, LiteralBase& result);

/// Represents a single 4-state bit. The usual bit values of 0 and 1 are
/// augmented with X (unknown) and Z (high impedance). Both X and Z are
/// considered "unknown" for most computation purposes.
struct SLANG_EXPORT logic_t {
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
    logic_t operator&&(const logic_t& rhs) const { return *this & rhs; }
    logic_t operator||(const logic_t& rhs) const { return *this | rhs; }

    // This works around a bug in catch2:
    // 'static_cast': cannot convert from 'slang::logic_t' to 'const bool &'
#if !defined(UNITTESTS)
    explicit
#endif
    operator bool() const {
        return !isUnknown() && value != 0;
    }

    SLANG_EXPORT friend bool exactlyEqual(logic_t lhs, logic_t rhs) {
        return lhs.value == rhs.value;
    }

    char toChar() const;
    SLANG_EXPORT friend std::ostream& operator<<(std::ostream& os, const logic_t& rhs);

    static constexpr uint8_t X_VALUE = 1 << 7;
    static constexpr uint8_t Z_VALUE = 1 << 6;
    static const logic_t x;
    static const logic_t z;
};

/// POD base class for SVInt that contains all data members. The purpose of this
/// is so that other types can manage the backing memory for SVInts with really
/// large bit widths.
class SLANG_EXPORT SVIntStorage {
public:
    SVIntStorage() : val(0), bitWidth(1), signFlag(false), unknownFlag(false) {}
    SVIntStorage(bitwidth_t bits, bool signFlag, bool unknownFlag) :
        val(0), bitWidth(bits), signFlag(signFlag), unknownFlag(unknownFlag) {}
    SVIntStorage(uint64_t* data, bitwidth_t bits, bool signFlag, bool unknownFlag) :
        pVal(data), bitWidth(bits), signFlag(signFlag), unknownFlag(unknownFlag) {}

    // 64 bits of value data; if bits > 64, we allocate words on the heap to hold
    // the values. If we have unknown values (X or Z) we allocate double the number
    // of data words, with the extra set indicating X or Z for each particular bit.
    union {
        uint64_t val;   // value used when bits <= 64
        uint64_t* pVal; // value used when bits > 64
    };

    bitwidth_t bitWidth; // number of bits in the integer
    bool signFlag;       // whether the number should be treated as signed
    bool unknownFlag;    // whether we have at least one X or Z value in the number
};

///
/// SystemVerilog arbitrary precision integer type.
/// This type is designed to implement all of the operations supported by SystemVerilog
/// expressions involving integer vectors. Each value has an arbitrary (but constant) size in bits,
/// up to a maximum of 2**24-1.
///
/// Additionally, SVInt can represent a 4-state value, where each bit can take on additional
/// states of X and Z.
///
/// Small integer values that fit within 64 bits are kept in a simple native integer. Otherwise,
/// space is allocated on the heap. If there are any unknown bits in the number, an extra set of
/// words are allocated adjacent in memory. The bits in these extra words indicate whether the
/// corresponding bits in the low words are unknown or normal.
///
class SLANG_EXPORT SVInt : SVIntStorage {
public:
    /// Simple default constructor for convenience, results in a 1 bit zero value.
    SVInt() {}

    /// Construct from a single bit that can be unknown.
    explicit SVInt(logic_t bit) : SVIntStorage(1, false, bit.isUnknown()) {
        if (isSingleWord())
            val = bit.value;
        else
            initSlowCase(bit);
    }

    /// Construct from a given integer value. Uses only the bits necessary to hold the value.
    template<std::integral T>
    SVInt(T value) : SVIntStorage(0, false, false) {
        val = (uint64_t)value;
        if constexpr (std::is_signed_v<T>) {
            signFlag = true;
            if (value < 0)
                bitWidth = bitwidth_t(64 - std::countl_one(val) + 1);
            else
                bitWidth = bitwidth_t(64 - std::countl_zero(val) + 1);
        }
        else if constexpr (std::is_same_v<T, bool>) {
            bitWidth = 1;
        }
        else {
            bitWidth = (bitwidth_t)std::bit_width(std::make_unsigned_t<T>(value));
        }

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
    SVInt(bitwidth_t bits, uint64_t value, bool isSigned) : SVIntStorage(bits, isSigned, false) {
        SLANG_ASSERT(bits > 0 && bits <= MAX_BITS);
        if (isSingleWord())
            val = value;
        else
            initSlowCase(value);
        clearUnusedBits();
    }

    /// Construct from numeric data already in memory as a range of bytes.
    SVInt(bitwidth_t bits, std::span<const byte> bytes, bool isSigned) :
        SVIntStorage(bits, isSigned, false) {
        SLANG_ASSERT(bits > 0 && bits <= MAX_BITS);
        initSlowCase(bytes);
    }

    ~SVInt() {
        if (!isSingleWord())
            delete[] pVal;
    }

    /// Copy construct.
    SVInt(const SVInt& other) : SVInt(static_cast<const SVIntStorage&>(other)) {}
    SVInt(const SVIntStorage& other) :
        SVIntStorage(other.bitWidth, other.signFlag, other.unknownFlag) {
        if (isSingleWord())
            val = other.val;
        else
            initSlowCase(other);
    }

    /// Move construct.
    SVInt(SVInt&& other) noexcept :
        SVIntStorage(other.bitWidth, other.signFlag, other.unknownFlag) {
        if (isSingleWord())
            val = other.val;
        else
            pVal = std::exchange(other.pVal, nullptr);
    }

    bool isSigned() const { return signFlag; }
    bool hasUnknown() const { return unknownFlag; }
    bitwidth_t getBitWidth() const { return bitWidth; }

    /// Check if the integer can fit into a single 64-bit word.
    bool isSingleWord() const { return bitWidth <= BITS_PER_WORD && !unknownFlag; }

    /// Gets the number of words required to hold the integer, including the unknown bits.
    uint32_t getNumWords() const { return getNumWords(bitWidth, unknownFlag); }

    /// Gets a pointer to the underlying numeric data.
    const uint64_t* getRawPtr() const { return isSingleWord() ? &val : pVal; }

    /// Checks whether it's possible to convert the value to a simple built-in
    /// integer type and if so returns it.
    template<std::integral T>
    std::optional<T> as() const {
        bitwidth_t bits = getMinRepresentedBits();
        if (unknownFlag || bits > sizeof(T) * CHAR_BIT)
            return std::nullopt;

        uint64_t word = getRawData()[0];
        if (signFlag && isNegative()) {
            // If we're a negative value, make sure the top "unused" bits
            // have ones in them, so that when we cast to an int it correctly
            // appears to be negative.
            uint32_t wordBits = bits % BITS_PER_WORD;
            if (wordBits > 0)
                word |= ~uint64_t(0ULL) << wordBits;
        }

        return static_cast<T>(word);
    }

    /// Convert the integer to a double precision floating point value, rounding
    /// where necessary. Any unknown bits are converted to zero during conversion.
    double toDouble() const;

    /// Convert the integer to a single precision floating point value, rounding
    /// where necessary. Any unknown bits are converted to zero during conversion.
    float toFloat() const;

    /// Check whether the number is negative. Note that this doesn't care about
    /// the sign flag; it simply looks at the highest bit to determine whether it is set.
    bool isNegative() const { return (bool)(*this)[int32_t(bitWidth) - 1]; }

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

    /// Removes all unknown bits from the number, converting them to zeros.
    void flattenUnknowns();

    /// Resize the number to be the minimum number of bits without changing
    /// the stored value. Note that this modifies the value in place.
    void shrinkToFit();

    // Create an integer of the given bit width filled with X's or Z's.
    static SVInt createFillX(bitwidth_t bitWidth, bool isSigned);
    static SVInt createFillZ(bitwidth_t bitWidth, bool isSigned);

    [[nodiscard]] size_t hash() const;
    void writeTo(SmallVectorBase<char>& buffer, LiteralBase base,
                 bitwidth_t abbreviateThresholdBits = DefaultStringAbbreviationThresholdBits) const;
    void writeTo(SmallVectorBase<char>& buffer, LiteralBase base, bool includeBase,
                 bitwidth_t abbreviateThresholdBits = MAX_BITS) const;
    std::string toString(
        bitwidth_t abbreviateThresholdBits = DefaultStringAbbreviationThresholdBits,
        bool exactUnknowns = false) const;
    std::string toString(LiteralBase base, bitwidth_t abbreviateThresholdBits =
                                               DefaultStringAbbreviationThresholdBits) const;
    std::string toString(LiteralBase base, bool includeBase,
                         bitwidth_t abbreviateThresholdBits = MAX_BITS) const;

    /// Power function. Note that the result will have the same bitwidth
    /// as this object. The value will be modulo the bit width.
    [[nodiscard]] SVInt pow(const SVInt& rhs) const;

    /// Left shifting.
    [[nodiscard]] SVInt shl(const SVInt& rhs) const;
    [[nodiscard]] SVInt shl(bitwidth_t amount) const;

    /// Arithmetic right shifting.
    [[nodiscard]] SVInt ashr(const SVInt& rhs) const;
    [[nodiscard]] SVInt ashr(bitwidth_t amount) const;

    /// Logical right shifting.
    [[nodiscard]] SVInt lshr(const SVInt& rhs) const;
    [[nodiscard]] SVInt lshr(bitwidth_t amount) const;

    /// Multiple concatenation/replication
    [[nodiscard]] SVInt replicate(const SVInt& times) const;

    /// Reduces all of the bits in the integer to one by applying OR, AND, or XOR.
    [[nodiscard]] logic_t reductionOr() const;
    [[nodiscard]] logic_t reductionAnd() const;
    [[nodiscard]] logic_t reductionXor() const;

    /// Get the number of "active bits". An SVInt might have a large bit width but be set
    /// to a very small value, in which case it will have a low number of active bits.
    bitwidth_t getActiveBits() const { return bitWidth - countLeadingZeros(); }

    /// Get the minimum number of bits required to hold this value, taking into account
    /// the sign flag and whether or not the value would be considered positive.
    /// Note that this ignores unknown bits.
    bitwidth_t getMinRepresentedBits() const {
        if (!signFlag)
            return getActiveBits();
        else if (isNegative())
            return bitWidth - countLeadingOnes() + 1;
        else
            return getActiveBits() + 1;
    }

    /// Count the number of leading zeros. This doesn't do anything special for
    /// unknown values, so make sure you know what you're doing with it.
    bitwidth_t countLeadingZeros() const {
        if (isSingleWord())
            return bitwidth_t(std::countl_zero(val)) - (BITS_PER_WORD - bitWidth);
        return countLeadingZerosSlowCase();
    }

    /// Count the number of leading ones. This doesn't do anything special for
    /// unknown values, so make sure you know what you're doing with it.
    bitwidth_t countLeadingOnes() const {
        if (isSingleWord())
            return bitwidth_t(std::countl_one(val << (BITS_PER_WORD - bitWidth)));
        return countLeadingOnesSlowCase();
    }

    /// Count the number of leading unknown bits.
    bitwidth_t countLeadingUnknowns() const;

    /// Count the number of leading Z bits.
    bitwidth_t countLeadingZs() const;

    /// Count the number of 1 bits in the number.
    bitwidth_t countOnes() const;

    /// Count the number of 0 bits in the number.
    bitwidth_t countZeros() const;

    /// Count the number of X bits in the number.
    bitwidth_t countXs() const;

    /// Count the number of Z bits in the number.
    bitwidth_t countZs() const;

    /// Return a subset of the integer's bit range as a new integer.
    [[nodiscard]] SVInt slice(int32_t msb, int32_t lsb) const;

    /// Replace a range of bits in the number with the given bit pattern.
    void set(int32_t msb, int32_t lsb, const SVInt& value);

    /// Perform sign extension to the given number of bits.
    [[nodiscard]] SVInt sext(bitwidth_t bits) const;

    /// Returns true if all bits in [bitWidth-1:msb] are exactly equal.
    bool isSignExtendedFrom(bitwidth_t msb) const;

    /// If bit msb is nonzero, duplicate it to all bits in [bitWidth-1:msb].
    void signExtendFrom(bitwidth_t msb);

    /// Perform zero extension to the given number of bits.
    [[nodiscard]] SVInt zext(bitwidth_t bits) const;

    /// Extend the number to the given number of bits, performing sign extension
    /// if `isSigned` is true.
    [[nodiscard]] SVInt extend(bitwidth_t bits, bool isSigned) const;

    /// Truncate the number to the given number of bits.
    [[nodiscard]] SVInt trunc(bitwidth_t bits) const;

    /// Resize the number to the given number of bits, truncating if smaller,
    /// making a copy if the same size, zero extending if larger and unsigned,
    /// and sign extending if larger and signed.
    [[nodiscard]] SVInt resize(bitwidth_t bits) const;

    /// Reverses the bit ordering of the number.
    [[nodiscard]] SVInt reverse() const;

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
        rhs.pVal = nullptr;
        return *this;
    }

    /// Bitwise xnor.
    [[nodiscard]] SVInt xnor(const SVInt& rhs) const;

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
    logic_t operator!() const { return !reductionOr(); }

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
    logic_t operator&&(const SVInt& rhs) const { return reductionOr() && rhs.reductionOr(); }
    logic_t operator||(const SVInt& rhs) const { return reductionOr() || rhs.reductionOr(); }

    logic_t operator[](const SVInt& index) const;
    logic_t operator[](int32_t index) const;

    explicit operator logic_t() const { return reductionOr(); }

    /// Constructs from a string (in SystemVerilog syntax). This is mostly for convenience;
    /// any errors will assert instead of being handled gracefully.
    static SVInt fromString(std::string_view str);

    /// Construct from an array of digits.
    static SVInt fromDigits(bitwidth_t bits, LiteralBase base, bool isSigned, bool anyUnknown,
                            std::span<logic_t const> digits);

    /// Construct from a floating point value.
    static SVInt fromDouble(bitwidth_t bits, double value, bool isSigned, bool round = true);
    static SVInt fromFloat(bitwidth_t bits, float value, bool isSigned, bool round = true);

    /// Evaluates a conditional expression; i.e. condition ? left : right
    static SVInt conditional(const SVInt& condition, const SVInt& lhs, const SVInt& rhs);

    /// Implements logical implication: lhs -> rhs. This is equivalent to (!lhs || rhs).
    static logic_t logicalImpl(const SVInt& lhs, const SVInt& rhs);

    /// Implements logical equivalence: lhs <-> rhs.
    /// This is equivalent to ((lhs -> rhs) && (rhs -> lhs)).
    static logic_t logicalEquiv(const SVInt& lhs, const SVInt& rhs);

    /// Concatenates one or more integers into one output integer.
    static SVInt concat(std::span<SVInt const> operands);

    /// Stream formatting operator. Guesses a nice base to use and writes the string representation
    /// into the stream.
    SLANG_EXPORT friend std::ostream& operator<<(std::ostream& os, const SVInt& rhs);

    /// Stricter equality, taking into account unknown bits.
    SLANG_EXPORT friend bool exactlyEqual(const SVInt& lhs, const SVInt& rhs);

    /// Wildcard based equality, with unknown bits as wildcards.
    /// This method only looks for wildcard bits on the rhs, as needed by the conditional operator.
    SLANG_EXPORT friend logic_t condWildcardEqual(const SVInt& lhs, const SVInt& rhs);

    /// Wildcard based equality, with unknown bits as wildcards.
    /// This method implements matching as required by casex statements.
    SLANG_EXPORT friend bool caseXWildcardEqual(const SVInt& lhs, const SVInt& rhs);

    /// Wildcard based equality, with Z bits as wildcards.
    /// This method implements matching as required by casez statements.
    SLANG_EXPORT friend bool caseZWildcardEqual(const SVInt& lhs, const SVInt& rhs);

    enum {
        BITS_PER_WORD = sizeof(uint64_t) * CHAR_BIT,
        WORD_SIZE = sizeof(uint64_t),
        BITWIDTH_BITS = 24,
        MAX_BITS = (1 << BITWIDTH_BITS) - 1
    };

    static const SVInt Zero;
    static const SVInt One;

    /// The default threshold, in bits, to use for abbreviating toString results
    /// when calling one of the simple toString() methods without passing a user
    /// provided threshold.
    static constexpr bitwidth_t DefaultStringAbbreviationThresholdBits = 128;

private:
    // fast internal constructors to just set fields on new values
    SVInt(uint64_t* data, bitwidth_t bits, bool signFlag, bool unknownFlag) :
        SVIntStorage(data, bits, signFlag, unknownFlag) {}

    static SVInt allocUninitialized(bitwidth_t bits, bool signFlag, bool unknownFlag);
    static SVInt allocZeroed(bitwidth_t bits, bool signFlag, bool unknownFlag);

    // Initialization routines for various cases.
    void initSlowCase(logic_t bit);
    void initSlowCase(uint64_t value);
    void initSlowCase(std::span<const byte> bytes);
    void initSlowCase(const SVIntStorage& other);

    uint64_t* getRawData() { return isSingleWord() ? &val : pVal; }
    const uint64_t* getRawData() const { return isSingleWord() ? &val : pVal; }

    // Slow cases for assignment, equality checking, and counting leading zeros.
    SVInt& assignSlowCase(const SVInt& other);
    logic_t equalsSlowCase(const SVInt& rhs) const;
    bitwidth_t countLeadingZerosSlowCase() const;
    bitwidth_t countLeadingOnesSlowCase() const;

    // Get the number of bits that are useful in the top word
    void getTopWordMask(bitwidth_t& bitsInMsw, uint64_t& mask) const;

    // Clear out any unused bits in the topmost word if our bit width
    // is not an even multiple of the word size.
    void clearUnusedBits();

    // Check if we still need to have the unknownFlag set after doing an
    // operation that might have removed the unknown bits in the number.
    void checkUnknown();
    void makeUnknown();

    // $unsigned(*this) value saturated at bitwidth_t::max()
    bitwidth_t unsignedAmount() const;

    static constexpr uint32_t whichWord(bitwidth_t bitIndex) { return bitIndex / BITS_PER_WORD; }
    static constexpr uint32_t whichBit(bitwidth_t bitIndex) { return bitIndex % BITS_PER_WORD; }
    static constexpr uint64_t maskBit(bitwidth_t bitIndex) { return 1ULL << whichBit(bitIndex); }

    static SVInt fromDecimalDigits(bitwidth_t bits, bool isSigned, std::span<logic_t const> digits);

    static SVInt fromPow2Digits(bitwidth_t bits, bool isSigned, bool anyUnknown, uint32_t radix,
                                uint32_t shift, std::span<logic_t const> digits);

    // Split an integer's data into 32-bit words.
    static void splitWords(const SVInt& value, uint32_t* dest, uint32_t numWords);

    // Build the output result of a divide (used for both quotients and remainders).
    static void buildDivideResult(SVInt* result, uint32_t* value, bitwidth_t bitWidth,
                                  bool signFlag, uint32_t numWords);

    // Entry point for Knuth divide that handles corner cases and splitting the integers into 32-bit
    // words.
    static void divide(const SVInt& lhs, uint32_t lhsWords, const SVInt& rhs, uint32_t rhsWords,
                       SVInt* quotient, SVInt* remainder);

    // Unsigned division algorithm.
    static SVInt udiv(const SVInt& lhs, const SVInt& rhs, bool bothSigned);

    // Unsigned remainder algorithm.
    static SVInt urem(const SVInt& lhs, const SVInt& rhs, bool bothSigned);

    // Unsigned modular exponentiation algorithm.
    static SVInt modPow(const SVInt& base, const SVInt& exponent, bool bothSigned);

    static constexpr uint32_t getNumWords(bitwidth_t bitWidth, bool unknown) {
        uint32_t value = (bitWidth + BITS_PER_WORD - 1) / BITS_PER_WORD;
        return unknown ? value * 2 : value;
    }
};

inline logic_t operator||(const SVInt& lhs, logic_t rhs) {
    return lhs != 0 || rhs;
}
inline logic_t operator||(logic_t lhs, const SVInt& rhs) {
    return lhs || rhs != 0;
}
inline logic_t operator&&(const SVInt& lhs, logic_t rhs) {
    return lhs != 0 && rhs;
}
inline logic_t operator&&(logic_t lhs, const SVInt& rhs) {
    return lhs && rhs != 0;
}

inline bool operator||(bool lhs, logic_t rhs) {
    return lhs || (bool)rhs;
}
inline bool operator||(logic_t lhs, bool rhs) {
    return (bool)lhs || rhs;
}
inline bool operator&&(bool lhs, logic_t rhs) {
    return lhs && (bool)rhs;
}
inline bool operator&&(logic_t lhs, bool rhs) {
    return (bool)lhs && rhs;
}

/// Implements logical implication: lhs -> rhs. This is equivalent to (!lhs || rhs).
inline logic_t SVInt::logicalImpl(const SVInt& lhs, const SVInt& rhs) {
    return !lhs || rhs;
}

/// Implements logical equivalence: lhs <-> rhs. This is equivalent to ((lhs -> rhs) && (rhs ->
/// lhs)).
inline logic_t SVInt::logicalEquiv(const SVInt& lhs, const SVInt& rhs) {
    return logicalImpl(lhs, rhs) && logicalImpl(rhs, lhs);
}

/// Returns the ceiling of the log_2 of the value. If value is zero, returns zero.
inline SLANG_EXPORT uint32_t clog2(const SVInt& v) {
    if (v == 0)
        return 0;
    return v.getBitWidth() - (v - SVInt::One).countLeadingZeros();
}

inline namespace literals {

inline SVInt operator""_si(const char* str, size_t size) {
    return SVInt::fromString(std::string_view(str, size));
}

} // namespace literals

} // namespace slang

namespace std {

template<>
struct hash<slang::SVInt> {
    size_t operator()(const slang::SVInt& sv) const { return sv.hash(); }
};

template<>
struct equal_to<slang::SVInt> {
    bool operator()(const slang::SVInt& lhs, const slang::SVInt& rhs) const {
        return exactlyEqual(lhs, rhs);
    }
};

} // namespace std
