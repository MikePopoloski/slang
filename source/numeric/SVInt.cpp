//------------------------------------------------------------------------------
// SVInt.cpp
// Arbitrary precision integer support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/numeric/SVInt.h"

#include "SVIntHelpers.h"
#include <cmath>
#include <fmt/core.h>
#include <ostream>
#include <stdexcept>

#include "slang/text/CharInfo.h"
#include "slang/util/Hash.h"
#include "slang/util/String.h"

static const double log2_10 = log2(10.0);

namespace slang {

const logic_t logic_t::x{logic_t::X_VALUE};
const logic_t logic_t::z{logic_t::Z_VALUE};

const SVInt SVInt::Zero = 0u;
const SVInt SVInt::One = 1u;

bool literalBaseFromChar(char base, LiteralBase& result) {
    switch (base) {
        case 'd':
        case 'D':
            result = LiteralBase::Decimal;
            return true;
        case 'b':
        case 'B':
            result = LiteralBase::Binary;
            return true;
        case 'o':
        case 'O':
            result = LiteralBase::Octal;
            return true;
        case 'h':
        case 'H':
            result = LiteralBase::Hex;
            return true;
        default:
            return false;
    }
}

char logic_t::toChar() const {
    if (value == logic_t::x.value)
        return 'x';
    if (value == logic_t::z.value)
        return 'z';
    if (value)
        return '1';
    return '0';
}

std::ostream& operator<<(std::ostream& os, const logic_t& rhs) {
    if (rhs.value == logic_t::x.value)
        os << "x";
    else if (rhs.value == logic_t::z.value)
        os << "z";
    else
        os << (uint32_t)rhs.value;
    return os;
}

SVInt SVInt::fromString(std::string_view str) {
    if (str.empty())
        SLANG_THROW(std::invalid_argument("String is empty"));

    const char* c = str.data();
    const char* end = c + str.length();
    bool negative = *c == '-';
    if (*c == '-' || *c == '+') {
        c++; // heh
        if (c == end)
            SLANG_THROW(std::invalid_argument("String only has a sign?"));
    }

    // look for a base specifier (optional)
    // along the way we'll keep track of the current decimal value, so that
    // if we find that it's actually a size we'll already be done
    bool sizeBad = false;
    bool sizeOverflow = false;
    uint32_t possibleSize = 0;
    const char* apostrophe = nullptr;
    for (const char* tmp = c; tmp != end; tmp++) {
        char d = *tmp;
        if (d == '\'') {
            // found it, we're done
            apostrophe = tmp;
            break;
        }
        else if (isDecimalDigit(d)) {
            // If the number gets larger than the maximum allowed bit width
            // then this is either not a size or a bad one.
            possibleSize *= 10;
            possibleSize += getDigitValue(d);
            if (possibleSize > MAX_BITS)
                sizeOverflow = true;
        }
        else if (d != '_') {
            // underscores are allowed as digit separators; anything else means this
            // is not a valid bit width
            sizeBad = true;
        }
    }

    // numbers without a size specifier are assumed to be 32 bits, signed, and in decimal base
    bool isSigned = true;
    bitwidth_t bits = 32;
    LiteralBase base = LiteralBase::Decimal;

    if (apostrophe) {
        if (sizeBad || sizeOverflow || possibleSize == 0)
            SLANG_THROW(std::invalid_argument("Size is invalid (bad chars or overflow 16 bits)"));
        bits = possibleSize;

        c = apostrophe + 1;
        if (c == end)
            SLANG_THROW(std::invalid_argument("Nothing after size specifier"));

        if (*c == 's' || *c == 'S') {
            isSigned = true;
            c++;
            if (c == end)
                SLANG_THROW(std::invalid_argument("Nothing after sign specifier"));
        }
        else {
            isSigned = false;
        }

        if (!literalBaseFromChar(*c, base))
            SLANG_THROW(std::invalid_argument(fmt::format("Unknown base specifier '{}'", *c)));

        c++;
        if (c == end)
            SLANG_THROW(std::invalid_argument("Nothing after base specifier"));
    }
    else if (sizeBad) {
        SLANG_THROW(std::invalid_argument("Not an integer or sized literal"));
    }

    // convert the remaining chars to an array of digits to pass to the other
    // constructor
    bool isUnknown = false;
    SmallVector<logic_t> digits;
    for (; c != end; ++c) {
        char d = *c;
        if (d == '_')
            continue;

        logic_t value;
        switch (d) {
            case 'X':
            case 'x':
                value = logic_t::x;
                isUnknown = true;
                break;
            case 'Z':
            case 'z':
            case '?':
                value = logic_t::z;
                isUnknown = true;
                break;
            default:
                value = logic_t(getHexDigitValue(d));
                break;
        }
        digits.push_back(value);
    }

    SVInt result = fromDigits(bits, base, isSigned, isUnknown, digits);

    // if it's supposed to be negative, flip it around
    if (negative)
        return -result;
    else
        return result;
}

SVInt SVInt::fromDigits(bitwidth_t bits, LiteralBase base, bool isSigned, bool anyUnknown,
                        std::span<logic_t const> digits) {
    if (digits.empty())
        SLANG_THROW(std::invalid_argument("No digits provided"));

    // Note: If the user specified a number too large to fit in the number of bits specified,
    // the spec says to truncate from the left, which this method will successfully do.

    uint32_t radix = 0;
    uint32_t shift = 0;
    switch (base) {
        case LiteralBase::Binary:
            radix = 2;
            shift = 1;
            break;
        case LiteralBase::Octal:
            radix = 8;
            shift = 3;
            break;
        case LiteralBase::Decimal:
            radix = 10;
            shift = 0; // can't actually shift for Decimal numbers
            break;
        case LiteralBase::Hex:
            radix = 16;
            shift = 4;
            break;
    }

    if (bits <= BITS_PER_WORD && !anyUnknown) {
        // Fast path for values that fit in one word:
        // let's do the computation entirely in a normal uint64_t instead
        // of having to do SVInt operations
        uint64_t val = 0;
        for (const logic_t& d : digits) {
            if (shift)
                val <<= shift;
            else
                val *= radix;

            val += d.value;
            if (d.value >= radix) {
                SLANG_THROW(std::invalid_argument(
                    fmt::format("Digit {} too large for radix {}", d.value, radix)));
            }
        }
        return SVInt(bits, val, isSigned);
    }

    if (radix == 10) {
        // In base ten we can't have individual bits be X or Z, it's all or nothing
        if (anyUnknown) {
            if (digits.size() != 1) {
                SLANG_THROW(std::invalid_argument(
                    "If a decimal number is unknown, it must have exactly one digit."));
            }

            if (exactlyEqual(digits[0], logic_t::z))
                return createFillZ(bits, isSigned);
            else
                return createFillX(bits, isSigned);
        }

        return fromDecimalDigits(bits, isSigned, digits);
    }

    return fromPow2Digits(bits, isSigned, anyUnknown, radix, shift, digits);
}

SVInt SVInt::fromDecimalDigits(bitwidth_t bits, bool isSigned, std::span<logic_t const> digits) {
    SVInt result = allocZeroed(bits, isSigned, false);

    constexpr int charsPerWord = 18; // 18 decimal digits can fit in a 64-bit word
    const logic_t* d = digits.data();
    uint64_t maxWord = (uint64_t)std::pow(10, charsPerWord);
    uint32_t count = 0;
    uint64_t word;

    auto nextDigit = [&]() {
        uint8_t v = d->value;
        if (v >= 10) {
            SLANG_THROW(
                std::invalid_argument(fmt::format("Digit {} too large for radix {}", v, 10)));
        }
        d++;
        return v;
    };

    auto writeWord = [&]() {
        if (!count) {
            if (word)
                result.pVal[count++] = word;
        }
        else {
            uint64_t carry = mulOne(result.pVal, result.pVal, count, maxWord);
            carry += addOne(result.pVal, result.pVal, count, word);
            if (carry)
                result.pVal[count++] = carry;
        }
    };

    size_t i;
    for (i = charsPerWord; i < digits.size(); i += charsPerWord) {
        word = nextDigit();
        for (size_t j = charsPerWord - 1; j != 0; j--)
            word = word * 10 + nextDigit();

        writeWord();
    }

    maxWord = 10;
    word = nextDigit();

    for (size_t j = digits.size() - (i - charsPerWord) - 1; j > 0; j--) {
        word = word * 10 + nextDigit();
        maxWord *= 10;
    }

    writeWord();

    return result;
}

SVInt SVInt::fromPow2Digits(bitwidth_t bits, bool isSigned, bool anyUnknown, uint32_t radix,
                            uint32_t shift, std::span<logic_t const> digits) {

    SVInt result = allocZeroed(bits, isSigned, anyUnknown);

    uint32_t numWords = getNumWords(bits, false);
    uint32_t ones = (1 << shift) - 1;
    uint64_t word = 0;
    uint64_t unknownWord = 0;
    uint64_t* dest = result.pVal;
    uint64_t* endPtr = dest + numWords;
    uint32_t bitPos = 0;

    for (ptrdiff_t i = ptrdiff_t(digits.size()) - 1; i >= 0; i--) {
        logic_t d = digits[size_t(i)];
        uint64_t unknown = 0;
        uint64_t value = d.value;

        if (exactlyEqual(d, logic_t::x)) {
            value = 0;
            unknown = ones;
        }
        else if (exactlyEqual(d, logic_t::z)) {
            value = ones;
            unknown = ones;
        }
        else if (value >= radix) {
            SLANG_THROW(std::invalid_argument(
                fmt::format("Digit {} too large for radix {}", value, radix)));
        }

        word |= value << bitPos;
        unknownWord |= unknown << bitPos;
        bitPos += shift;

        if (bitPos >= BITS_PER_WORD) {
            *dest = word;
            if (anyUnknown)
                *(dest + numWords) = unknownWord;

            dest++;
            if (dest == endPtr)
                break;

            bitPos -= BITS_PER_WORD;
            word = value >> (shift - bitPos);
            unknownWord = unknown >> (shift - bitPos);
        }
    }

    if (dest != endPtr) {
        if (word)
            *dest = word;
        if (anyUnknown && unknownWord)
            *(dest + numWords) = unknownWord;
    }

    result.clearUnusedBits();
    result.checkUnknown();

    if (result.hasUnknown()) {
        // If the most significant bit is X or Z, we need to extend that out to the full range.
        uint32_t givenBits = std::min((uint32_t)digits.size() * shift, result.getBitWidth());
        uint32_t wordBits = givenBits % BITS_PER_WORD;
        uint32_t wordOffset = givenBits / BITS_PER_WORD;
        uint64_t mask = UINT64_MAX;
        if (wordBits)
            mask <<= wordBits;
        else {
            wordBits = 64;
            wordOffset--;
            mask = 0;
        }

        uint32_t topWord = numWords + wordOffset;
        if (result.pVal[topWord] >> (wordBits - 1)) {
            // Unknown bit was set, so now do the extension.
            result.pVal[topWord] |= mask;
            for (topWord++; topWord < numWords * 2; topWord++)
                result.pVal[topWord] = UINT64_MAX;

            if (result.pVal[wordOffset] >> (wordBits - 1)) {
                // The Z bit was set as well, so handle that too.
                result.pVal[wordOffset] |= mask;
                for (wordOffset++; wordOffset < numWords; wordOffset++)
                    result.pVal[wordOffset] = UINT64_MAX;
            }
            result.clearUnusedBits();
        }
    }

    return result;
}

SVInt SVInt::fromDouble(bitwidth_t bits, double value, bool isSigned, bool round) {
    return fromIEEE754<double, 11, 52, 1023>(bits, value, isSigned, round);
}

SVInt SVInt::fromFloat(bitwidth_t bits, float value, bool isSigned, bool round) {
    return fromIEEE754<float, 8, 23, 127>(bits, value, isSigned, round);
}

double SVInt::toDouble() const {
    return toIEEE754<double, 11, 52, 1023>(*this);
}

float SVInt::toFloat() const {
    return toIEEE754<float, 8, 23, 127>(*this);
}

void SVInt::setAllZeros() {
    if (isSingleWord())
        val = 0;
    else if (unknownFlag)
        *this = SVInt(bitWidth, 0, signFlag);
    else
        memset(pVal, 0, getNumWords() * WORD_SIZE);
}

void SVInt::setAllOnes() {
    // we don't have unknown digits anymore, so reallocate if necessary
    if (unknownFlag) {
        unknownFlag = false;
        delete[] pVal;
        if (getNumWords() > 1)
            pVal = new uint64_t[getNumWords()];
    }

    if (isSingleWord())
        val = UINT64_MAX;
    else {
        for (uint32_t i = 0; i < getNumWords(); i++)
            pVal[i] = UINT64_MAX;
    }
    clearUnusedBits();
}

void SVInt::setAllX() {
    // first set low half to zero (for X)
    uint32_t words = getNumWords(bitWidth, false);
    if (unknownFlag)
        memset(pVal, 0, words * WORD_SIZE);
    else {
        if (!isSingleWord())
            delete[] pVal;

        unknownFlag = true;
        pVal = new uint64_t[words * 2]();
    }

    // now set upper half to ones (for unknown)
    for (uint32_t i = words; i < words * 2; i++)
        pVal[i] = UINT64_MAX;
    clearUnusedBits();
}

void SVInt::setAllZ() {
    if (!unknownFlag) {
        if (!isSingleWord())
            delete[] pVal;

        unknownFlag = true;
        pVal = new uint64_t[getNumWords()];
    }

    // everything set to 1 (for Z in the low half and for unknown in the upper half)
    for (uint32_t i = 0; i < getNumWords(); i++)
        pVal[i] = UINT64_MAX;
    clearUnusedBits();
}

void SVInt::flattenUnknowns() {
    if (!unknownFlag)
        return;

    uint32_t words = getNumWords(bitWidth, false);
    for (uint32_t i = 0; i < words; i++) {
        pVal[i] &= ~pVal[i + words];
        pVal[i + words] = 0;
    }

    checkUnknown();
}

void SVInt::shrinkToFit() {
    bitwidth_t minBits = getMinRepresentedBits();
    if (minBits == 0)
        minBits = 1;

    if (minBits != bitWidth)
        *this = resize(minBits);
}

bitwidth_t SVInt::unsignedAmount() const {
    // [11.4.10] The right operand of shift operators is always treated as an unsigned number
    bitwidth_t bits = getActiveBits();
    if (bits > sizeof(bitwidth_t) * CHAR_BIT)
        return std::numeric_limits<bitwidth_t>::max();
    return static_cast<bitwidth_t>(*getRawPtr());
}

SVInt SVInt::shl(const SVInt& rhs) const {
    // if the shift amount is unknown, result is all X's
    if (rhs.hasUnknown())
        return createFillX(bitWidth, signFlag);

    return shl(rhs.unsignedAmount());
}

SVInt SVInt::shl(bitwidth_t amount) const {
    // handle trivial cases
    if (amount == 0)
        return *this;
    if (amount >= bitWidth) // if the shift amount is too large, we end up with zero anyway
        return SVInt(bitWidth, 0, signFlag);
    if (isSingleWord())
        return SVInt(bitWidth, val << amount, signFlag);

    // handle the small shift case
    SVInt result = allocUninitialized(bitWidth, signFlag, unknownFlag);
    if (amount < BITS_PER_WORD && !unknownFlag) {
        uint64_t carry = 0;
        for (uint32_t i = 0; i < getNumWords(); i++) {
            result.pVal[i] = pVal[i] << amount | carry;
            carry = pVal[i] >> (BITS_PER_WORD - amount);
        }
    }
    else {
        // otherwise do a full shift
        uint32_t numWords = getNumWords(bitWidth, false);
        uint32_t wordShift = amount % BITS_PER_WORD;
        uint32_t offset = amount / BITS_PER_WORD;

        // also handle shifting the unknown bits if necessary
        shlFar(result.pVal, pVal, wordShift, offset, 0, numWords);
        if (unknownFlag)
            shlFar(result.pVal, pVal, wordShift, offset, numWords, numWords);
    }

    result.clearUnusedBits();
    result.checkUnknown();
    return result;
}

SVInt SVInt::lshr(const SVInt& rhs) const {
    // if the shift amount is unknown, result is all X's
    if (rhs.hasUnknown())
        return createFillX(bitWidth, signFlag);

    return lshr(rhs.unsignedAmount());
}

SVInt SVInt::lshr(bitwidth_t amount) const {
    // handle trivial cases
    if (amount == 0)
        return *this;
    if (amount >= bitWidth) // if the shift amount is too large, we end up with zero anyway
        return SVInt(bitWidth, 0, signFlag);
    if (isSingleWord())
        return SVInt(bitWidth, val >> amount, signFlag);

    // handle the small shift case
    SVInt result = allocZeroed(bitWidth, signFlag, unknownFlag);
    if (amount < BITS_PER_WORD && !unknownFlag)
        lshrNear(result.pVal, pVal, getNumWords(), amount);
    else {
        // otherwise do a full shift
        uint32_t numWords = getNumWords(bitWidth, false);
        uint32_t wordShift = amount % BITS_PER_WORD;
        uint32_t offset = amount / BITS_PER_WORD;

        // also handle shifting the unknown bits if necessary
        lshrFar(result.pVal, pVal, wordShift, offset, 0, numWords);
        if (unknownFlag)
            lshrFar(result.pVal, pVal, wordShift, offset, numWords, numWords);
    }

    result.checkUnknown();
    return result;
}

SVInt SVInt::ashr(const SVInt& rhs) const {
    if (!signFlag)
        return lshr(rhs);
    if (rhs.hasUnknown())
        return createFillX(bitWidth, signFlag);

    return ashr(rhs.unsignedAmount());
}

SVInt SVInt::ashr(bitwidth_t amount) const {
    if (amount == 0)
        return *this;

    logic_t msb = (*this)[int32_t(bitWidth) - 1];
    if (!signFlag || exactlyEqual(msb, logic_t(false))) // unsigned or nonnegative
        return lshr(amount);

    if (amount >= bitWidth) {
        if (exactlyEqual(msb, logic_t::x))
            return createFillX(bitWidth, signFlag);
        if (exactlyEqual(msb, logic_t::z))
            return createFillZ(bitWidth, signFlag);
        // msb==1 here. If msb==0, call lshr already.
        return SVInt(bitWidth, UINT64_MAX, signFlag);
    }

    bitwidth_t contractedWidth = bitWidth - amount;

    auto tmp = lshr(amount);
    tmp.signExtendFrom(contractedWidth - 1);
    return tmp;
}

SVInt SVInt::replicate(const SVInt& times) const {
    uint32_t n = times.as<uint32_t>().value();
    SmallVector<SVInt> buffer(n, UninitializedTag());
    for (size_t i = 0; i < n; ++i)
        buffer.push_back(*this);
    return concat(std::span<SVInt const>(buffer.begin(), buffer.end()));
}

size_t SVInt::hash() const {
    return (size_t)detail::hashing::hash(getRawData(), getNumWords() * WORD_SIZE);
}

std::ostream& operator<<(std::ostream& os, const SVInt& rhs) {
    os << rhs.toString();
    return os;
}

std::string SVInt::toString(bitwidth_t abbreviateThresholdBits, bool exactUnknowns) const {
    // guess the base to use
    // unknown bits require binary base for lossless representation
    LiteralBase base;
    if ((bitWidth < 8 && !signFlag) || (unknownFlag && exactUnknowns) ||
        (unknownFlag && bitWidth <= 64)) {
        base = LiteralBase::Binary;
    }
    else if (bitWidth <= 32 || signFlag) {
        base = LiteralBase::Decimal;
    }
    else {
        base = LiteralBase::Hex;
    }

    return toString(base, abbreviateThresholdBits);
}

std::string SVInt::toString(LiteralBase base, bitwidth_t abbreviateThresholdBits) const {
    // Append the base unless we're a signed 32-bit base 10 integer.
    bool includeBase = base != LiteralBase::Decimal || bitWidth != 32 || !signFlag || unknownFlag;

    SmallVector<char> buffer;
    writeTo(buffer, base, includeBase, abbreviateThresholdBits);
    return std::string(buffer.begin(), buffer.end());
}

std::string SVInt::toString(LiteralBase base, bool includeBase,
                            bitwidth_t abbreviateThresholdBits) const {
    SmallVector<char> buffer;
    writeTo(buffer, base, includeBase, abbreviateThresholdBits);
    return std::string(buffer.begin(), buffer.end());
}

void SVInt::writeTo(SmallVectorBase<char>& buffer, LiteralBase base,
                    bitwidth_t abbreviateThresholdBits) const {
    // Append the base unless we're a signed 32-bit base 10 integer.
    bool includeBase = base != LiteralBase::Decimal || bitWidth != 32 || !signFlag || unknownFlag;
    writeTo(buffer, base, includeBase, abbreviateThresholdBits);
}

void SVInt::writeTo(SmallVectorBase<char>& buffer, LiteralBase base, bool includeBase,
                    bitwidth_t abbreviateThresholdBits) const {
    // negative sign if necessary
    SVInt tmp(*this);
    if (signFlag && !unknownFlag && isNegative()) {
        tmp = -tmp;
        buffer.push_back('-');
    }

    // If the number is larger than the threshold to abbreviate,
    // force it to print as a decimal.
    bitwidth_t activeBits = tmp.getActiveBits();
    if (activeBits > abbreviateThresholdBits) {
        includeBase = true;
        base = LiteralBase::Decimal;
    }

    if (includeBase) {
        uintToStr(buffer, bitWidth);
        buffer.push_back('\'');
        if (signFlag)
            buffer.push_back('s');
        switch (base) {
            case LiteralBase::Binary:
                buffer.push_back('b');
                break;
            case LiteralBase::Octal:
                buffer.push_back('o');
                break;
            case LiteralBase::Decimal:
                buffer.push_back('d');
                break;
            case LiteralBase::Hex:
                buffer.push_back('h');
                break;
        }
    }

    uint32_t base10Exponent = 0;
    size_t startOffset = buffer.size();
    static const char Digits[] = "0123456789abcdef";
    if (base == LiteralBase::Decimal) {
        // decimal numbers that have unknown values only print as a single letter,
        // with the following rules:
        // - If all bits are unknown, print 'x'
        // - If all bits are high impendance, print 'z'
        // - If some bits are unknown, print 'X'
        // - Otherwise, if some bits are high impedance , print 'Z'
        if (unknownFlag) {
            uint64_t mask;
            bitwidth_t bitsInMsw;
            uint32_t words = getNumWords(bitWidth, false);
            getTopWordMask(bitsInMsw, mask);

            auto all = [&](uint32_t start, uint64_t v) {
                for (uint32_t i = 0; i < words - 1; i++) {
                    if (pVal[start + i] != v)
                        return false;
                }

                return pVal[start + words - 1] == (mask & v);
            };

            auto anyXs = [&]() {
                for (uint32_t i = 0; i < words - 1; i++) {
                    if ((~pVal[i] & pVal[i + words]) != 0)
                        return true;
                }

                return (~pVal[words - 1] & mask & pVal[words * 2 - 1]) != 0;
            };

            bool upperOnes = all(words, UINT64_MAX);
            if (upperOnes && all(0, UINT64_MAX))
                buffer.push_back('z');
            else if (upperOnes && all(0, 0))
                buffer.push_back('x');
            else if (anyXs())
                buffer.push_back('X');
            else
                buffer.push_back('Z');
        }
        else {
            // Limit the size of the output string based on the given threshold.
            if (activeBits > abbreviateThresholdBits) {
                base10Exponent =
                    std::max(5u, (uint32_t)ceil((activeBits - abbreviateThresholdBits) / log2_10));
                SVInt divisor(bitwidth_t(ceil(base10Exponent * log2_10)), 10, false);
                divisor = divisor.pow(base10Exponent);

                SVInt remainder;
                SVInt quotient;
                divide(tmp, tmp.getNumWords(), divisor, divisor.getNumWords(), &quotient,
                       &remainder);
                tmp = quotient;
            }

            // repeatedly divide by 10 to get each digit
            SVInt divisor(4, 10, false);
            while (tmp != 0) {
                SVInt remainder;
                SVInt quotient;
                divide(tmp, tmp.getNumWords(), divisor, divisor.getNumWords(), &quotient,
                       &remainder);
                uint64_t digit = remainder.as<uint64_t>().value();
                SLANG_ASSERT(digit < 10);
                buffer.push_back(Digits[digit]);
                tmp = quotient;
            }
        }
    }
    else {
        // for bases 2, 8, and 16 we can just shift instead of dividing
        uint32_t shiftAmount = 0;
        uint32_t maskAmount = 0;
        switch (base) {
            case LiteralBase::Binary:
                shiftAmount = 1;
                maskAmount = 1;
                break;
            case LiteralBase::Octal:
                shiftAmount = 3;
                maskAmount = 7;
                break;
            case LiteralBase::Hex:
                shiftAmount = 4;
                maskAmount = 15;
                break;
            case LiteralBase::Decimal:
                SLANG_UNREACHABLE;
        }

        // if we have unknown values here, the comparison will return X
        // we want to keep going so that we print the unknowns
        int bitsLeft = int(tmp.getBitWidth());
        logic_t x = tmp != 0;
        while (x || x.isUnknown()) {
            if (bitsLeft < int(shiftAmount))
                maskAmount = (1 << bitsLeft) - 1;

            uint32_t digit = uint32_t(tmp.getRawData()[0]) & maskAmount;
            if (!tmp.unknownFlag)
                buffer.push_back(Digits[digit]);
            else {
                uint32_t u = uint32_t(tmp.pVal[getNumWords(bitWidth, false)]) & maskAmount;
                if (!u)
                    buffer.push_back(Digits[digit]);
                else if (u == maskAmount && (digit & maskAmount) == 0)
                    buffer.push_back('x');
                else if (u == maskAmount && digit == maskAmount)
                    buffer.push_back('z');
                else if (~digit & u)
                    buffer.push_back('X');
                else
                    buffer.push_back('Z');
            }
            // this shift might shift away the unknown digits, at which point
            // it converts back to being a normal 2-state value
            tmp = tmp.lshr(shiftAmount);
            bitsLeft -= int(shiftAmount);
            x = tmp != 0;
        }

        // If there are bits left over and the last digit we pushed was
        // an unknown we need to insert an extra 0 to indicate that the
        // leading bits are actually zeroes and not extended unknowns.
        if (bitsLeft > 0 && !buffer.empty() && (buffer.back() == 'x' || buffer.back() == 'z'))
            buffer.push_back('0');
    }

    // no digits means this is zero
    if (startOffset == buffer.size())
        buffer.push_back('0');
    else {
        // reverse the digits
        std::ranges::reverse(buffer.begin() + startOffset, buffer.end());
        if (base10Exponent > 0) {
            buffer.append_range("...e"sv);
            uintToStr(buffer, base10Exponent);
        }
    }
}

SVInt SVInt::pow(const SVInt& rhs) const {
    // ignore unknowns
    if (unknownFlag || rhs.unknownFlag)
        return createFillX(bitWidth, signFlag);

    // Handle special cases first (note that the result always has
    // the bit width of *this)
    bitwidth_t lhsBits = getActiveBits();
    bitwidth_t rhsBits = rhs.getActiveBits();
    // The second operand of the power operator shall be treated as self-determined
    if (lhsBits == 0) {
        if (rhsBits == 0) // 0**0 == 1
            return SVInt(bitWidth, 1, signFlag);
        if (rhs.signFlag && rhs.isNegative()) // 0**-y == x
            return createFillX(bitWidth, signFlag);
        // 0**y == 0
        return SVInt(bitWidth, 0, signFlag);
    }

    // x**0 == 1 || 1**y == 1
    if (rhsBits == 0 || lhsBits == 1)
        return SVInt(bitWidth, 1, signFlag);

    if (signFlag && isNegative()) {
        if (reductionAnd()) { // x == -1
            // if rhs is odd, result is -1
            // otherwise, result is 1
            if (rhs.isOdd())
                return SVInt(bitWidth, UINT64_MAX, signFlag);
            else
                return SVInt(bitWidth, 1, signFlag);
        }
    }

    if (rhs.signFlag && rhs.isNegative()) // x**-y == 0
        return SVInt(bitWidth, 0, signFlag);

    // we have one of two cases left (rhs is always positive here):
    // 1. lhs > 1 (just do the operation)
    // 2. lhs < -1 (invert, do the op, figure out the sign at the end)
    if (signFlag && isNegative()) {
        // result is negative if rhs is odd, otherwise positive
        if (rhs.isOdd())
            return -modPow(-(*this), rhs, signFlag);
        else
            return modPow(-(*this), rhs, signFlag);
    }

    // Optimization for the common case of 2**y
    if (lhsBits == 2 && getRawData()[0] == 2)
        return SVInt(bitWidth, 1, signFlag).shl(rhs);

    return modPow(*this, rhs, signFlag);
}

logic_t SVInt::reductionAnd() const {
    uint64_t mask;
    bitwidth_t bitsInMsw;
    getTopWordMask(bitsInMsw, mask);

    if (unknownFlag) {
        uint32_t words = getNumWords(bitWidth, false);
        for (uint32_t i = 0; i < words - 1; i++) {
            if ((pVal[i] | pVal[i + words]) != UINT64_MAX)
                return logic_t(false);
        }
        if ((pVal[words - 1] | pVal[words * 2 - 1]) != mask)
            return logic_t(false);
        return logic_t::x;
    }

    if (isSingleWord())
        return logic_t(val == mask);
    else {
        for (uint32_t i = 0; i < getNumWords() - 1; i++) {
            if (pVal[i] != UINT64_MAX)
                return logic_t(false);
        }
        return logic_t(pVal[getNumWords() - 1] == mask);
    }
}

logic_t SVInt::reductionOr() const {
    if (unknownFlag) {
        uint32_t words = getNumWords(bitWidth, false);
        for (uint32_t i = 0; i < words; i++) {
            if (pVal[i] & ~pVal[i + words])
                return logic_t(true);
        }
        return logic_t::x;
    }

    if (isSingleWord())
        return logic_t(val != 0);
    else {
        for (uint32_t i = 0; i < getNumWords(); i++) {
            if (pVal[i] != 0)
                return logic_t(true);
        }
    }
    return logic_t(false);
}

logic_t SVInt::reductionXor() const {
    if (unknownFlag)
        return logic_t::x;

    // reduction xor basically determines whether the number of set
    // bits in the number is even or odd
    uint32_t count = countOnes();
    if (count % 2 == 0)
        return logic_t(0);

    return logic_t(1);
}

SVInt SVInt::operator-() const {
    if (unknownFlag)
        return createFillX(bitWidth, signFlag);
    return SVInt(bitWidth, 0, signFlag) - *this;
}

SVInt SVInt::operator~() const {
    SVInt result(*this);
    uint32_t words = getNumWords(bitWidth, false);

    // just use xor to quickly flip everything
    if (isSingleWord())
        result.val ^= UINT64_MAX;
    else {
        for (uint32_t i = 0; i < words; i++)
            result.pVal[i] ^= UINT64_MAX;
    }

    if (unknownFlag) {
        // any unknown bits are still unknown, but we need to make sure
        // any high impedance values become X's
        for (uint32_t i = 0; i < words; i++)
            result.pVal[i] &= ~result.pVal[i + words];
    }

    result.clearUnusedBits();
    return result;
}

SVInt& SVInt::operator++() {
    if (isSingleWord())
        ++val;
    else if (unknownFlag)
        setAllX();
    else
        addOne(pVal, pVal, getNumWords(), 1);
    clearUnusedBits();
    return *this;
}

SVInt& SVInt::operator--() {
    if (isSingleWord())
        --val;
    else if (unknownFlag)
        setAllX();
    else
        subOne(pVal, pVal, getNumWords(), 1);
    clearUnusedBits();
    return *this;
}

SVInt& SVInt::operator+=(const SVInt& rhs) {
    if (bitWidth != rhs.bitWidth) {
        if (bitWidth < rhs.bitWidth)
            *this = extend(rhs.bitWidth, signFlag && rhs.signFlag);
        else
            return *this += rhs.extend(bitWidth, signFlag && rhs.signFlag);
    }

    if (unknownFlag || rhs.unknownFlag)
        setAllX();
    else {
        if (isSingleWord())
            val += rhs.val;
        else
            addGeneral(pVal, pVal, rhs.pVal, getNumWords());
        clearUnusedBits();
    }
    return *this;
}

SLANG_NO_SANITIZE("unsigned-integer-overflow")
SVInt& SVInt::operator-=(const SVInt& rhs) {
    if (bitWidth != rhs.bitWidth) {
        if (bitWidth < rhs.bitWidth)
            *this = extend(rhs.bitWidth, signFlag && rhs.signFlag);
        else
            return *this -= rhs.extend(bitWidth, signFlag && rhs.signFlag);
    }

    if (unknownFlag || rhs.unknownFlag)
        setAllX();
    else {
        if (isSingleWord())
            val -= rhs.val;
        else
            subGeneral(pVal, pVal, rhs.pVal, getNumWords());
        clearUnusedBits();
    }
    return *this;
}

SVInt& SVInt::operator*=(const SVInt& rhs) {
    if (bitWidth != rhs.bitWidth) {
        if (bitWidth < rhs.bitWidth)
            *this = extend(rhs.bitWidth, signFlag && rhs.signFlag);
        else
            return *this *= rhs.extend(bitWidth, signFlag && rhs.signFlag);
    }

    if (unknownFlag || rhs.unknownFlag)
        setAllX();
    else {
        if (isSingleWord())
            val *= rhs.val;
        else {
            // check for zeros
            bitwidth_t lhsBits = getActiveBits();
            uint32_t lhsWords = !lhsBits ? 0 : whichWord(lhsBits - 1) + 1;
            if (!lhsWords)
                return *this;

            bitwidth_t rhsBits = rhs.getActiveBits();
            uint32_t rhsWords = !rhsBits ? 0 : whichWord(rhsBits - 1) + 1;
            if (!rhsWords) {
                setAllZeros();
                return *this;
            }

            // allocate result space and do the multiply
            uint32_t destWords = lhsWords + rhsWords;
            TempBuffer<uint64_t, 128> dst(destWords);
            mul(dst.get(), pVal, lhsWords, rhs.pVal, rhsWords);

            // copy the result back into *this
            setAllZeros();
            uint32_t wordsToCopy = destWords >= getNumWords() ? getNumWords() : destWords;
            memcpy(pVal, dst.get(), wordsToCopy * WORD_SIZE);
        }
        clearUnusedBits();
    }
    return *this;
}

SVInt& SVInt::operator/=(const SVInt& rhs) {
    *this = *this / rhs;
    return *this;
}

SVInt& SVInt::operator%=(const SVInt& rhs) {
    *this = *this % rhs;
    return *this;
}

SVInt& SVInt::operator&=(const SVInt& rhs) {
    if (bitWidth != rhs.bitWidth) {
        bool bothSigned = signFlag && rhs.signFlag;
        if (bitWidth < rhs.bitWidth)
            *this = extend(rhs.bitWidth, bothSigned);
        else
            return *this &= rhs.extend(bitWidth, bothSigned);
    }

    if (!hasUnknown() && rhs.hasUnknown())
        makeUnknown();

    if (isSingleWord())
        val &= rhs.val;
    else {
        uint32_t words = getNumWords(bitWidth, false);
        if (unknownFlag) {
            if (rhs.isSingleWord()) {
                pVal[1] &= rhs.val;
                pVal[0] = ~pVal[1] & pVal[0] & rhs.val;
            }
            else {
                if (rhs.hasUnknown()) {
                    for (uint32_t i = 0; i < words; i++) {
                        pVal[i + words] = (pVal[i + words] | rhs.pVal[i + words]) &
                                          (pVal[i + words] | pVal[i]) &
                                          (rhs.pVal[i + words] | rhs.pVal[i]);
                    }
                }
                else {
                    for (uint32_t i = 0; i < words; i++)
                        pVal[i + words] &= rhs.pVal[i];
                }

                for (uint32_t i = 0; i < words; i++)
                    pVal[i] = ~pVal[i + words] & pVal[i] & rhs.pVal[i];
            }
        }
        else {
            for (uint32_t i = 0; i < words; i++)
                pVal[i] &= rhs.pVal[i];
        }
    }
    clearUnusedBits();
    checkUnknown();
    return *this;
}

SVInt& SVInt::operator|=(const SVInt& rhs) {
    if (bitWidth != rhs.bitWidth) {
        bool bothSigned = signFlag && rhs.signFlag;
        if (bitWidth < rhs.bitWidth)
            *this = extend(rhs.bitWidth, bothSigned);
        else
            return *this |= rhs.extend(bitWidth, bothSigned);
    }

    if (!hasUnknown() && rhs.hasUnknown())
        makeUnknown();

    if (isSingleWord())
        val |= rhs.val;
    else {
        uint32_t words = getNumWords(bitWidth, false);
        if (unknownFlag) {
            if (rhs.isSingleWord()) {
                pVal[1] &= ~rhs.val;
                pVal[0] = ~pVal[1] & (pVal[0] | rhs.val);
            }
            else {
                if (rhs.hasUnknown()) {
                    for (uint32_t i = 0; i < words; i++) {
                        pVal[i + words] = (pVal[i + words] & (rhs.pVal[i + words] | ~rhs.pVal[i])) |
                                          (~pVal[i] & rhs.pVal[i + words]);
                    }
                }
                else {
                    for (uint32_t i = 0; i < words; i++)
                        pVal[i + words] &= ~rhs.pVal[i];
                }

                for (uint32_t i = 0; i < words; i++)
                    pVal[i] = ~pVal[i + words] & (pVal[i] | rhs.pVal[i]);
            }
        }
        else {
            for (uint32_t i = 0; i < words; i++)
                pVal[i] |= rhs.pVal[i];
        }
    }
    clearUnusedBits();
    checkUnknown();
    return *this;
}

SVInt& SVInt::operator^=(const SVInt& rhs) {
    if (bitWidth != rhs.bitWidth) {
        bool bothSigned = signFlag && rhs.signFlag;
        if (bitWidth < rhs.bitWidth)
            *this = extend(rhs.bitWidth, bothSigned);
        else
            return *this ^= rhs.extend(bitWidth, bothSigned);
    }

    if (!hasUnknown() && rhs.hasUnknown())
        makeUnknown();

    if (isSingleWord())
        val ^= rhs.val;
    else {
        uint32_t words = getNumWords(bitWidth, false);
        if (unknownFlag) {
            if (rhs.isSingleWord())
                pVal[0] = ~pVal[1] & (pVal[0] ^ rhs.val);
            else {
                if (rhs.hasUnknown()) {
                    for (uint32_t i = 0; i < words; i++)
                        pVal[i + words] |= rhs.pVal[i + words];
                }

                for (uint32_t i = 0; i < words; i++)
                    pVal[i] = ~pVal[i + words] & (pVal[i] ^ rhs.pVal[i]);
            }
        }
        else {
            for (uint32_t i = 0; i < words; i++)
                pVal[i] ^= rhs.pVal[i];
        }
    }
    clearUnusedBits();
    return *this;
}

SVInt SVInt::xnor(const SVInt& rhs) const {
    if (bitWidth != rhs.bitWidth) {
        bool bothSigned = signFlag && rhs.signFlag;
        if (bitWidth < rhs.bitWidth)
            return extend(rhs.bitWidth, bothSigned).xnor(rhs);
        else
            return xnor(rhs.extend(bitWidth, bothSigned));
    }

    SVInt result(*this);
    if (!hasUnknown() && rhs.hasUnknown())
        result.makeUnknown();

    if (result.isSingleWord())
        result.val = ~(result.val ^ rhs.val);
    else {
        uint32_t words = getNumWords(bitWidth, false);
        if (result.hasUnknown()) {
            if (rhs.isSingleWord())
                result.pVal[0] = ~result.pVal[1] & ~(result.pVal[0] ^ rhs.val);
            else {
                if (rhs.hasUnknown()) {
                    for (uint32_t i = 0; i < words; i++)
                        result.pVal[i + words] |= rhs.pVal[i + words];
                }

                for (uint32_t i = 0; i < words; i++)
                    result.pVal[i] = ~result.pVal[i + words] & ~(result.pVal[i] ^ rhs.pVal[i]);
            }
        }
        else {
            for (uint32_t i = 0; i < words; i++)
                result.pVal[i] = ~(result.pVal[i] ^ rhs.pVal[i]);
        }
    }
    result.clearUnusedBits();
    return result;
}

SVInt SVInt::operator+(const SVInt& rhs) const {
    SVInt tmp(*this);
    tmp += rhs;
    return tmp;
}

SVInt SVInt::operator-(const SVInt& rhs) const {
    SVInt tmp(*this);
    tmp -= rhs;
    return tmp;
}

SVInt SVInt::operator*(const SVInt& rhs) const {
    SVInt tmp(*this);
    tmp *= rhs;
    return tmp;
}

SVInt SVInt::operator/(const SVInt& rhs) const {
    bool bothSigned = signFlag && rhs.signFlag;
    if (bitWidth != rhs.bitWidth) {
        if (bitWidth < rhs.bitWidth)
            return extend(rhs.bitWidth, bothSigned) / rhs;
        else
            return *this / rhs.extend(bitWidth, bothSigned);
    }

    // Any X's mean all X's; also dividing by zero does the same
    if (unknownFlag || rhs.unknownFlag || rhs == 0)
        return createFillX(bitWidth, bothSigned);

    // handle signed division
    if (bothSigned) {
        // do the division on positive numbers and flip the sign at the end
        if (isNegative()) {
            if (rhs.isNegative())
                return udiv(-(*this), -rhs, true);
            return -udiv(-(*this), rhs, true);
        }
        if (rhs.isNegative())
            return -udiv(*this, -rhs, true);
    }

    // otherwise, just do the division
    return udiv(*this, rhs, bothSigned);
}

SVInt SVInt::operator%(const SVInt& rhs) const {
    bool bothSigned = signFlag && rhs.signFlag;
    if (bitWidth != rhs.bitWidth) {
        if (bitWidth < rhs.bitWidth)
            return extend(rhs.bitWidth, bothSigned) % rhs;
        else
            return *this % rhs.extend(bitWidth, bothSigned);
    }

    // Any X's mean all X's; also dividing by zero does the same
    if (unknownFlag || rhs.unknownFlag || rhs == 0)
        return createFillX(bitWidth, bothSigned);

    // handle signed remainder
    if (bothSigned) {
        // do the remainder on positive numbers and flip the sign at the end
        if (isNegative()) {
            if (rhs.isNegative())
                return -urem(-(*this), -rhs, true);
            return -urem(-(*this), rhs, true);
        }
        if (rhs.isNegative())
            return urem(*this, -rhs, true);
    }

    // otherwise, just do the remainder
    return urem(*this, rhs, false);
}

SVInt SVInt::operator&(const SVInt& rhs) const {
    SVInt tmp(*this);
    tmp &= rhs;
    return tmp;
}

SVInt SVInt::operator|(const SVInt& rhs) const {
    SVInt tmp(*this);
    tmp |= rhs;
    return tmp;
}

SVInt SVInt::operator^(const SVInt& rhs) const {
    SVInt tmp(*this);
    tmp ^= rhs;
    return tmp;
}

logic_t SVInt::operator<(const SVInt& rhs) const {
    if (unknownFlag || rhs.hasUnknown())
        return logic_t::x;

    bool bothSigned = signFlag && rhs.signFlag;
    if (bitWidth != rhs.bitWidth) {
        if (bitWidth < rhs.bitWidth)
            return extend(rhs.bitWidth, bothSigned) < rhs;
        else
            return *this < rhs.extend(bitWidth, bothSigned);
    }
    // handle signed negatives
    if (bothSigned && isNegative() ^ rhs.isNegative())
        return logic_t(isNegative());

    // both are positive or both are negative
    // or not both are signed
    if (isSingleWord())
        return logic_t(val < rhs.val);

    bitwidth_t a1 = getActiveBits();
    bitwidth_t a2 = rhs.getActiveBits();
    if (a1 < a2)
        return logic_t(true);
    if (a2 < a1)
        return logic_t(false);
    if (a1 == 0)
        return logic_t(false); // both values are zero

    // same number of words, compare each one until there's no match
    uint32_t top = whichWord(a1 - 1);
    for (int i = int(top); i >= 0; i--) {
        if (pVal[i] > rhs.pVal[i])
            return logic_t(false);
        if (pVal[i] < rhs.pVal[i])
            return logic_t(true);
    }
    return logic_t(false);
}

logic_t SVInt::operator[](const SVInt& index) const {
    auto value = index.as<int32_t>();
    if (!value)
        return logic_t::x;

    return (*this)[*value];
}

logic_t SVInt::operator[](int32_t index) const {
    bitwidth_t bi = bitwidth_t(index);
    if (index < 0 || bi >= bitWidth)
        return logic_t::x;

    bool bit = (maskBit(bi) & (isSingleWord() ? val : pVal[whichWord(bi)])) != 0;
    if (!unknownFlag)
        return logic_t(bit);

    bool unknownBit = (maskBit(bi) & pVal[whichWord(bi) + getNumWords(bitWidth, false)]) != 0;
    if (!unknownBit)
        return logic_t(bit);

    return bit ? logic_t::z : logic_t::x;
}

SVInt SVInt::slice(int32_t msb, int32_t lsb) const {
    SLANG_ASSERT(msb >= lsb);

    // handle indexing out of bounds
    bitwidth_t selectWidth = bitwidth_t(msb - lsb + 1);
    if (msb < 0 || lsb >= int32_t(bitWidth)) {
        // request is completely out of range, return all xs
        return createFillX(selectWidth, false);
    }

    // variables to keep track of out-of-bounds accesses
    uint32_t frontOOB = lsb < 0 ? uint32_t(-lsb) : 0;
    uint32_t backOOB = bitwidth_t(msb) >= bitWidth ? bitwidth_t(msb - int32_t(bitWidth) + 1) : 0;
    bool anyOOB = frontOOB || backOOB;
    if (isSingleWord() && !anyOOB) {
        // simplest case; 1 word input, 1 word output, no out of bounds
        uint64_t mask = selectWidth == 64 ? UINT64_MAX : (1ull << selectWidth) - 1;
        return SVInt(selectWidth, (val >> lsb) & mask, false);
    }

    // core part of the method: copy over the proper number of bits
    uint32_t validSelectWidth = selectWidth - frontOOB - backOOB;
    SVInt result;
    if (selectWidth > 64 || unknownFlag || anyOOB)
        result = SVInt::allocZeroed(selectWidth, signFlag, unknownFlag || anyOOB);
    else
        result = SVInt(selectWidth, 0, signFlag);
    bitcpy(result.getRawData(), frontOOB, getRawData(), validSelectWidth,
           frontOOB ? 0 : uint32_t(lsb));

    if (unknownFlag) {
        // copy over preexisting unknown data
        uint32_t words = getNumWords(selectWidth, false);
        bitcpy(result.getRawData() + words, frontOOB, pVal + getNumWords() / 2, validSelectWidth,
               frontOOB ? 0 : uint32_t(lsb));
    }

    // If we had any out of bounds accesses, fill them with x's.
    if (anyOOB) {
        uint64_t* dest = result.getRawData() + getNumWords(selectWidth, false);
        setBits(dest, 0, frontOOB);
        setBits(dest, validSelectWidth + frontOOB, backOOB);
    }

    result.clearUnusedBits();
    result.checkUnknown();
    return result;
}

void SVInt::set(int32_t msb, int32_t lsb, const SVInt& value) {
    SLANG_ASSERT(msb >= lsb);

    bitwidth_t selectWidth = bitwidth_t(msb - lsb + 1);
    SLANG_ASSERT(value.getBitWidth() == selectWidth);
    if (msb < 0 || lsb >= int32_t(bitWidth))
        return;

    uint32_t frontOOB = lsb < 0 ? uint32_t(-lsb) : 0;
    uint32_t backOOB = bitwidth_t(msb) >= bitWidth ? bitwidth_t(msb - int32_t(bitWidth) + 1) : 0;
    uint32_t validSelectWidth = selectWidth - frontOOB - backOOB;

    if (!hasUnknown() && value.hasUnknown()) {
        uint64_t* newData = new uint64_t[getNumWords(bitWidth, true)]();
        memcpy(newData, getRawData(), getNumWords());

        if (!isSingleWord())
            delete[] pVal;

        unknownFlag = true;
        pVal = newData;
    }

    bitcpy(getRawData(), (uint32_t)std::max(lsb, 0), value.getRawData(), validSelectWidth,
           frontOOB);
    if (value.unknownFlag) {
        bitcpy(getRawData() + getNumWords(bitWidth, false), (uint32_t)std::max(lsb, 0),
               value.getRawData() + getNumWords(value.bitWidth, false), validSelectWidth, frontOOB);
    }
    else if (unknownFlag) {
        // We have to unset any of the unknown bits for the given segment.
        clearBits(getRawData() + getNumWords(bitWidth, false), (uint32_t)std::max(lsb, 0),
                  validSelectWidth);
    }

    clearUnusedBits();
    checkUnknown();
}

SVInt SVInt::sext(bitwidth_t bits) const {
    SLANG_ASSERT(bits > bitWidth);

    if (bits <= SVInt::BITS_PER_WORD && !unknownFlag) {
        uint64_t newVal = val << (SVInt::BITS_PER_WORD - bitWidth); // NOLINT
        newVal = uint64_t((int64_t)newVal >> (bits - bitWidth));
        return SVInt(bits, newVal >> (SVInt::BITS_PER_WORD - bits), signFlag);
    }

    // copy and sign extend; for unknown values, this copies the data words
    // but not the unknown-indicator words, which we do separately below
    SVInt result = SVInt::allocUninitialized(bits, signFlag, unknownFlag);
    uint32_t oldWords = SVInt::getNumWords(bitWidth, false);
    uint32_t newWords = SVInt::getNumWords(bits, false);
    signExtendCopy(result.pVal, getRawData(), bitWidth, oldWords, newWords);

    if (unknownFlag)
        signExtendCopy(result.pVal + newWords, pVal + oldWords, bitWidth, oldWords, newWords);

    result.clearUnusedBits();
    return result;
}

bool SVInt::isSignExtendedFrom(bitwidth_t msb) const {
    if (msb >= bitWidth - 1)
        return true;

    uint64_t maskMsw;
    bitwidth_t bitsInMsw;
    getTopWordMask(bitsInMsw, maskMsw);

    if (isSingleWord()) {
        auto signBits = val >> msb;
        return !signBits || signBits == maskMsw >> msb;
    }

    auto bit = whichBit(msb);
    auto word = whichWord(msb);
    auto numWords = getNumWords(bitWidth, false);

    if (!isSignExtended(pVal, numWords, word, bit, maskMsw))
        return false;

    if (!unknownFlag)
        return true;

    return isSignExtended(pVal + numWords, numWords, word, bit, maskMsw);
}

void SVInt::signExtendFrom(bitwidth_t msb) {
    SLANG_ASSERT(msb < bitWidth - 1);

    uint64_t maskMsw;
    bitwidth_t bitsInMsw;
    getTopWordMask(bitsInMsw, maskMsw);

    if (isSingleWord()) {
        if (val & (1ULL << msb))
            val |= (UINT64_MAX << msb) & maskMsw;
        return;
    }

    auto bit = whichBit(msb);
    auto word = whichWord(msb);
    auto numWords = getNumWords(bitWidth, false);

    signExtend(pVal, numWords, word, bit, maskMsw);
    if (unknownFlag)
        signExtend(pVal + numWords, numWords, word, bit, maskMsw);
}

SVInt SVInt::zext(bitwidth_t bits) const {
    SLANG_ASSERT(bits > bitWidth);

    if (bits <= SVInt::BITS_PER_WORD && !unknownFlag)
        return SVInt(bits, val, signFlag);

    SVInt result = allocZeroed(bits, signFlag, unknownFlag);

    uint32_t valueWords = SVInt::getNumWords(bitWidth, false);
    for (uint32_t i = 0; i < valueWords; i++)
        result.pVal[i] = getRawData()[i];

    if (unknownFlag) {
        uint32_t newWords = SVInt::getNumWords(bits, false);
        for (uint32_t i = 0; i < valueWords; i++)
            result.pVal[i + newWords] = getRawData()[i + valueWords];
    }

    return result;
}

SVInt SVInt::extend(bitwidth_t bits, bool useSign) const {
    return useSign ? sext(bits) : zext(bits);
}

SVInt SVInt::trunc(bitwidth_t bits) const {
    SLANG_ASSERT(bits > 0 && bits <= bitWidth);

    if (isSingleWord()) {
        uint64_t mask = bits == 64 ? UINT64_MAX : (1ull << bits) - 1;
        return SVInt(bits, val & mask, signFlag);
    }

    SVInt result;
    if (bits > 64 || unknownFlag)
        result = SVInt::allocZeroed(bits, signFlag, unknownFlag);
    else
        result = SVInt(bits, 0, signFlag);

    bitcpy(result.getRawData(), 0, getRawData(), bits, 0);

    if (unknownFlag) {
        // copy over preexisting unknown data
        uint32_t words = getNumWords(bits, false);
        bitcpy(result.getRawData() + words, 0, pVal + getNumWords() / 2, bits, 0);
    }

    result.clearUnusedBits();
    result.checkUnknown();
    return result;
}

SVInt SVInt::resize(bitwidth_t bits) const {
    if (bits < bitWidth)
        return trunc(bits);
    if (bits > bitWidth)
        return extend(bits, signFlag);
    return *this;
}

SVInt SVInt::reverse() const {
    if (isSingleWord()) {
        uint64_t r = reverseBits64(val) >> (BITS_PER_WORD - bitWidth);
        return SVInt(bitWidth, r, signFlag);
    }

    auto result = SVInt::allocUninitialized(bitWidth, signFlag, unknownFlag);
    uint32_t words = getNumWords(bitWidth, false);
    uint64_t* dst = result.getRawData();
    const uint64_t* src = getRawData();

    for (uint32_t i = 0; i < words; i++)
        dst[i] = reverseBits64(src[words - i - 1]);

    if (unknownFlag) {
        dst += words;
        src += words;
        for (uint32_t i = 0; i < words; i++)
            dst[i] = reverseBits64(src[words - i - 1]);
    }

    // If we aren't aligned to a multiple of 64 bits, we need to shift
    // the result back down because we reversed some bits that weren't
    // actually included in the number.
    bitwidth_t msw = bitWidth % BITS_PER_WORD;
    if (msw != 0)
        return result.lshr(BITS_PER_WORD - msw);

    return result;
}

SVInt SVInt::conditional(const SVInt& condition, const SVInt& lhs, const SVInt& rhs) {
    bool bothSigned = lhs.signFlag && rhs.signFlag;
    if (lhs.bitWidth != rhs.bitWidth) {
        if (lhs.bitWidth < rhs.bitWidth)
            return conditional(condition, lhs.extend(rhs.bitWidth, bothSigned), rhs);
        else
            return conditional(condition, lhs, rhs.extend(lhs.bitWidth, bothSigned));
    }

    logic_t c = (logic_t)condition;
    if (!c.isUnknown())
        return c ? lhs : rhs;

    if (exactlyEqual(lhs, rhs))
        return rhs;

    SVInt result = SVInt::allocUninitialized(lhs.bitWidth, bothSigned, true);
    uint32_t words = getNumWords(lhs.bitWidth, false);

    for (uint32_t i = 0; i < words; i++) {
        // Unknown if either bit is unknown or bits differ.
        const uint64_t* lp = lhs.getRawData();
        const uint64_t* rp = rhs.getRawData();
        result.pVal[i + words] = (lhs.unknownFlag ? lp[i + words] : 0) |
                                 (rhs.unknownFlag ? rp[i + words] : 0) | (lp[i] ^ rp[i]);
        result.pVal[i] = ~result.pVal[i + words] & lp[i] & rp[i];
    }

    result.clearUnusedBits();
    return result;
}

SVInt SVInt::concat(std::span<SVInt const> operands) {
    // 0 operand concatenations can be valid inside of larger concatenations.
    if (operands.size() == 0)
        return SVInt::Zero;

    // First, compute how many bits total we are dealing with.
    bitwidth_t bits = 0;
    bool isUnknown = false;
    for (const auto& op : operands) {
        bits += op.bitWidth;
        isUnknown |= op.unknownFlag;
    }

    uint32_t words = SVInt::getNumWords(bits, isUnknown);
    if (words == 1 || bits == 0) {
        // The concatenation still fits into a single word.
        bitwidth_t offset = 0;
        uint64_t val = 0;

        // The first operand writes the msb, so operate in reverse.
        for (auto it = operands.rbegin(); it != operands.rend(); it++) {
            bitcpy(&val, offset, &it->val, it->bitWidth);
            offset += it->bitWidth;
        }
        return SVInt(bits, val, false);
    }

    // Result data is zeroed out, which is the proper default, so it doesn't
    // matter that we may not write to certain unknown words or might not
    // write all the way to the end.
    SVInt result = SVInt::allocZeroed(bits, false, isUnknown);

    bitwidth_t offset = 0;
    for (auto it = operands.rbegin(); it != operands.rend(); it++) {
        bitcpy(result.getRawData(), offset, it->getRawData(), it->bitWidth);
        if (it->unknownFlag) {
            bitcpy(result.getRawData() + words / 2, offset, it->pVal + it->getNumWords() / 2,
                   it->bitWidth);
        }
        offset += it->bitWidth;
    }

    return result;
}

SVInt SVInt::allocUninitialized(bitwidth_t bits, bool signFlag, bool unknownFlag) {
    SLANG_ASSERT(bits && (bits > 64 || unknownFlag));
    return SVInt(new uint64_t[getNumWords(bits, unknownFlag)], bits, signFlag, unknownFlag);
}

SVInt SVInt::allocZeroed(bitwidth_t bits, bool signFlag, bool unknownFlag) {
    SLANG_ASSERT(bits && (bits > 64 || unknownFlag));
    return SVInt(new uint64_t[getNumWords(bits, unknownFlag)](), bits, signFlag, unknownFlag);
}

void SVInt::initSlowCase(logic_t bit) {
    pVal = new uint64_t[getNumWords()](); // allocation is zero cleared
    pVal[1] = 1;
    if (exactlyEqual(bit, logic_t::z))
        pVal[0] = 1;
}

void SVInt::initSlowCase(uint64_t value) {
    uint32_t words = getNumWords();
    pVal = new uint64_t[words](); // allocation is zero cleared
    pVal[0] = value;

    // sign extend if necessary
    if (signFlag && int64_t(value) < 0) {
        for (uint32_t i = 1; i < words; i++)
            pVal[i] = (uint64_t)(-1);
    }
}

void SVInt::initSlowCase(std::span<const byte> bytes) {
    if (isSingleWord()) {
        val = 0;
        memcpy(&val, bytes.data(), std::min<size_t>(WORD_SIZE, bytes.size()));
    }
    else {
        uint32_t words = getNumWords();
        pVal = new uint64_t[words](); // allocation is zero cleared
        memcpy(pVal, bytes.data(), std::min<size_t>(words * WORD_SIZE, bytes.size()));
    }
    clearUnusedBits();
}

void SVInt::initSlowCase(const SVIntStorage& other) {
    uint32_t words = getNumWords();
    pVal = new uint64_t[words];
    std::ranges::copy(other.pVal, other.pVal + words, pVal);
}

SVInt& SVInt::assignSlowCase(const SVInt& rhs) {
    if (this == &rhs)
        return *this;

    if (rhs.isSingleWord()) {
        delete[] pVal;
        val = rhs.val;
    }
    else {
        if (isSingleWord()) {
            pVal = new uint64_t[rhs.getNumWords()];
        }
        else if (getNumWords() != rhs.getNumWords()) {
            delete[] pVal;
            pVal = new uint64_t[rhs.getNumWords()];
        }
        memcpy(pVal, rhs.pVal, rhs.getNumWords() * WORD_SIZE);
    }
    bitWidth = rhs.bitWidth;
    signFlag = rhs.signFlag;
    unknownFlag = rhs.unknownFlag;
    return *this;
}

logic_t SVInt::equalsSlowCase(const SVInt& rhs) const {
    if (unknownFlag || rhs.unknownFlag) {
        // We can't know whether the numbers are definitely equal, but if there is a 0/1 pair, it is
        // definitely not equal. xor detects 0/1 pairs for each bit and !reductionOr collects all
        // pairs.
        return !(*this ^ rhs).reductionOr();
    }

    // handle unequal bit widths; spec says that if both values are signed, then do sign
    // extension
    const uint64_t* lval = pVal;
    const uint64_t* rval = rhs.pVal;

    if (bitWidth != rhs.bitWidth) {
        if (signFlag && rhs.signFlag) {
            if (bitWidth < rhs.bitWidth)
                return sext(rhs.bitWidth).equalsSlowCase(rhs);
            else
                return rhs.sext(bitWidth).equalsSlowCase(*this);
        }

        if (isSingleWord())
            lval = &val;
        if (rhs.isSingleWord())
            rval = &rhs.val;
    }

    bitwidth_t a1 = getActiveBits();
    bitwidth_t a2 = rhs.getActiveBits();
    if (a1 != a2)
        return logic_t(false);

    if (a1 == 0)
        return logic_t(true);

    // compare each word
    uint32_t limit = whichWord(a1 - 1);
    for (uint32_t i = 0; i <= limit; i++) {
        if (lval[i] != rval[i])
            return logic_t(false);
    }

    return logic_t(true);
}

void SVInt::getTopWordMask(bitwidth_t& bitsInMsw, uint64_t& mask) const {
    bitsInMsw = bitWidth % BITS_PER_WORD;
    if (bitsInMsw)
        mask = (1ull << bitsInMsw) - 1;
    else {
        mask = UINT64_MAX;
        bitsInMsw = BITS_PER_WORD;
    }
}

bitwidth_t SVInt::countLeadingZerosSlowCase() const {
    // Most significant word might have extra bits that shouldn't count
    uint64_t mask;
    bitwidth_t bitsInMsw;
    getTopWordMask(bitsInMsw, mask);

    uint32_t i = getNumWords();
    uint64_t part = pVal[i - 1] & mask;
    if (part)
        return (bitwidth_t)std::countl_zero(part) - (BITS_PER_WORD - bitsInMsw);

    bitwidth_t count = bitsInMsw;
    for (--i; i > 0; --i) {
        if (pVal[i - 1] == 0)
            count += BITS_PER_WORD;
        else {
            count += (bitwidth_t)std::countl_zero(pVal[i - 1]);
            break;
        }
    }
    return count;
}

bitwidth_t SVInt::countLeadingOnesSlowCase() const {
    bitwidth_t bitsInMsw = bitWidth % BITS_PER_WORD;
    uint32_t shift = 0;
    if (!bitsInMsw)
        bitsInMsw = BITS_PER_WORD;
    else
        shift = BITS_PER_WORD - bitsInMsw;

    int i = int(getNumWords() - 1);
    bitwidth_t count = (bitwidth_t)std::countl_one(pVal[i] << shift);
    if (count == bitsInMsw) {
        for (i--; i >= 0; i--) {
            if (pVal[i] == UINT64_MAX)
                count += BITS_PER_WORD;
            else {
                count += (bitwidth_t)std::countl_one(pVal[i]);
                break;
            }
        }
    }

    return count;
}

bitwidth_t SVInt::countLeadingUnknowns() const {
    if (!hasUnknown())
        return 0;

    bitwidth_t bitsInMsw = bitWidth % BITS_PER_WORD;
    uint32_t shift = 0;
    if (!bitsInMsw)
        bitsInMsw = BITS_PER_WORD;
    else
        shift = BITS_PER_WORD - bitsInMsw;

    int words = (int)getNumWords(bitWidth, false);
    int i = words - 1;
    bitwidth_t count = (bitwidth_t)std::countl_one(pVal[i + words] << shift);
    if (count == bitsInMsw) {
        for (i--; i >= 0; i--) {
            if (pVal[i + words] == UINT64_MAX)
                count += BITS_PER_WORD;
            else {
                count += (bitwidth_t)std::countl_one(pVal[i + words]);
                break;
            }
        }
    }

    return count;
}

bitwidth_t SVInt::countLeadingZs() const {
    if (!hasUnknown())
        return 0;

    bitwidth_t bitsInMsw = bitWidth % BITS_PER_WORD;
    uint32_t shift = 0;
    if (!bitsInMsw)
        bitsInMsw = BITS_PER_WORD;
    else
        shift = BITS_PER_WORD - bitsInMsw;

    int words = (int)getNumWords(bitWidth, false);
    int i = words - 1;
    bitwidth_t count = (bitwidth_t)std::countl_one((pVal[i + words] & pVal[i]) << shift);
    if (count == bitsInMsw) {
        for (i--; i >= 0; i--) {
            auto elem = pVal[i + words] & pVal[i];
            if (elem == UINT64_MAX)
                count += BITS_PER_WORD;
            else {
                count += (bitwidth_t)std::countl_one(elem);
                break;
            }
        }
    }

    return count;
}

bitwidth_t SVInt::countOnes() const {
    if (isSingleWord())
        return (bitwidth_t)std::popcount(val);

    bitwidth_t count = 0;
    if (!unknownFlag) {
        for (uint32_t i = 0; i < getNumWords(); i++)
            count += (bitwidth_t)std::popcount(pVal[i]);
    }
    else {
        uint32_t words = getNumWords(bitWidth, false);
        for (uint32_t i = 0; i < words; i++)
            count += (bitwidth_t)std::popcount(pVal[i] & ~pVal[i + words]);
    }

    return count;
}

bitwidth_t SVInt::countZeros() const {
    if (isSingleWord())
        return bitWidth - (bitwidth_t)std::popcount(val);

    bitwidth_t count = 0;
    if (!unknownFlag) {
        for (uint32_t i = 0; i < getNumWords(); i++)
            count += (bitwidth_t)std::popcount(~pVal[i]);
    }
    else {
        uint32_t words = getNumWords(bitWidth, false);
        for (uint32_t i = 0; i < words; i++)
            count += (bitwidth_t)std::popcount(~pVal[i] & ~pVal[i + words]);
    }

    uint32_t wordBits = bitWidth % BITS_PER_WORD;
    if (wordBits)
        count -= BITS_PER_WORD - wordBits;

    return count;
}

bitwidth_t SVInt::countXs() const {
    if (!unknownFlag)
        return 0;

    bitwidth_t count = 0;
    uint32_t words = getNumWords(bitWidth, false);
    for (uint32_t i = 0; i < words; i++)
        count += (bitwidth_t)std::popcount(~pVal[i] & pVal[i + words]);

    return count;
}

bitwidth_t SVInt::countZs() const {
    if (!unknownFlag)
        return 0;

    bitwidth_t count = 0;
    uint32_t words = getNumWords(bitWidth, false);
    for (uint32_t i = 0; i < words; i++)
        count += (bitwidth_t)std::popcount(pVal[i] & pVal[i + words]);

    return count;
}

void SVInt::clearUnusedBits() {
    // clear out unused bits in the top word after we've assigned something to it
    uint32_t wordBits = bitWidth % BITS_PER_WORD;
    if (wordBits == 0)
        return;

    uint64_t mask = ~uint64_t(0ULL) >> (BITS_PER_WORD - wordBits);
    if (isSingleWord())
        val &= mask;
    else {
        pVal[getNumWords() - 1] &= mask;
        if (unknownFlag)
            pVal[getNumWords(bitWidth, false) - 1] &= mask;
    }
}

void SVInt::checkUnknown() {
    // check if we've lost all of our unknown bits and need
    // to downgrade back to a non-unknown value
    if (!unknownFlag || countLeadingZeros() < bitWidth)
        return;

    unknownFlag = false;
    uint32_t words = getNumWords();
    if (words == 1) {
        uint64_t newVal = pVal[0];
        delete[] pVal;
        val = newVal;
    }
    else {
        uint64_t* newMem = new uint64_t[words];
        memcpy(newMem, pVal, words * WORD_SIZE);
        delete[] pVal;
        pVal = newMem;
    }
}

void SVInt::makeUnknown() {
    if (unknownFlag)
        return;

    uint32_t words = getNumWords();
    unknownFlag = true;
    if (words == 1) {
        auto value = val;
        pVal = new uint64_t[2];
        pVal[0] = value;
        pVal[1] = 0;
    }
    else {
        uint64_t* newMem = new uint64_t[words * 2]();
        memcpy(newMem, pVal, words * WORD_SIZE);
        delete[] pVal;
        pVal = newMem;
    }
}

SVInt SVInt::createFillX(bitwidth_t bitWidth, bool isSigned) {
    SVInt result = SVInt::allocUninitialized(bitWidth, isSigned, true);
    result.setAllX();
    return result;
}

SVInt SVInt::createFillZ(bitwidth_t bitWidth, bool isSigned) {
    SVInt result = SVInt::allocUninitialized(bitWidth, isSigned, true);
    result.setAllZ();
    return result;
}

void SVInt::splitWords(const SVInt& value, uint32_t* dest, uint32_t numWords) {
    for (uint32_t i = 0; i < numWords; i++) {
        uint64_t val = value.getRawData()[i];
        dest[i * 2] = uint32_t(val);
        dest[i * 2 + 1] = uint32_t(val >> 32);
    }
}

void SVInt::buildDivideResult(SVInt* result, uint32_t* value, bitwidth_t bitWidth, bool signFlag,
                              uint32_t numWords) {
    if (!result)
        return;

    if (numWords == 1) {
        uint64_t val = uint64_t(value[0]) | (uint64_t(value[1]) << (BITS_PER_WORD / 2));
        *result = SVInt(bitWidth, val, signFlag);
    }
    else {
        *result = SVInt(bitWidth, 0, signFlag);
        for (uint32_t i = 0; i < numWords; i++)
            result->pVal[i] = uint64_t(value[i * 2]) |
                              (uint64_t(value[i * 2 + 1]) << (BITS_PER_WORD / 2));
    }
}

SLANG_NO_SANITIZE("unsigned-integer-overflow")
void SVInt::divide(const SVInt& lhs, uint32_t lhsWords, const SVInt& rhs, uint32_t rhsWords,
                   SVInt* quotient, SVInt* remainder) {
    SLANG_ASSERT(lhsWords >= rhsWords);

    // The Knuth algorithm requires arrays of 32-bit words (because results of operations
    // need to fit natively into 64 bits). Allocate space for the backing memory, either on
    // the stack if it's small or on the heap if it's not.
    uint32_t divisorWords = rhsWords * 2;
    uint32_t extraWords = (lhsWords * 2) - divisorWords;
    uint32_t dividendWords = divisorWords + extraWords;

    size_t totalWordsNeeded = (remainder ? 4 : 3) * divisorWords + 2 * extraWords + 1;
    TempBuffer<uint32_t, 128> scratch(totalWordsNeeded);
    uint32_t* u = scratch.get();
    uint32_t* v = u + dividendWords + 1;
    uint32_t* q = v + divisorWords;
    uint32_t* r = remainder ? q + dividendWords : nullptr;

    // Initialize the dividend and divisor
    memset(u, 0, (dividendWords + 1) * sizeof(uint32_t));
    splitWords(lhs, u, lhsWords);

    memset(v, 0, divisorWords * sizeof(uint32_t));
    splitWords(rhs, v, rhsWords);

    // Initialize quotient and remainder
    memset(q, 0, dividendWords * sizeof(uint32_t));
    if (remainder)
        memset(r, 0, divisorWords * sizeof(uint32_t));

    // extra word for spill space in Knuth algorithm
    u[dividendWords] = 0;

    // Adjust sizes for division. The Knuth algorithm will fail if there
    // are empty words in the input.
    for (uint32_t i = divisorWords; i > 0 && v[i - 1] == 0; i--) {
        divisorWords--;
        extraWords++;
    }
    for (uint32_t i = dividendWords; i > 0 && u[i - 1] == 0; i--)
        extraWords--;

    // If we're left with only a single divisor word, Knuth won't work.
    // We can use a sequence of standard 64 bit divides for this.
    dividendWords = divisorWords + extraWords;
    if (divisorWords == 1) {
        uint32_t divisor = v[0];
        uint32_t rem = 0;
        for (int i = int(dividendWords - 1); i >= 0; i--) {
            uint64_t partial_dividend = uint64_t(rem) << 32 | u[i];
            if (partial_dividend == 0) {
                q[i] = 0;
                rem = 0;
            }
            else if (partial_dividend < divisor) {
                q[i] = 0;
                rem = (uint32_t)partial_dividend;
            }
            else if (partial_dividend == divisor) {
                q[i] = 1;
                rem = 0;
            }
            else {
                q[i] = (uint32_t)(partial_dividend / divisor);
                rem = (uint32_t)(partial_dividend - (q[i] * divisor));
            }
        }
        if (r)
            r[0] = rem;
    }
    else {
        // otherwise invoke Knuth
        knuthDiv(u, v, q, r, extraWords, divisorWords);
    }

    bool bothSigned = lhs.signFlag && rhs.signFlag;
    buildDivideResult(quotient, q, lhs.bitWidth, bothSigned, lhsWords);
    buildDivideResult(remainder, r, rhs.bitWidth, bothSigned, rhsWords);
}

SVInt SVInt::udiv(const SVInt& lhs, const SVInt& rhs, bool bothSigned) {
    // At this point we have two values with the same bit widths, both positive,
    // and X's have been dealt with. Also, we know rhs isn't zero.
    if (lhs.isSingleWord())
        return SVInt(lhs.bitWidth, lhs.val / rhs.val, bothSigned);

    bitwidth_t lhsBits = lhs.getActiveBits();
    uint32_t lhsWords = !lhsBits ? 0 : (whichWord(lhsBits - 1) + 1);
    bitwidth_t rhsBits = rhs.getActiveBits();
    uint32_t rhsWords = !rhsBits ? 0 : (whichWord(rhsBits - 1) + 1);

    // 0 / X
    if (!lhsWords)
        return SVInt(lhs.bitWidth, 0, bothSigned);
    // X / X
    if (&lhs == &rhs)
        return SVInt(lhs.bitWidth, 1, bothSigned);
    // X / Y where X < Y
    if (lhsWords < rhsWords || lhs < rhs)
        return SVInt(lhs.bitWidth, 0, bothSigned);
    // X and Y are actually a single word
    if (lhsWords == 1 && rhsWords == 1)
        return SVInt(lhs.bitWidth, lhs.pVal[0] / rhs.pVal[0], bothSigned);

    // compute it the hard way with the Knuth algorithm
    SVInt quotient;
    divide(lhs, lhsWords, rhs, rhsWords, &quotient, nullptr);
    return quotient;
}

SVInt SVInt::urem(const SVInt& lhs, const SVInt& rhs, bool bothSigned) {
    // At this point we have two values with the same bit widths, both positive,
    // and X's have been dealt with. Also, we know rhs isn't zero.
    if (lhs.isSingleWord())
        return SVInt(lhs.bitWidth, lhs.val % rhs.val, bothSigned);

    bitwidth_t lhsBits = lhs.getActiveBits();
    uint32_t lhsWords = !lhsBits ? 0 : (whichWord(lhsBits - 1) + 1);
    bitwidth_t rhsBits = rhs.getActiveBits();
    uint32_t rhsWords = !rhsBits ? 0 : (whichWord(rhsBits - 1) + 1);

    // 0 % X
    if (!lhsWords)
        return SVInt(lhs.bitWidth, 0, bothSigned);
    // X % X
    if (&lhs == &rhs)
        return SVInt(lhs.bitWidth, 0, bothSigned);
    // X % Y where X < Y
    if (lhsWords < rhsWords || lhs < rhs)
        return lhs;
    // X and Y are actually a single word
    if (lhsWords == 1)
        return SVInt(lhs.bitWidth, lhs.pVal[0] % rhs.pVal[0], bothSigned);

    // compute it the hard way with the Knuth algorithm
    SVInt remainder;
    divide(lhs, lhsWords, rhs, rhsWords, nullptr, &remainder);
    return remainder;
}

SVInt SVInt::modPow(const SVInt& base, const SVInt& exponent, bool bothSigned) {
    // This is based on the modular exponentiation algorithm described here:
    // https://en.wikipedia.org/wiki/Modular_exponentiation
    //
    // The result value will have the same bit width as the lhs. That's the value we'll
    // be using as the modulus in the (a * b) mod m equation.
    // Allocate a temporary scratch buffer that has 2x the number of bits so that we can
    // handle any possible intermediate multiply.
    TempBuffer<uint64_t, 128> scratch(getNumWords(base.bitWidth * 2, false));
    SVInt baseCopy = base;
    SVInt result(base.bitWidth, 1, false);

    auto mulReduce = [&](const SVInt& left, const SVInt& right, SVInt& result) {
        bitwidth_t lhsBits = left.getActiveBits();
        bitwidth_t rhsBits = right.getActiveBits();
        uint32_t lhsWords = !lhsBits ? 0 : whichWord(lhsBits - 1) + 1;
        uint32_t rhsWords = !rhsBits ? 0 : whichWord(rhsBits - 1) + 1;

        scratch.fill(0);
        mul(scratch.get(), left.getRawData(), lhsWords, right.getRawData(), rhsWords);

        uint32_t destWords = lhsWords + rhsWords;
        if (destWords >= result.getNumWords()) {
            memcpy(result.getRawData(), scratch.get(), result.getNumWords() * sizeof(uint64_t));
            result.clearUnusedBits();
        }
        else {
            memcpy(result.getRawData(), scratch.get(), destWords * sizeof(uint64_t));
            result.clearUnusedBits();
        }
    };

    // Loop through each bit of the exponent.
    uint32_t exponentWords = exponent.getNumWords();
    for (uint32_t i = 0; i < exponentWords - 1; i++) {
        uint64_t word = exponent.getRawData()[i];
        for (int j = 0; j < BITS_PER_WORD; j++) {
            if (word & 0x1)
                mulReduce(result, baseCopy, result);
            mulReduce(baseCopy, baseCopy, baseCopy);
            word >>= 1;
        }
    }

    // Unroll the last loop iteration to avoid multiplications
    // when the rest of the exponent bits are zero
    uint64_t word = exponent.getRawData()[exponentWords - 1];
    while (word) {
        if (word & 0x1)
            mulReduce(result, baseCopy, result);
        if (word != 1)
            mulReduce(baseCopy, baseCopy, baseCopy);
        word >>= 1;
    }

    result.setSigned(bothSigned);
    return result;
}

bool exactlyEqual(const SVInt& lhs, const SVInt& rhs) {
    // if no unknown flags, do normal comparison
    if (!lhs.unknownFlag && !rhs.unknownFlag)
        return (bool)(lhs == rhs);

    // if one has unknown and the other doesn't, they're not equal
    if (!lhs.unknownFlag || !rhs.unknownFlag)
        return false;

    // handle sign extension if necessary
    if (lhs.bitWidth != rhs.bitWidth) {
        bool bothSigned = lhs.signFlag && rhs.signFlag;
        if (lhs.bitWidth < rhs.bitWidth)
            return exactlyEqual(lhs.extend(rhs.bitWidth, bothSigned), rhs);
        else
            return exactlyEqual(lhs, rhs.extend(lhs.bitWidth, bothSigned));
    }

    // ok, equal widths, and they both have unknown values, do a straight memory compare
    return memcmp(lhs.pVal, rhs.pVal, lhs.getNumWords() * SVInt::WORD_SIZE) == 0;
}

logic_t condWildcardEqual(const SVInt& lhs, const SVInt& rhs) {
    // if no unknown flags, do normal comparison
    if (!rhs.unknownFlag)
        return lhs == rhs;

    // handle sign extension if necessary
    if (lhs.bitWidth != rhs.bitWidth) {
        bool bothSigned = lhs.signFlag && rhs.signFlag;
        if (lhs.bitWidth < rhs.bitWidth)
            return condWildcardEqual(lhs.extend(rhs.bitWidth, bothSigned), rhs);
        else
            return condWildcardEqual(lhs, rhs.extend(lhs.bitWidth, bothSigned));
    }

    uint32_t words = SVInt::getNumWords(rhs.bitWidth, false);
    for (uint32_t i = 0; i < words; ++i) {
        // bitmask to avoid comparing the bits unknown on the rhs
        uint64_t mask = ~rhs.pVal[i + words];
        if (lhs.unknownFlag && (lhs.getRawData()[i + words] & mask) != 0)
            return logic_t::x;

        if ((lhs.getRawData()[i] & mask) != (rhs.pVal[i] & mask))
            return logic_t(false);
    }

    return logic_t(true);
}

bool caseXWildcardEqual(const SVInt& lhs, const SVInt& rhs) {
    // if no unknown flags, do normal comparison
    if (!lhs.unknownFlag && !rhs.unknownFlag)
        return exactlyEqual(lhs, rhs);

    // handle sign extension if necessary
    if (lhs.bitWidth != rhs.bitWidth) {
        bool bothSigned = lhs.signFlag && rhs.signFlag;
        if (lhs.bitWidth < rhs.bitWidth)
            return caseXWildcardEqual(lhs.extend(rhs.bitWidth, bothSigned), rhs);
        else
            return caseXWildcardEqual(lhs, rhs.extend(lhs.bitWidth, bothSigned));
    }

    uint32_t words = SVInt::getNumWords(rhs.bitWidth, false);
    for (uint32_t i = 0; i < words; ++i) {
        // bitmask to avoid comparing the unknown bits on either side
        uint64_t mask = UINT64_MAX;
        if (lhs.unknownFlag)
            mask &= ~lhs.pVal[i + words];
        if (rhs.unknownFlag)
            mask &= ~rhs.pVal[i + words];

        if ((lhs.getRawData()[i] & mask) != (rhs.getRawData()[i] & mask))
            return false;
    }

    return true;
}

bool caseZWildcardEqual(const SVInt& lhs, const SVInt& rhs) {
    // if no unknown flags, do normal comparison
    if (!lhs.unknownFlag && !rhs.unknownFlag)
        return exactlyEqual(lhs, rhs);

    // handle sign extension if necessary
    if (lhs.bitWidth != rhs.bitWidth) {
        bool bothSigned = lhs.signFlag && rhs.signFlag;
        if (lhs.bitWidth < rhs.bitWidth)
            return caseZWildcardEqual(lhs.extend(rhs.bitWidth, bothSigned), rhs);
        else
            return caseZWildcardEqual(lhs, rhs.extend(lhs.bitWidth, bothSigned));
    }

    uint32_t words = SVInt::getNumWords(rhs.bitWidth, false);
    for (uint32_t i = 0; i < words; ++i) {
        // bitmask to avoid comparing the Z bits on either side
        uint64_t mask = UINT64_MAX;

        uint64_t lunknown = 0;
        if (lhs.unknownFlag) {
            lunknown = lhs.pVal[i + words] & ~lhs.pVal[i];
            mask &= ~(lhs.pVal[i + words] & lhs.pVal[i]);
        }

        uint64_t runknown = 0;
        if (rhs.unknownFlag) {
            runknown = rhs.pVal[i + words] & ~rhs.pVal[i];
            mask &= ~(rhs.pVal[i + words] & rhs.pVal[i]);
        }

        if ((lhs.getRawData()[i] & mask) != (rhs.getRawData()[i] & mask) ||
            (lunknown & mask) != (runknown & mask)) {
            return false;
        }
    }

    return true;
}

} // namespace slang
