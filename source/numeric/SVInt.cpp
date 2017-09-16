//------------------------------------------------------------------------------
// SVInt.cpp
// Arbitrary precision integer support.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "SVInt.h"

#include <stdexcept>

#include "fmt/format.h"

#include "text/CharInfo.h"
#include "util/Hash.h"

namespace slang {

#include "SVIntHelpers.h"

const logic_t logic_t::x {logic_t::X_VALUE};
const logic_t logic_t::z {logic_t::Z_VALUE};

const SVInt SVInt::Zero {0, false};
const SVInt SVInt::One {1, false};

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

std::ostream& operator<<(std::ostream& os, const logic_t& rhs) {
    if (rhs.value == logic_t::x.value)
        os << "x";
    else if (rhs.value == logic_t::z.value)
        os << "z";
    else
        os << (uint32_t)rhs.value;
    return os;
}

SVInt SVInt::fromString(string_view str) {
    if (str.empty())
        throw std::invalid_argument("String is empty");

    const char* c = str.data();
    const char* end = c + str.length();
    bool negative = *c == '-';
    if (*c == '-' || *c == '+') {
        c++;    // heh
        if (c == end)
            throw std::invalid_argument("String only has a sign?");
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
            // bit widths can't be larger than 2^16, so if the number gets larger
            // then this is either not a size or a bad one
            possibleSize *= 10;
            possibleSize += getDigitValue(d);
            if (possibleSize > UINT16_MAX)
                sizeOverflow = true;
        }
        else if (d != '_') {
            // underscores are allowed as digit separators; anything else means this
            // is not a valid bit width
            sizeBad = true;
        }
    }

    // numbers without a size specifier are assumed to be 32 bits, signed, and in decimal base
    bool signFlag = true;
    uint16_t bitWidth = 32;
    LiteralBase base = LiteralBase::Decimal;

    if (apostrophe) {
        if (sizeBad || sizeOverflow || possibleSize == 0)
            throw std::invalid_argument("Size is invalid (bad chars or overflow 16 bits)");
        bitWidth = (uint16_t)possibleSize;

        c = apostrophe + 1;
        if (c == end)
            throw std::invalid_argument("Nothing after size specifier");

        if (*c == 's' || *c == 'S') {
            signFlag = true;
            c++;
            if (c == end)
                throw std::invalid_argument("Nothing after sign specifier");
        }
        else {
            signFlag = false;
        }

        if (!literalBaseFromChar(*c, base))
            throw std::invalid_argument(fmt::format("Unknown base specifier '{}'", *c));

        c++;
        if (c == end)
            throw std::invalid_argument("Nothing after base specifier");
    }
    else if (sizeBad) {
        throw std::invalid_argument("Not an integer or sized literal");
    }

    // convert the remaining chars to an array of digits to pass to the other
    // constructor
    bool unknownFlag = false;
    SmallVectorSized<logic_t, 16> digits;
    for (; c != end; ++c) {
        char d = *c;
        if (d == '_')
            continue;

        logic_t value;
        switch (d) {
            case 'X':
            case 'x':
                value = logic_t::x;
                unknownFlag = true;
                break;
            case 'Z':
            case 'z':
            case '?':
                value = logic_t::z;
                unknownFlag = true;
                break;
            default:
                value = logic_t(getHexDigitValue(d));
                break;
        }
        digits.append(value);
    }

    SVInt result = fromDigits(bitWidth, base, signFlag, unknownFlag, digits);

    // if it's supposed to be negative, flip it around
    if (negative)
        return -result;
    else
        return result;
}

SVInt SVInt::fromDigits(uint16_t bits, LiteralBase base, bool isSigned,
                        bool anyUnknown, span<logic_t const> digits) {
    if (digits.empty())
        throw std::invalid_argument("No digits provided");

    int radix = 0;
    int shift = 0;
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
            if (d.value >= radix)
                throw std::invalid_argument(fmt::format("Digit {} too large for radix {}", d.value, radix));
        }
        return SVInt(bits, val, isSigned);
    }

    // If the user specified a number too large to fit in the number of bits specified,
    // the spec says to truncate from the left, which this method will successfully do.
    SVInt result = allocZeroed(bits, isSigned, anyUnknown);

    if (radix == 10) {
        SVInt digit(bits, 0, false);
        SVInt radixSv(bits, 10, false);

        for (const logic_t& d : digits) {
            // In base ten we can't have individual bits be X or Z, it's all or nothing
            if (anyUnknown) {
                if (digits.size() != 1)
                    throw std::invalid_argument("If a decimal number is unknown, it must have exactly one digit.");

                if (exactlyEqual(d, logic_t::z))
                    return createFillZ(bits, isSigned);
                else
                    return createFillX(bits, isSigned);
            }

            int value = d.value;
            if (value >= radix)
                throw std::invalid_argument(fmt::format("Digit {} too large for radix {}", value, radix));

            result *= radixSv;
            digit.pVal[0] = value;
            result += digit;
        }
        return result;
    }

    uint32_t numWords = getNumWords(bits, false);
    int ones = (1 << shift) - 1;
    for (const logic_t& d : digits) {
        int unknown = 0;
        int value = d.value;

        if (exactlyEqual(d, logic_t::x)) {
            value = 0;
            unknown = ones;
        }
        else if (exactlyEqual(d, logic_t::z)) {
            value = ones;
            unknown = ones;
        }
        else if (value >= radix) {
            throw std::invalid_argument(fmt::format("Digit {} too large for radix {}", value, radix));
        }

        if (shift >= bits) {
            // We only get here when the number has very few bits but has unknowns,
            // so just clear out the lower word and move on.
            result.pVal[0] = 0;
            result.pVal[numWords] = 0;
        }
        else {
            // Shift, including the unknown bits if necessary.
            shlFar(result.pVal, result.pVal, shift, 0, 0, numWords);
            if (anyUnknown)
                shlFar(result.pVal, result.pVal, shift, 0, numWords, numWords);
        }

        // Because we're shifting bits for the radix involved (2, 8, or 16) we
        // know that the bits we're setting are fresh and all zero, so adding
        // won't cause any kind of carry.
        result.pVal[0] += value;

        if (anyUnknown)
            result.pVal[getNumWords(bits, false)] += unknown;
    }

    result.clearUnusedBits();
    result.checkUnknown();

    if (result.hasUnknown()) {
        // If the most significant bit is X or Z, we need to extend that out to the full range.
        uint32_t givenBits = (uint32_t)digits.size() * shift;
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
    int words = getNumWords(bitWidth, false);
    if (unknownFlag)
        memset(pVal, 0, words * WORD_SIZE);
    else {
        if (!isSingleWord())
            delete[] pVal;

        unknownFlag = true;
        pVal = new uint64_t[words * 2]();
    }

    // now set upper half to ones (for unknown)
    for (int i = words; i < words * 2; i++)
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

SVInt SVInt::shl(const SVInt& rhs) const {
    // if the shift amount is unknown, result is all X's
    if (rhs.hasUnknown())
        return createFillX(bitWidth, signFlag);

    // if the shift amount is too large, we end up with zero anyway
    if (rhs >= bitWidth)
        return SVInt(bitWidth, 0, signFlag);
    return shl(rhs.as<uint32_t>().value());
}

SVInt SVInt::shl(uint32_t amount) const {
    // handle trivial cases
    if (amount == 0)
        return *this;
    if (amount >= bitWidth)
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
        int numWords = getNumWords(bitWidth, false);
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

    // if the shift amount is too large, we end up with zero anyway
    if (rhs >= bitWidth)
        return SVInt(bitWidth, 0, signFlag);
    return lshr(rhs.as<uint32_t>().value());
}

SVInt SVInt::lshr(uint32_t amount) const {
    // handle trivial cases
    if (amount == 0)
        return *this;
    if (amount >= bitWidth)
        return SVInt(bitWidth, 0, signFlag);
    if (isSingleWord())
        return SVInt(bitWidth, val >> amount, signFlag);

    // handle the small shift case
    SVInt result = allocUninitialized(bitWidth, signFlag, unknownFlag);
    if (amount < BITS_PER_WORD && !unknownFlag)
        lshrNear(result.pVal, pVal, getNumWords(), amount);
    else {
        // otherwise do a full shift
        int numWords = getNumWords(bitWidth, false);
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
    if (rhs >= bitWidth)
        return SVInt(bitWidth, *this >= 0 ? 0 : -1, signFlag);

    return ashr(rhs.as<uint32_t>().value());
}

SVInt SVInt::ashr(uint32_t amount) const {
    if (!signFlag)
        return lshr(amount);
    if (amount == 0)
        return *this;
    if (amount >= bitWidth)
        return SVInt(bitWidth, *this >= 0 ? 0 : -1, signFlag);

    uint32_t contractedWidth = bitWidth - amount;
    SVInt tmp = lshr(amount);

    if (contractedWidth <= 64 && getNumWords() > 1) {
        // signExtend won't be safe as it will assume it is operating on a single-word
        // input when it isn't, so let's manually take care of that case here.
        SVInt result = SVInt::allocUninitialized(bitWidth, signFlag, unknownFlag);
        uint64_t newVal = tmp.pVal[0] << (SVInt::BITS_PER_WORD - contractedWidth);
        result.pVal[0] = (int64_t)newVal >> (SVInt::BITS_PER_WORD - contractedWidth);
        for (size_t i = 1; i < getNumWords(); ++i) {
            // sign extend the rest based on original sign
            result.pVal[i] = val & (1ULL << 63) ? 0 : ~0L;
        }
        result.clearUnusedBits();
        return result;
    }
    // Pretend our width is just the width we shifted to, then signExtend
    tmp.bitWidth = (uint16_t)contractedWidth;
    return signExtend(tmp, bitWidth);
}

SVInt SVInt::replicate(const SVInt& times) const {
    // TODO: optimize to avoid all the copies?
    uint32_t n = times.as<uint32_t>().value();
    SmallVectorSized<SVInt, 8> buffer;
    for (size_t i = 0; i < n; ++i)
        buffer.append(*this);
    return concatenate(span<SVInt const>(buffer.begin(), buffer.end()));
}

SVInt SVInt::bitSelect(int16_t lsb, int16_t msb) const {
    // This would be bad, and there would be no proper size for the output
    ASSERT(msb >= lsb);

    uint16_t selectWidth = msb - lsb + 1;
    // handle indexing out of bounds
    if (msb < 0 || lsb >= bitWidth) {
        // request is completely out of range, return all xs
        return createFillX(selectWidth, false);
    }

    // variables to keep track of out-of-bounds accesses
    uint16_t frontOOB = lsb < 0 ? -lsb : 0;
    uint16_t backOOB = msb >= bitWidth ? msb - bitWidth + 1 : 0;
    bool anyOOB = frontOOB || backOOB;
    uint16_t validSelectWidth = selectWidth - frontOOB - backOOB;

    if (isSingleWord() && !anyOOB) {
        // simplest case; 1 word input, 1 word output, no out of bounds
        uint64_t selection = (val >> lsb) & ((1 << selectWidth) - 1);
        return SVInt(selectWidth, selection, false);
    }

    // core part of the method: copy over the proper number of bits
    int words = getNumWords(selectWidth, unknownFlag || anyOOB);
    uint64_t* newData = new uint64_t[words]();

    copyBits((uint8_t*)newData, frontOOB, (uint8_t*)getRawData(), validSelectWidth, frontOOB ? 0 : lsb);
    bool actualUnknownsInResult = anyOOB;
    if (unknownFlag) {
        // copy over preexisting unknown data
        copyBits((uint8_t*)(newData + words / 2), frontOOB, (uint8_t*)(pVal + getNumWords() / 2), validSelectWidth);
        for (int i = words / 2; i < words; ++i) {
            if (newData[i] != 0) {
                actualUnknownsInResult = true;
                break;
            }
        }
    }

    // back to special case handling
    if (anyOOB) {
        // We have to fill in some x's for out of bounds data
        // a buffer of just xs for us to use copyBits() from
        size_t bufLen = std::max<size_t>(frontOOB, backOOB) / 8 + 1;
        uint8_t* xs = new uint8_t[bufLen];
        memset(xs, 0xFF, bufLen);
        copyBits((uint8_t*)(newData + words / 2), 0, xs, frontOOB);
        copyBits((uint8_t*)(newData + words / 2), validSelectWidth + frontOOB, xs, backOOB);
        free(xs);
    }
    else if (words == 1) {
        // If the output is a single word and everything is valid, we need to return a single-word output
        uint64_t newVal = *newData;
        free(newData);
        return SVInt(selectWidth, newVal, false);
    }

    return SVInt(newData, selectWidth, signFlag, actualUnknownsInResult);
}

size_t SVInt::hash(size_t seed) const {
    return xxhash(getRawData(), getNumWords() * WORD_SIZE, seed);
}

std::ostream& operator<<(std::ostream& os, const SVInt& rhs) {
    os << rhs.toString();
    return os;
}

std::string SVInt::toString() const {
    // guess the base to use
    LiteralBase base;
    if (bitWidth < 8)
        base = LiteralBase::Binary;
    else if (!unknownFlag && (bitWidth == 32 || signFlag))
        base = LiteralBase::Decimal;
    else
        base = LiteralBase::Hex;

    return toString(base);
}

std::string SVInt::toString(LiteralBase base) const {
    SmallVectorSized<char, 32> buffer;
    writeTo(buffer, base);
    return std::string(buffer.begin(), buffer.end());
}

void SVInt::writeTo(SmallVector<char>& buffer, LiteralBase base) const {
    // negative sign if necessary
    SVInt tmp(*this);
    if (signFlag && !unknownFlag && isNegative()) {
        tmp = -tmp;
        buffer.append('-');
    }

    // append the bit size, unless we're a signed 32-bit base 10 integer
    if (base != LiteralBase::Decimal || bitWidth != 32 || !signFlag || unknownFlag) {
        buffer.appendRange(std::to_string(bitWidth));
        buffer.append('\'');
        if (signFlag)
            buffer.append('s');
        switch (base) {
            case LiteralBase::Binary: buffer.append('b'); break;
            case LiteralBase::Octal: buffer.append('o'); break;
            case LiteralBase::Decimal: buffer.append('d'); break;
            case LiteralBase::Hex: buffer.append('h'); break;
        }
    }

    // for bases 2, 8, and 16 we can just shift instead of dividing
    uint32_t startOffset = buffer.size();
    static const char Digits[] = "0123456789abcdef";
    if (base == LiteralBase::Decimal) {
        // decimal numbers that have unknown values only print as a single letter
        if (unknownFlag) {
            if (getRawData()[0])
                buffer.append('z');
            else
                buffer.append('x');
        }
        else {
            // repeatedly divide by 10 to get each digit
            SVInt divisor(4, 10, false);
            while (tmp != 0) {
                SVInt remainder;
                SVInt quotient;
                divide(tmp, tmp.getNumWords(), divisor, divisor.getNumWords(), &quotient, &remainder);
                uint64_t digit = remainder.as<uint64_t>().value();
                ASSERT(digit < 10);
                buffer.append(Digits[digit]);
                tmp = quotient;
            }
        }
    }
    else {
        uint32_t shiftAmount = 0;
        uint32_t maskAmount = 0;
        switch (base) {
            case LiteralBase::Binary: shiftAmount = 1; maskAmount = 1; break;
            case LiteralBase::Octal: shiftAmount = 3; maskAmount = 7; break;
            case LiteralBase::Hex: shiftAmount = 4; maskAmount = 15; break;
        }

        // if we have unknown values here, the comparison will return X
        // we want to keep going so that we print the unknowns
        logic_t x = tmp != 0;
        while (x || x.isUnknown()) {
            uint32_t digit = uint32_t(tmp.getRawData()[0]) & maskAmount;
            if (!tmp.unknownFlag)
                buffer.append(Digits[digit]);
            else {
                uint32_t u = uint32_t(tmp.pVal[getNumWords(bitWidth, false)]) & maskAmount;
                if (!u)
                    buffer.append(Digits[digit]);
                else if (digit)
                    buffer.append('z');
                else
                    buffer.append('x');
            }
            // this shift might shift away the unknown digits, at which point
            // it converts back to being a normal 2-state value
            tmp = tmp.lshr(shiftAmount);
            x = tmp != 0;
        }
    }

    // no digits means this is zero
    if (startOffset == buffer.size())
        buffer.append('0');
    else {
        // reverse the digits
        std::reverse(buffer.begin() + startOffset, buffer.end());
    }
}

SVInt SVInt::pow(const SVInt& rhs) const {
    // ignore unknowns
    bool bothSigned = signFlag && rhs.signFlag;
    if (unknownFlag || rhs.unknownFlag)
        return createFillX(bitWidth, bothSigned);

    // Handle special cases first (note that the result always has
    // the bit width of *this)
    uint32_t lhsBits = getActiveBits();
    uint32_t rhsBits = rhs.getActiveBits();
    if (lhsBits == 0) {
        if (rhsBits == 0)      // 0**0 == 1
            return SVInt(bitWidth, 1, bothSigned);
        if (rhs.signFlag && rhs.isNegative())  // 0**-y == x
            return createFillX(bitWidth, bothSigned);
        // 0**y == 0
        return SVInt(bitWidth, 0, bothSigned);
    }

    // x**0 == 1 || 1**y == 1
    if (rhsBits == 0 || lhsBits == 1)
        return SVInt(bitWidth, 1, bothSigned);

    if (bothSigned && isNegative()) {
        if (*this == SVInt(bitWidth, UINT64_MAX, bothSigned)) {
            // if rhs is odd, result is -1
            // otherwise, result is 1
            if (rhs.isOdd())
                return SVInt(bitWidth, UINT64_MAX, bothSigned);
            else
                return SVInt(bitWidth, 1, bothSigned);
        }
    }

    if (bothSigned && rhs.isNegative()) // x**-y == 0
        return SVInt(bitWidth, 0, bothSigned);

    // we have one of two cases left (rhs is always positive here):
    // 1. lhs > 1 (just do the operation)
    // 2. lhs < -1 (invert, do the op, figure out the sign at the end)
    if (bothSigned && isNegative()) {
        // result is negative if rhs is odd, otherwise positive
        if (rhs.isOdd())
            return -modPow(-(*this), rhs, bothSigned);
        else
            return modPow(-(*this), rhs, bothSigned);
    }
    return modPow(*this, rhs, bothSigned);
}

logic_t SVInt::reductionAnd() const {
    if (unknownFlag)
        return logic_t::x;

    uint64_t mask;
    uint32_t bitsInMsw;
    getTopWordMask(bitsInMsw, mask);

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
    if (unknownFlag)
        return logic_t::x;

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
    uint32_t count = countPopulation();
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
            *this = extend(*this, rhs.bitWidth, signFlag && rhs.signFlag);
        else
            return *this += extend(rhs, bitWidth, signFlag && rhs.signFlag);
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

SVInt& SVInt::operator-=(const SVInt& rhs) {
    if (bitWidth != rhs.bitWidth) {
        if (bitWidth < rhs.bitWidth)
            *this = extend(*this, rhs.bitWidth, signFlag && rhs.signFlag);
        else
            return *this -= extend(rhs, bitWidth, signFlag && rhs.signFlag);
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
            *this = extend(*this, rhs.bitWidth, signFlag && rhs.signFlag);
        else
            return *this *= extend(rhs, bitWidth, signFlag && rhs.signFlag);
    }

    if (unknownFlag || rhs.unknownFlag)
        setAllX();
    else {
        if (isSingleWord())
            val *= rhs.val;
        else {
            // check for zeros
            uint32_t lhsBits = getActiveBits();
            uint32_t lhsWords = !lhsBits ? 0 : whichWord(lhsBits - 1) + 1;
            if (!lhsWords)
                return *this;

            uint32_t rhsBits = rhs.getActiveBits();
            uint32_t rhsWords = !rhsBits ? 0 : whichWord(rhsBits - 1) + 1;
            if (!rhsWords) {
                setAllZeros();
                return *this;
            }

            // allocate result space and do the multiply
            uint32_t destWords = lhsWords + rhsWords;
            uint64_t* dst = new uint64_t[destWords];
            mul(dst, pVal, lhsWords, rhs.pVal, rhsWords);

            // copy the result back into *this
            setAllZeros();
            uint32_t wordsToCopy = destWords >= getNumWords() ? getNumWords() : destWords;
            memcpy(pVal, dst, wordsToCopy * WORD_SIZE);
            delete[] dst;
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
            *this = extend(*this, rhs.bitWidth, bothSigned);
        else
            return *this &= extend(rhs, bitWidth, bothSigned);
    }

    if (isSingleWord())
        val &= rhs.val;
    else {
        uint32_t words = getNumWords(bitWidth, false);
        if (unknownFlag) {
            for (uint32_t i = 0; i < words; i++)
                pVal[i + words] = (pVal[i + words] | rhs.pVal[i + words]) & (pVal[i + words] | pVal[i]) & (rhs.pVal[i + words] | rhs.pVal[i]);

            for (uint32_t i = 0; i < words; i++)
                pVal[i] = ~pVal[i + words] & pVal[i] & rhs.pVal[i];
        }
        else {
            for (uint32_t i = 0; i < words; i++)
                pVal[i] &= rhs.pVal[i];
        }
    }
    clearUnusedBits();
    return *this;
}

SVInt& SVInt::operator|=(const SVInt& rhs) {
    if (bitWidth != rhs.bitWidth) {
        bool bothSigned = signFlag && rhs.signFlag;
        if (bitWidth < rhs.bitWidth)
            *this = extend(*this, rhs.bitWidth, bothSigned);
        else
            return *this |= extend(rhs, bitWidth, bothSigned);
    }

    if (isSingleWord())
        val |= rhs.val;
    else {
        uint32_t words = getNumWords(bitWidth, false);
        if (unknownFlag) {
            for (uint32_t i = 0; i < words; i++)
                pVal[i + words] = (pVal[i + words] & (rhs.pVal[i + words] | ~rhs.pVal[i])) | (~pVal[i] & rhs.pVal[i + words]);

            for (uint32_t i = 0; i < words; i++)
                pVal[i] = ~pVal[i + words] & (pVal[i] | rhs.pVal[i]);
        }
        else {
            for (uint32_t i = 0; i < words; i++)
                pVal[i] |= rhs.pVal[i];
        }
    }
    clearUnusedBits();
    return *this;
}

SVInt& SVInt::operator^=(const SVInt& rhs) {
    if (bitWidth != rhs.bitWidth) {
        bool bothSigned = signFlag && rhs.signFlag;
        if (bitWidth < rhs.bitWidth)
            *this = extend(*this, rhs.bitWidth, bothSigned);
        else
            return *this ^= extend(rhs, bitWidth, bothSigned);
    }

    if (isSingleWord())
        val ^= rhs.val;
    else {
        uint32_t words = getNumWords(bitWidth, false);
        if (unknownFlag) {
            for (uint32_t i = 0; i < words; i++)
                pVal[i + words] |= rhs.pVal[i + words];

            for (uint32_t i = 0; i < words; i++)
                pVal[i] = ~pVal[i + words] & (pVal[i] ^ rhs.pVal[i]);
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
            return extend(*this, rhs.bitWidth, bothSigned).xnor(rhs);
        else
            return xnor(extend(rhs, bitWidth, bothSigned));
    }

    SVInt result(*this);
    if (isSingleWord())
        result.val = ~(result.val ^ rhs.val);
    else {
        uint32_t words = getNumWords(bitWidth, false);
        if (unknownFlag) {
            for (uint32_t i = 0; i < words; i++)
                result.pVal[i + words] |= rhs.pVal[i + words];

            for (uint32_t i = 0; i < words; i++)
                result.pVal[i] = ~result.pVal[i + words] & ~(result.pVal[i] ^ rhs.pVal[i]);
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
            return extend(*this, rhs.bitWidth, bothSigned) / rhs;
        else
            return *this / extend(rhs, bitWidth, bothSigned);
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
    return udiv(*this, rhs, false);
}

SVInt SVInt::operator%(const SVInt& rhs) const {
    bool bothSigned = signFlag && rhs.signFlag;
    if (bitWidth != rhs.bitWidth) {
        if (bitWidth < rhs.bitWidth)
            return extend(*this, rhs.bitWidth, bothSigned) % rhs;
        else
            return *this % extend(rhs, bitWidth, bothSigned);
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

    bool bothSigned = signFlag & rhs.signFlag;
    if (bitWidth != rhs.bitWidth) {
        if (bitWidth < rhs.bitWidth)
            return extend(*this, rhs.bitWidth, bothSigned) < rhs;
        else
            return *this < extend(rhs, bitWidth, bothSigned);
    }

    if (bothSigned) {
        // handle negatives
        if (isNegative()) {
            if (rhs.isNegative())
                return -(*this) > -rhs;
            else
                return logic_t(true);
        }
        if (rhs.isNegative())
            return logic_t(false);
    }

    if (isSingleWord())
        return logic_t(val < rhs.val);

    uint32_t a1 = getActiveBits();
    uint32_t a2 = rhs.getActiveBits();
    if (a1 < a2)
        return logic_t(true);
    if (a2 < a1)
        return logic_t(false);

    // same number of words, compare each one until there's no match
    uint32_t top = whichWord(a1 - 1);
    for (int i = top; i >= 0; i--) {
        if (pVal[i] > rhs.pVal[i])
            return logic_t(false);
        if (pVal[i] < rhs.pVal[i])
            return logic_t(true);
    }
    return logic_t(false);
}

logic_t SVInt::operator[](uint32_t index) const {
    bool bit = (maskBit(index) & (isSingleWord() ? val : pVal[whichWord(index)])) != 0;
    if (!unknownFlag)
        return logic_t(bit);

    bool unknownBit = (maskBit(index) & pVal[whichWord(index) + getNumWords(bitWidth, false)]) != 0;
    if (!unknownBit)
        return logic_t(bit);

    return bit ? logic_t::z : logic_t::x;
}

SVInt SVInt::operator()(const SVInt& msb, const SVInt& lsb) const {
    // TODO:
    return (*this)((uint16_t)msb.as<uint64_t>().value(), (uint16_t)lsb.as<uint64_t>().value());
}

SVInt SVInt::operator()(uint16_t msb, uint16_t lsb) const {
    if (lsb != 0)
        return lshr(lsb)(msb - lsb, 0);

    // lsb is always zero from here on out
    SVInt result(msb + 1, 0, false);
    if (result.isSingleWord())
        result.val = getRawData()[0];
    else {
        for (uint32_t i = 0; i < result.getNumWords(); i++)
            result.pVal[i] = pVal[i];
    }
    result.clearUnusedBits();
    return result;
}

SVInt SVInt::conditional(const SVInt& condition, const SVInt& lhs, const SVInt& rhs) {
    bool bothSigned = lhs.signFlag && rhs.signFlag;
    if (lhs.bitWidth != rhs.bitWidth) {
        if (lhs.bitWidth < rhs.bitWidth)
            return conditional(condition, extend(lhs, rhs.bitWidth, bothSigned), rhs);
        else
            return conditional(condition, lhs, extend(rhs, lhs.bitWidth, bothSigned));
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
                                 (rhs.unknownFlag ? rp[i + words] : 0) | 
                                 (lp[i] ^ rp[i]);
        result.pVal[i] = ~result.pVal[i + words] & lp[i] & rp[i];
    }

    result.clearUnusedBits();
    return result;
}

SVInt SVInt::allocUninitialized(uint16_t bits, bool signFlag, bool unknownFlag) {
    return SVInt(new uint64_t[getNumWords(bits, unknownFlag)], bits, signFlag, unknownFlag);
}

SVInt SVInt::allocZeroed(uint16_t bits, bool signFlag, bool unknownFlag) {
    return SVInt(new uint64_t[getNumWords(bits, unknownFlag)](), bits, signFlag, unknownFlag);
}

void SVInt::initSlowCase(logic_t bit) {
    pVal = new uint64_t[getNumWords()]();   // allocation is zero cleared
    pVal[1] = 1;
    if (bit == logic_t::z)
        pVal[0] = 1;
}

void SVInt::initSlowCase(uint64_t value) {
    uint32_t words = getNumWords();
    pVal = new uint64_t[words]();   // allocation is zero cleared
    pVal[0] = value;

    // sign extend if necessary
    if (signFlag && int64_t(value) < 0) {
        for (uint32_t i = 1; i < words; i++)
            pVal[i] = (uint64_t)(-1);
    }
}

void SVInt::initSlowCase(const SVInt& other) {
    uint32_t words = getNumWords();
    pVal = new uint64_t[words];
    std::copy(other.pVal, other.pVal + words, pVal);
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
    if (unknownFlag || rhs.unknownFlag)
        return logic_t::x;

    // handle unequal bit widths; spec says that if both values are signed, then do sign extension
    const uint64_t* lval = pVal;
    const uint64_t* rval = rhs.pVal;

    if (bitWidth != rhs.bitWidth) {
        if (signFlag && rhs.signFlag) {
            if (bitWidth < rhs.bitWidth)
                return signExtend(*this, rhs.bitWidth).equalsSlowCase(rhs);
            else
                return signExtend(rhs, bitWidth).equalsSlowCase(*this);
        }

        if (isSingleWord())
            lval = &val;
        if (rhs.isSingleWord())
            rval = &rhs.val;
    }

    uint32_t a1 = getActiveBits();
    uint32_t a2 = rhs.getActiveBits();
    if (a1 != a2)
        return logic_t(false);

    // compare each word
    int limit = whichWord(a1 - 1);
    for (int i = 0; i <= limit; i++) {
        if (lval[i] != rval[i])
            return logic_t(false);
    }

    return logic_t(true);
}

void SVInt::getTopWordMask(uint32_t& bitsInMsw, uint64_t& mask) const {
    bitsInMsw = bitWidth % BITS_PER_WORD;
    if (bitsInMsw)
        mask = (1ull << bitsInMsw) - 1;
    else {
        mask = UINT64_MAX;
        bitsInMsw = BITS_PER_WORD;
    }
}

uint32_t SVInt::countLeadingZerosSlowCase() const {
    // Most significant word might have extra bits that shouldn't count
    uint64_t mask;
    uint32_t bitsInMsw;
    getTopWordMask(bitsInMsw, mask);

    uint32_t i = getNumWords();
    uint64_t part = pVal[i - 1] & mask;
    if (part)
        return slang::countLeadingZeros(part) - (BITS_PER_WORD - bitsInMsw);

    int count = bitsInMsw;
    for (--i; i > 0; --i) {
        if (pVal[i - 1] == 0)
            count += BITS_PER_WORD;
        else {
            count += slang::countLeadingZeros(pVal[i - 1]);
            break;
        }
    }
    return count;
}

uint32_t SVInt::countLeadingOnesSlowCase() const {
    uint32_t bitsInMsw = bitWidth % BITS_PER_WORD;
    uint32_t shift = 0;
    if (!bitsInMsw)
        bitsInMsw = BITS_PER_WORD;
    else
        shift = BITS_PER_WORD - bitsInMsw;

    int i = getNumWords() - 1;
    uint32_t count = slang::countLeadingOnes(pVal[i] << shift);
    if (count == bitsInMsw) {
        for (i--; i >= 0; i--) {
            if (pVal[i] == (uint64_t)-1)
                count += BITS_PER_WORD;
            else {
                count += slang::countLeadingOnes(pVal[i]);
                break;
            }
        }
    }

    return count;
}

uint32_t SVInt::countPopulation() const {
    // don't worry about unknowns in this function; only use it if the number is all known
    if (isSingleWord())
        return slang::countPopulation(val);

    uint32_t count = 0;
    for (uint32_t i = 0; i < getNumWords(); i++)
        count += slang::countPopulation(pVal[i]);
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

SVInt SVInt::createFillX(uint16_t bitWidth, bool isSigned) {
    SVInt result(new uint64_t[getNumWords(bitWidth, true)], bitWidth, isSigned, true);
    result.setAllX();
    return result;
}

SVInt SVInt::createFillZ(uint16_t bitWidth, bool isSigned) {
    SVInt result(new uint64_t[getNumWords(bitWidth, true)], bitWidth, isSigned, true);
    result.setAllZ();
    return result;
}

void SVInt::splitWords(const SVInt& value, uint32_t* dest, uint32_t numWords) {
    const uint64_t mask = ~0ull >> sizeof(uint32_t) * CHAR_BIT;
    for (uint32_t i = 0; i < numWords; i++) {
        uint64_t val = value.getNumWords() == 1 ? value.val : value.pVal[i];
        dest[i * 2] = uint32_t(val & mask);
        dest[i * 2 + 1] = uint32_t(val >> (sizeof(uint32_t) * CHAR_BIT));
    }
}

void SVInt::buildDivideResult(SVInt* result, uint32_t* value, uint16_t bitWidth, bool signFlag, uint32_t numWords) {
    if (!result)
        return;

    if (numWords == 1) {
        uint64_t val = uint64_t(value[0]) | (uint64_t(value[1]) << (BITS_PER_WORD / 2));
        *result = SVInt(bitWidth, val, signFlag);
    }
    else {
        *result = SVInt(bitWidth, 0, signFlag);
        for (uint32_t i = 0; i < numWords; i++)
            result->pVal[i] = uint64_t(value[i * 2]) | (uint64_t(value[i * 2 + 1]) << (BITS_PER_WORD / 2));
    }
}

void SVInt::divide(const SVInt& lhs, uint32_t lhsWords, const SVInt& rhs, uint32_t rhsWords,
    SVInt* quotient, SVInt* remainder)
{
    ASSERT(lhsWords >= rhsWords, "Fractional result");

    // The Knuth algorithm requires arrays of 32-bit words (because results of operations
    // need to fit natively into 64 bits). Allocate space for the backing memory, either on
    // the stack if it's small or on the heap if it's not.
    uint32_t divisorWords = rhsWords * 2;
    uint32_t extraWords = (lhsWords * 2) - divisorWords;
    uint32_t dividendWords = divisorWords + extraWords;

    uint32_t scratch[128];
    uint32_t* u = nullptr;
    uint32_t* v = nullptr;
    uint32_t* q = nullptr;
    uint32_t* r = nullptr;
    if ((remainder ? 4 : 3) * divisorWords + 2 * extraWords + 1 <= 128) {
        u = scratch;
        v = u + dividendWords + 1;
        q = v + divisorWords;
        if (remainder)
            r = q + dividendWords;
    }
    else {
        u = new uint32_t[dividendWords + 1];
        v = new uint32_t[divisorWords];
        q = new uint32_t[dividendWords];
        if (remainder)
            r = new uint32_t[divisorWords];
    }

    // Initialize the dividend and divisor
    splitWords(lhs, u, lhsWords);
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
        for (int i = dividendWords - 1; i >= 0; i--) {
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

    // cleanup
    if (u != scratch) {
        delete[] u;
        delete[] v;
        delete[] q;
        delete[] r;
    }
}

SVInt SVInt::udiv(const SVInt& lhs, const SVInt& rhs, bool bothSigned) {
    // At this point we have two values with the same bit widths, both positive,
    // and X's have been dealt with. Also, we know rhs isn't zero.
    if (lhs.isSingleWord())
        return SVInt(lhs.bitWidth, lhs.val / rhs.val, bothSigned);

    uint32_t lhsBits = lhs.getActiveBits();
    uint32_t lhsWords = !lhsBits ? 0 : (whichWord(lhsBits - 1) + 1);
    uint32_t rhsBits = rhs.getActiveBits();
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

    uint32_t lhsBits = lhs.getActiveBits();
    uint32_t lhsWords = !lhsBits ? 0 : (whichWord(lhsBits - 1) + 1);
    uint32_t rhsBits = rhs.getActiveBits();
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
    // Allocate a temporary result value that has 2x the number of bits so that we can
    // handle any possible intermediate multiply.
    uint16_t bitWidth = base.bitWidth;
    ASSERT(UINT16_MAX - bitWidth > bitWidth);
    SVInt value(bitWidth * 2, 1, false);
    SVInt baseCopy = zeroExtend(base, bitWidth * 2);

    // Because the mod in this case is always a power of two, set up a mask
    // that we'll AND with instead of the more costly remainder operation.
    SVInt mask(bitWidth, 0, false);
    mask.setAllOnes();
    mask = zeroExtend(mask, bitWidth * 2);

    // Loop through each bit of the exponent.
    uint32_t exponentWords = exponent.getNumWords();
    for (uint32_t i = 0; i < exponentWords - 1; i++) {
        uint64_t word = exponent.getRawData()[i];
        for (int j = 0; j < BITS_PER_WORD; j++) {
            if (word & 0x1) {
                value *= baseCopy;
                value &= mask;
            }
            baseCopy *= baseCopy;
            baseCopy &= mask;
            word >>= 1;
        }
    }

    // Unroll the last loop iteration to avoid multiplications
    // when the rest of the exponent bits are zero
    uint64_t word = exponent.getRawData()[exponentWords - 1];
    while (word) {
        if (word & 0x1) {
            value *= baseCopy;
            value &= mask;
        }
        if (word != 1) {
            baseCopy *= baseCopy;
            baseCopy &= mask;
        }
        word >>= 1;
    }

    // Truncate the result down to fit into the final bit width; we know
    // since we've been reducing at each step that none of the truncated
    // bits will be significant.
    SVInt result = value(bitWidth - 1, 0);
    result.setSigned(bothSigned);
    return result;
}

SVInt signExtend(const SVInt& value, uint16_t bits) {
    ASSERT(bits > value.bitWidth);

    if (bits <= SVInt::BITS_PER_WORD && !value.unknownFlag) {
        uint64_t newVal = value.val << (SVInt::BITS_PER_WORD - value.bitWidth);
        newVal = (int64_t)newVal >> (bits - value.bitWidth);
        return SVInt(bits, newVal >> (SVInt::BITS_PER_WORD - bits), value.signFlag);
    }

    // copy and sign extend; for unknown values, this copies the data words
    // but not the unknown-indicator words, which we do separately below
    SVInt result(new uint64_t[SVInt::getNumWords(bits, value.unknownFlag)], bits, value.signFlag, value.unknownFlag);
    signExtendCopy(result.pVal, value.getRawData(), value.bitWidth, bits);

    if (value.unknownFlag) {
        signExtendCopy(
            result.pVal + SVInt::getNumWords(bits, false),
            value.pVal + SVInt::getNumWords(value.bitWidth, false),
            value.bitWidth,
            bits
        );
    }

    return result;
}

SVInt zeroExtend(const SVInt& value, uint16_t bits) {
    ASSERT(bits > value.bitWidth);

    if (bits <= SVInt::BITS_PER_WORD && !value.unknownFlag)
        return SVInt(bits, value.val, value.signFlag);

    SVInt result(new uint64_t[SVInt::getNumWords(bits, value.unknownFlag)](), bits, value.signFlag, value.unknownFlag);

    uint32_t valueWords = SVInt::getNumWords(value.bitWidth, false);
    for (uint32_t i = 0; i < valueWords; i++)
        result.pVal[i] = value.getRawData()[i];

    if (value.unknownFlag) {
        uint32_t newWords = SVInt::getNumWords(bits, false);
        for (uint32_t i = 0; i < valueWords; i++)
            result.pVal[i + newWords] = value.getRawData()[i + valueWords];
    }

    return result;
}

SVInt extend(const SVInt& value, uint16_t bits, bool sign) {
    return sign ? signExtend(value, bits) : zeroExtend(value, bits);
}

bool exactlyEqual(const SVInt& lhs, const SVInt &rhs) {
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
            return exactlyEqual(extend(lhs, rhs.bitWidth, bothSigned), rhs);
        else
            return exactlyEqual(lhs, extend(rhs, lhs.bitWidth, bothSigned));
    }

    // ok, equal widths, and they both have unknown values, do a straight memory compare
    return memcmp(lhs.pVal, rhs.pVal, lhs.getNumWords() * SVInt::WORD_SIZE) == 0;
}

logic_t wildcardEqual(const SVInt& lhs, const SVInt& rhs) {
    // if no unknown flags, do normal comparison
    if (!lhs.unknownFlag && !rhs.unknownFlag)
        return lhs == rhs;

    // if the lhs has any unknown flags, then return 'x'
    if (lhs.unknownFlag) {
        return logic_t::x;
    }

    // handle sign extension if necessary
    if (lhs.bitWidth != rhs.bitWidth) {
        bool bothSigned = lhs.signFlag && rhs.signFlag;
        if (lhs.bitWidth < rhs.bitWidth)
            return wildcardEqual(extend(lhs, rhs.bitWidth, bothSigned), rhs);
        else
            return wildcardEqual(lhs, extend(rhs, lhs.bitWidth, bothSigned));
    }

    size_t words = lhs.getNumWords();
    // Do word-for-word wildcard comparison, being careful that one argument
    // might not
    for (size_t i = 0; i < words; ++i) {
        // bitmask to avoid comparing the bits unknown on the rhs
        uint64_t mask = ~rhs.pVal[i + words];
        // getRawData handles the case where lhs is a single word
        if ((lhs.getRawData()[i] & mask) != (rhs.pVal[i] & mask))
            return logic_t(false);
    }
    return logic_t(true);
}

SVInt concatenate(span<SVInt const> operands) {
    // 0 operand concatenations can be valid inside of larger concatenations
    if (operands.size() == 0) {
        return SVInt(0, 0, false);
    }

    // First, compute how many bits total we are dealing with
    uint16_t bits = 0;
    bool unknownFlag = false;

    for (const auto& op : operands) {
        bits += op.bitWidth;
        unknownFlag |= op.unknownFlag;
    }

    // words is the count of not unknown words
    int words = SVInt::getNumWords(bits, unknownFlag);
    if (words == 1) {
        // The concatenation still fits into a single word
        uint16_t offset = 0;
        uint64_t val = 0;
        // The first operand wriets the msb, therefore, we must operate in reverse
        for (auto it = operands.rbegin(); it != operands.rend(); it++) {
            copyBits((uint8_t*)&val, offset, (uint8_t*)&it->val, it->bitWidth);
            offset += it->bitWidth;
        }
        return SVInt(bits, val, false);
    }
    // data is already zeroed out, which is the proper default, so it doesn't
    // matter that we may not write to certain unknown words or might not
    // write all the way to the end
    uint64_t *data = new uint64_t[words]();

    // offset (in bits) to which we are writing
    uint16_t offset = 0;
    for (auto it = operands.rbegin(); it != operands.rend(); it++) {
        copyBits((uint8_t*)data, offset, (uint8_t*)it->getRawData(), it->bitWidth);
        if (it->unknownFlag) {
            copyBits((uint8_t*)(data + words / 2), offset,
                     (uint8_t*)(it->pVal + it->getNumWords() / 2), it->bitWidth);
        }
        offset += it->bitWidth;
    }
    return SVInt(data, bits, false, unknownFlag);
}

}
