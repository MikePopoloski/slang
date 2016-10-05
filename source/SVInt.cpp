//------------------------------------------------------------------------------
// SVInt.cpp
// Arbitrary precision integer support.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "SVInt.h"

namespace slang {

const logic_t logic_t::x = 1 << 7;
const logic_t logic_t::z = 1 << 6;

static void lshrNear(uint64_t* dst, uint64_t* src, int words, int amount) {
    // fast case for logical right shift of a small amount (less than 64 bits)
    uint64_t carry = 0;
    for (int i = words - 1; i >= 0; i--) {
        uint64_t temp = src[i];
        dst[i] = (temp >> amount) | carry;
        carry = temp << (64 - amount);
    }
}

SVInt SVInt::lshr(uint32_t amount) const {
    if (amount == 0 || amount >= bitWidth)
        return SVInt(bitWidth, 0, signFlag);

    if (isSingleWord())
        return SVInt(bitWidth, val >> amount, signFlag);

    uint64_t* newVal = new uint64_t[getNumWords()]();
    if (amount < BITS_PER_WORD && !unknownFlag)
        lshrNear(newVal, pVal, getNumWords(), amount);
    else {
        int numWords = getNumWords(bitWidth, false);
        uint32_t wordShift = amount % BITS_PER_WORD;
        uint32_t offset = amount / BITS_PER_WORD;

        // optimization: move whole words
        if (wordShift == 0) {
            for (uint32_t i = 0; i < numWords - offset; i++)
                newVal[i] = pVal[i + offset];

            if (unknownFlag) {
                for (uint32_t i = numWords; i < numWords + numWords - offset; i++)
                    newVal[i] = pVal[i + offset];
            }
        }
        else {
            // shift low order words
            uint32_t breakWord = numWords - offset - 1;
            for (uint32_t i = 0; i < breakWord; i++)
                newVal[i] = (pVal[i + offset] >> wordShift) | (pVal[i + offset + 1] << (BITS_PER_WORD - wordShift));

            newVal[breakWord] = pVal[breakWord + offset] >> wordShift;
        }
    }
    return SVInt(newVal, bitWidth, signFlag, unknownFlag);
}

SVInt SVInt::signExtend(uint16_t bits) const {
    ASSERT(bits > bitWidth);

    if (bits <= BITS_PER_WORD && !unknownFlag) {
        uint64_t newVal = val << (BITS_PER_WORD - bitWidth);
        newVal = (int64_t)newVal >> (bits - bitWidth);
        return SVInt(bits, newVal >> (BITS_PER_WORD - bits), signFlag);
    }

    // copy and sign extend; for unknown values, this copies the data words
    // but not the unknown-indicator words, which we do separate below
    SVInt result(new uint64_t[getNumWords(bits, unknownFlag)], bits, signFlag, unknownFlag);
    signExtendCopy(result.pVal, getRawData(), bitWidth, bits);

    if (unknownFlag)
        signExtendCopy(result.pVal + getNumWords(bits, false), pVal + getNumWords(bitWidth, false), bitWidth, bits);
    
    return result;
}

void SVInt::signExtendCopy(uint64_t* output, const uint64_t* input, uint16_t oldBits, uint16_t newBits) {
    // copy full words over
    int i;
    uint64_t word = 0;
    for (i = 0; i != oldBits / BITS_PER_WORD; i++) {
        word = input[i];
        output[i] = word;
    }

    // sign-extend the last word
    uint32_t last = (-oldBits) % BITS_PER_WORD;
    if (last != 0)
        word = (int64_t)input[i] << last >> last;
    else
        word = (int64_t)word >> (BITS_PER_WORD - 1);

    // fill remaining words
    for (; i != newBits / BITS_PER_WORD; i++) {
        output[i] = word;
        word = (int64_t)word >> (BITS_PER_WORD - 1);
    }

    // write remaining partial word
    last = (-newBits) % BITS_PER_WORD;
    if (last != 0)
        output[i] = word << last >> last;
}

std::string SVInt::toString(LiteralBase base) const {
    Buffer<char> buffer(16);
    writeTo(buffer, base);
    return std::string(buffer.begin(), buffer.end());
}

void SVInt::writeTo(Buffer<char>& buffer, LiteralBase base) const {
    // negative sign if necessary
    if (isNegative() && signFlag)
        buffer.append('-');

    // append the bit size, unless we're a signed 32-bit base 10 integer
    if (base != LiteralBase::Decimal || bitWidth != 32 || signFlag || unknownFlag) {
        buffer.appendRange(std::to_string(bitWidth));
        buffer.append('\'');
        if (signFlag)
            buffer.append('s');
        switch (base) {
            case LiteralBase::Binary: buffer.append('b'); break;
            case LiteralBase::Octal: buffer.append('o'); break;
            case LiteralBase::Decimal: buffer.append('d'); break;
            case LiteralBase::Hex: buffer.append('h'); break;
            default: ASSERT(false, "Unknown base"); break;
        }
    }

    SVInt tmp(*this);
    if (signFlag && isNegative()) {
        // TODO:
    }

    // for bases 2, 8, and 16 we can just shift instead of dividing
    uint32_t startOffset = buffer.count();
    static const char Digits[] = "0123456789ABCDEF";
    if (base == LiteralBase::Decimal) {
    }
    else {
        uint32_t shiftAmount = 0;
        uint32_t maskAmount = 0;
        switch (base) {
            case LiteralBase::Binary: shiftAmount = 1; maskAmount = 1; break;
            case LiteralBase::Octal: shiftAmount = 3; maskAmount = 7; break;
            case LiteralBase::Hex: shiftAmount = 4; maskAmount = 15; break;
            default: ASSERT(false, "Impossible"); break;
        }

        while (tmp != 0) {
            uint32_t digit = uint32_t(tmp.getRawData()[0]) & maskAmount;
            buffer.append(Digits[digit]);
            tmp = tmp.lshr(shiftAmount);
        }
    }

    // reverse the digits
    std::reverse(buffer.begin() + startOffset, buffer.end());
}

logic_t SVInt::operator[](uint32_t index) const {
    bool bit = (maskBit(index) & (isSingleWord() ? val : pVal[whichWord(index)])) != 0;
    if (!unknownFlag)
        return bit;

    bool unknownBit = (maskBit(index) & pVal[whichWord(index) + getNumWords(bitWidth, false)]) != 0;
    if (!unknownBit)
        return bit;

    return bit ? logic_t::z : logic_t::x;
}

void SVInt::initSlowCase(logic_t bit) {
    uint32_t words = getNumWords();
    pVal = new uint64_t[words]();   // allocation is zero cleared
    setUnknownBit(0, bit);
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
                return signExtend(rhs.bitWidth).equalsSlowCase(rhs);
            else
                return rhs.signExtend(bitWidth).equalsSlowCase(*this);
        }

        if (isSingleWord())
            lval = &val;
        if (rhs.isSingleWord())
            rval = &rhs.val;
    }

    uint32_t a1 = getActiveBits();
    uint32_t a2 = rhs.getActiveBits();
    if (a1 != a2)
        return false;

    // compare each word
    int limit = whichWord(a1 - 1);
    for (int i = 0; i <= limit; i++) {
        if (lval[i] != rval[i])
            return false;
    }

    return true;
}

uint32_t SVInt::countLeadingZerosSlowCase() const {
    int count = 0;
    for (int i = getNumWords() - 1; i >= 0; i--) {
        if (pVal[i] == 0)
            count += BITS_PER_WORD;
        else {
            count += slang::countLeadingZeros(pVal[i]);
            break;
        }
    }
    return count;
}

void SVInt::setUnknownBit(int index, logic_t bit) {
    // the encoding is:
    //   - If the bit is known, the trailing array word has a 0 bit set.
    //   - If the bit is unknown, the trailing array word has a 1 bit set at the right index.
    //     The primary word has a 0 or 1 to mean X or Z, respectively.
    ASSERT(unknownFlag);
    switch (bit.value) {
        case 0:
            pVal[whichWord(index)] &= ~maskBit(index);
            pVal[whichUnknownWord(index)] &= ~maskBit(index);
            break;
        case 1:
            pVal[whichWord(index)] |= maskBit(index);
            pVal[whichUnknownWord(index)] &= ~maskBit(index);
            break;
        case 1 << 7: // TODO
            pVal[whichWord(index)] &= ~maskBit(index);
            pVal[whichUnknownWord(index)] |= maskBit(index);
            break;
        case 1 << 6: // TODO
            pVal[whichWord(index)] |= maskBit(index);
            pVal[whichUnknownWord(index)] |= maskBit(index);
            break;
        default:
            ASSERT(false, "Bad bit value");
            break;
    }
}

void SVInt::clearUnusedBits() {
    // TODO: don't clear sign extension
    // clear out unused bits in the top word after we've assigned something to it
    uint32_t wordBits = bitWidth % BITS_PER_WORD;
    if (wordBits == 0)
        return;

    uint64_t mask = ~uint64_t(0ULL) >> (BITS_PER_WORD - wordBits);
    if (isSingleWord())
        val &= mask;
    else
        pVal[getNumWords() - 1] &= mask;
}

}