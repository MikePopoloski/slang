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
    // TODO: impl
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