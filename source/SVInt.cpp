//------------------------------------------------------------------------------
// SVInt.cpp
// Arbitrary precision integer support.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "SVInt.h"

#include <algorithm>

namespace slang {

#include "SVIntHelpers.h"

const logic_t logic_t::x = 1 << 7;
const logic_t logic_t::z = 1 << 6;

void SVInt::setAllZeros() {
    if (isSingleWord())
        val = 0;
    else if (unknownFlag)
        *this = SVInt(bitWidth, 0, signFlag);
    else
        memset(pVal, 0, getNumWords() * WORD_SIZE);
}

void SVInt::setAllOnes() {
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
}

void SVInt::setAllZ() {
    if (!unknownFlag) {
        if (!isSingleWord())
            delete[] pVal;

        unknownFlag = true;
        pVal = new uint64_t[getNumWords()];
    }

    for (uint32_t i = 0; i < getNumWords(); i++)
        pVal[i] = UINT64_MAX;
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

        lshrFar(newVal, pVal, wordShift, offset, 0, numWords);
        if (unknownFlag)
            lshrFar(newVal, pVal, wordShift, offset, numWords, numWords);
    }
    return SVInt(newVal, bitWidth, signFlag, unknownFlag);
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
        // TODO:
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

SVInt SVInt::operator+(const SVInt& rhs) const {
    SVInt tmp(*this);
    tmp += rhs;
    return tmp;
}

SVInt SVInt::operator-(const SVInt& rhs) const {
    SVInt tmp(*this);
    tmp += rhs;
    return tmp;
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

SVInt SVInt::createFillX(uint16_t bitWidth, bool isSigned) {
    SVInt result(new uint64_t[getNumWords(bitWidth, true)], bitWidth, isSigned, true);
    result.setAllX();
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

void SVInt::buildDivideResult(SVInt* result, uint32_t* value, uint32_t numWords) {
    if (!result)
        return;

    // TODO!
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

    buildDivideResult(quotient, q, lhsWords);
    buildDivideResult(remainder, r, rhsWords);

    // cleanup
    if (u != scratch) {
        delete[] u;
        delete[] v;
        delete[] q;
        delete[] r;
    }
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
    for (uint32_t i = 0; i < value.getNumWords(); i++)
        result.pVal[i] = value.getRawData()[i];

    return result;
}

SVInt extend(const SVInt& value, uint16_t bits, bool sign) {
    return sign ? signExtend(value, bits) : zeroExtend(value, bits);
}

}