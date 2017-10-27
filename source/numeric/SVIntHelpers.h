//------------------------------------------------------------------------------
// SVIntHelpers.h
// Contains internal helper functions for SVInt implementations.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

static void lshrNear(uint64_t* dst, uint64_t* src, int words, int amount) {
    // fast case for logical right shift of a small amount (less than 64 bits)
    uint64_t carry = 0;
    for (int i = words - 1; i >= 0; i--) {
        uint64_t temp = src[i];
        dst[i] = (temp >> amount) | carry;
        carry = temp << (64 - amount);
    }
}

static void lshrFar(uint64_t* dst, uint64_t* src, uint32_t wordShift, uint32_t offset, uint32_t start, int numWords) {
    // this function is split out so that if we have an unknown value we can reuse the code
    // optimization: move whole words
    if (wordShift == 0) {
        for (uint32_t i = start; i < start + numWords - offset; i++)
            dst[i] = src[i + offset];
    }
    else {
        // shift low order words
        uint32_t breakWord = start + numWords - offset - 1;
        for (uint32_t i = start; i < breakWord; i++)
            dst[i] = (src[i + offset] >> wordShift) | (src[i + offset + 1] << (SVInt::BITS_PER_WORD - wordShift));

        // shift the "break" word
        dst[breakWord] = src[breakWord + offset] >> wordShift;
    }
}

static void shlFar(uint64_t* dst, uint64_t* src, uint32_t wordShift, uint32_t offset, uint32_t start, int numWords) {
    // this function is split out so that if we have an unknown value we can reuse the code
    for (uint32_t i = start; i < start + offset; i++)
        dst[i] = 0;

    // optimization: move whole words
    if (wordShift == 0) {
        for (uint32_t i = start + offset; i < start + numWords; i++)
            dst[i] = src[i - offset];
    }
    else {
        for (uint32_t i = start + numWords - 1; i > start + offset; i--)
            dst[i] = src[i - offset] << wordShift | src[i - offset - 1] >> (SVInt::BITS_PER_WORD - wordShift);
        dst[start + offset] = src[start] << wordShift;
    }
}

static void signExtendCopy(uint64_t* output, const uint64_t* input, uint16_t oldBits,
                           int oldWords, int newWords) {
    // copy full words over
    memcpy(output, input, sizeof(uint64_t) * oldWords);

    // sign-extend the last word
    int lastWordBits = SVInt::BITS_PER_WORD - (((oldBits - 1) % SVInt::BITS_PER_WORD) + 1);
    output[oldWords - 1] = int64_t(output[oldWords - 1] << lastWordBits) >> lastWordBits;

    // fill the remaining words with the sign bit
    int isNegative = output[oldWords - 1] >> (SVInt::BITS_PER_WORD - 1);
    memset(output + oldWords, isNegative ? -1 : 0, (newWords - oldWords) * sizeof(uint64_t));
}

// Specialized adder for values <= 64.
static bool addOne(uint64_t* dst, uint64_t* src, int len, uint64_t value) {
    for (int i = 0; i < len; i++) {
        dst[i] = value + src[i];
        if (dst[i] < value)
            value = 1;  // carry
        else {
            value = 0;
            break;
        }
    }
    return value != 0;
}

// Specialized subtractor for values <= 64.
static bool subOne(uint64_t* dst, uint64_t* src, int len, uint64_t value) {
    for (int i = 0; i < len; i++) {
        uint64_t x = src[i];
        dst[i] -= value;
        if (value > x)
            value = 1;  // borrow
        else {
            value = 0;
            break;
        }
    }
    return value != 0;
}

// Generalized adder
NO_SANITIZE("unsigned-integer-overflow")
static bool addGeneral(uint64_t* dst, uint64_t* x, uint64_t* y, int len) {
    bool carry = false;
    for (int i = 0; i < len; i++) {
        uint64_t limit = std::min(x[i], y[i]);
        dst[i] = x[i] + y[i] + carry;
        carry = dst[i] < limit || (carry && dst[i] == limit);
    }
    return carry;
}

// Generalized subtractor (x - y)
NO_SANITIZE("unsigned-integer-overflow")
static bool subGeneral(uint64_t* dst, uint64_t* x, uint64_t* y, int len) {
    bool borrow = false;
    for (int i = 0; i < len; i++) {
        uint64_t tmp = borrow ? x[i] - 1 : x[i];
        borrow = y[i] > tmp || (borrow && x[i] == 0);
        dst[i] = tmp - y[i];
    }
    return borrow;
}

// One term of a multiply operation
NO_SANITIZE("unsigned-integer-overflow")
static uint64_t mulTerm(uint64_t x, uint64_t ly, uint64_t hy, uint64_t& carry) {
    uint64_t lx = x & 0xffffffffULL;
    uint64_t hx = x >> 32;
    uint64_t result = carry + lx * ly;

    // hasCarry:
    // - if 0, no carry
    // - if 1, has carry
    // - if 2, no carry and result is 0
    int hasCarry = 0;
    hasCarry = (result < carry) ? 1 : 0;
    carry = (hasCarry ? (1ULL << 32) : 0) + hx * ly + (result >> 32);
    hasCarry = (!carry && hasCarry) ? 1 : (!carry ? 2 : 0);

    carry += (lx * hy) & 0xffffffffULL;
    result = (carry << 32) | (result & 0xffffffffULL);

    uint64_t bias = 0;
    if ((!carry && hasCarry != 2) || hasCarry == 1)
        bias = 1ULL << 32;

    carry = bias + (carry >> 32) + ((lx * hy) >> 32) + (hx * hy);
    return result;
}

// Multiply an integer array by a single uint64
static uint64_t mulOne(uint64_t* dst, uint64_t* x, uint32_t len, uint64_t y) {
    uint64_t ly = y & 0xffffffffULL;
    uint64_t hy = y >> 32;
    uint64_t carry = 0;
    for (uint32_t i = 0; i < len; ++i)
        dst[i] = mulTerm(x[i], ly, hy, carry);
    return carry;
}

// Generalized multiplier
NO_SANITIZE("unsigned-integer-overflow")
static void mul(uint64_t* dst, uint64_t* x, uint32_t xlen, uint64_t* y, uint32_t ylen) {
    dst[xlen] = mulOne(dst, x, xlen, y[0]);
    for (uint32_t i = 1; i < ylen; i++) {
        uint64_t ly = y[i] & 0xffffffffULL;
        uint64_t hy = y[i] >> 32;
        uint64_t carry = 0;
        for (uint32_t j = 0; j < xlen; j++) {
            uint64_t result = mulTerm(x[j], ly, hy, carry);
            dst[i + j] += result;
            if (dst[i + j] < result)
                carry++;
        }
        dst[i + xlen] = carry;
    }
}

// Implementation of Knuth's Algorithm D (Division of nonnegative integers)
// from "Art of Computer Programming, Volume 2", section 4.3.1, p. 272.
// Note that this implementation is based on the APInt implementation from
// the LLVM project.
NO_SANITIZE("unsigned-integer-overflow")
static void knuthDiv(uint32_t* u, uint32_t* v, uint32_t* q, uint32_t* r, uint32_t m, uint32_t n) {
    ASSERT(u);
    ASSERT(v);
    ASSERT(q);
    ASSERT(u != v && u != q && v != q);
    ASSERT(n > 1);

    // b denotes the base of the number system. In our case b is 2^32.
    const uint64_t b = 1ULL << 32;

    // D1. [Normalize.] Set d = b / (v[n-1] + 1) and multiply all the digits of
    // u and v by d. Note that we have taken Knuth's advice here to use a power
    // of 2 value for d such that d * v[n-1] >= b/2 (b is the base). A power of
    // 2 allows us to shift instead of multiply and it is easy to determine the
    // shift amount from the leading zeros.  We are basically normalizing the u
    // and v so that its high bits are shifted to the top of v's range without
    // overflow. Note that this can require an extra word in u so that u must
    // be of length m+n+1.
    uint32_t shift = countLeadingZeros32(v[n - 1]);
    uint32_t v_carry = 0;
    uint32_t u_carry = 0;
    if (shift) {
        for (uint32_t i = 0; i < m + n; i++) {
            uint32_t u_tmp = u[i] >> (32 - shift);
            u[i] = (u[i] << shift) | u_carry;
            u_carry = u_tmp;
        }
        for (uint32_t i = 0; i < n; i++) {
            uint32_t v_tmp = v[i] >> (32 - shift);
            v[i] = (v[i] << shift) | v_carry;
            v_carry = v_tmp;
        }
    }
    u[m + n] = u_carry;

    // D2. [Initialize j.]  Set j to m. This is the loop counter over the places.
    int j = m;
    do {
        // D3. [Calculate q'.].
        //     Set qp = (u[j+n]*b + u[j+n-1]) / v[n-1]. (qp=qprime=q')
        //     Set rp = (u[j+n]*b + u[j+n-1]) % v[n-1]. (rp=rprime=r')
        // Now test if qp == b or qp*v[n-2] > b*rp + u[j+n-2]; if so, decrease
        // qp by 1, inrease rp by v[n-1], and repeat this test if rp < b. The test
        // on v[n-2] determines at high speed most of the cases in which the trial
        // value qp is one too large, and it eliminates all cases where qp is two
        // too large.
        uint64_t dividend = (uint64_t(u[j + n]) << 32) + u[j + n - 1];
        uint64_t qp = dividend / v[n - 1];
        uint64_t rp = dividend % v[n - 1];
        if (qp == b || qp * v[n - 2] > b * rp + u[j + n - 2]) {
            qp--;
            rp += v[n - 1];
            if (rp < b && (qp == b || qp * v[n - 2] > b * rp + u[j + n - 2]))
                qp--;
        }

        // D4. [Multiply and subtract.] Replace (u[j+n]u[j+n-1]...u[j]) with
        // (u[j+n]u[j+n-1]..u[j]) - qp * (v[n-1]...v[1]v[0]). This computation
        // consists of a simple multiplication by a one-place number, combined with
        // a subtraction.
        // The digits (u[j+n]...u[j]) should be kept positive; if the result of
        // this step is actually negative, (u[j+n]...u[j]) should be left as the
        // true value plus b**(n+1), namely as the b's complement of
        // the true value, and a "borrow" to the left should be remembered.
        int64_t borrow = 0;
        for (uint32_t i = 0; i < n; ++i) {
            uint64_t p = qp * uint64_t(v[i]);
            int64_t subres = int64_t(u[j + i]) - borrow - (uint32_t)p;
            u[j + i] = (uint32_t)subres;
            borrow = (p >> 32) - (subres >> 32);
        }
        bool isNeg = u[j + n] < borrow;
        u[j + n] -= (uint32_t)borrow;

        // D5. [Test remainder.] Set q[j] = qp. If the result of step D4 was
        // negative, go to step D6; otherwise go on to step D7.
        q[j] = (uint32_t)qp;
        if (isNeg) {
            // D6. [Add back]. The probability that this step is necessary is very
            // small, on the order of only 2/b. Make sure that test data accounts for
            // this possibility. Decrease q[j] by 1
            q[j]--;
            // and add (0v[n-1]...v[1]v[0]) to (u[j+n]u[j+n-1]...u[j+1]u[j]).
            // A carry will occur to the left of u[j+n], and it should be ignored
            // since it cancels with the borrow that occurred in D4.
            bool carry = false;
            for (uint32_t i = 0; i < n; i++) {
                uint32_t limit = std::min(u[j + i], v[i]);
                u[j + i] += v[i] + carry;
                carry = u[j + i] < limit || (carry && u[j + i] == limit);
            }
            u[j + n] += carry;
        }

        // D7. [Loop on j.]  Decrease j by one. Now if j >= 0, go back to D3.
    } while (--j >= 0);

    // D8. [Unnormalize]. Now q[...] is the desired quotient, and the desired
    // remainder may be obtained by dividing u[...] by d. If r is non-null we
    // compute the remainder (urem uses this).
    if (r) {
        // The value d is expressed by the "shift" value above since we avoided
        // multiplication by d by using a shift left. So, all we have to do is
        // shift right here.
        if (shift) {
            uint32_t carry = 0;
            for (int i = n - 1; i >= 0; i--) {
                r[i] = (u[i] >> shift) | carry;
                carry = u[i] << (32 - shift);
            }
        }
        else {
            for (int i = n - 1; i >= 0; i--)
                r[i] = u[i];
        }
    }
}

// Like memcpy, but at the bit level instead of bytes
// i.e if destBitOffset % 8 == bitLength % 8 == 0, this is
// equivalent to memcpy(dest + destBitOffset / 8, src, bitLength / 8)
static void copyBits(uint8_t* dest, uint16_t destBitOffset, uint8_t* src, uint16_t bitLength, uint16_t srcBitOffset = 0) {
    if (bitLength == 0) return;
    // Get the first byte we want to write to, and the reamaining bits are a bit offset
    dest += destBitOffset / 8;
    destBitOffset %= 8;
    src += srcBitOffset / 8;
    srcBitOffset %= 8;

    // Writing to the first byte is a special case, due to the bit offset
    uint8_t bitsToWrite = std::min<uint8_t>((uint8_t)bitLength, (uint8_t)(8 - destBitOffset));

    uint8_t srcByte = srcBitOffset ? (*src >> srcBitOffset) + (src[1] << (8 - srcBitOffset)) : *src;
    *dest = (*dest   & ((1 << destBitOffset) - 1)) + // preserved bits
            ((srcByte & ((1 << bitsToWrite) - 1)) << destBitOffset); // new bits

    // all remaining writes to dest are byte-aligned, but the reads from src
    // may not be
    srcBitOffset += bitsToWrite;
    bitLength -= bitsToWrite;
    while (bitLength > 0) {
        // advance dest one byte, and src the proper number of bits
        ++dest;
        src += srcBitOffset / 8;
        srcBitOffset %= 8;

        // Number of bits we are writing to this byte
        bitsToWrite = std::min<uint8_t>((uint8_t)bitLength, 8);
        // get the next 8 bits of src, probably not byte aligned
        // (if bitsToWrite < 8, this could have some extra bits in it
        srcByte = srcBitOffset ? (*src >> srcBitOffset) + (src[1] << (8 - srcBitOffset)) : *src;

        // Write srcByte, filling the upper bits with zereos if we have less than
        // a byte left to write.
        *dest = srcByte & ((1 << bitsToWrite) - 1); // new bits

        bitLength -= bitsToWrite;
        srcBitOffset += bitsToWrite;
    }
}

