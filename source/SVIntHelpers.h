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
    // this is split out so that if we have an unknown value we can reuse the code
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

static void signExtendCopy(uint64_t* output, const uint64_t* input, uint16_t oldBits, uint16_t newBits) {
    // copy full words over
    int i;
    uint64_t word = 0;
    for (i = 0; i != oldBits / SVInt::BITS_PER_WORD; i++) {
        word = input[i];
        output[i] = word;
    }

    // sign-extend the last word
    uint32_t last = (-oldBits) % SVInt::BITS_PER_WORD;
    if (last != 0)
        word = (int64_t)input[i] << last >> last;
    else
        word = (int64_t)word >> (SVInt::BITS_PER_WORD - 1);

    // fill remaining words
    for (; i != newBits / SVInt::BITS_PER_WORD; i++) {
        output[i] = word;
        word = (int64_t)word >> (SVInt::BITS_PER_WORD - 1);
    }

    // write remaining partial word
    last = (-newBits) % SVInt::BITS_PER_WORD;
    if (last != 0)
        output[i] = word << last >> last;
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
static bool subGeneral(uint64_t* dst, uint64_t* x, uint64_t* y, int len) {
    bool borrow = false;
    for (int i = 0; i < len; i++) {
        uint64_t tmp = borrow ? x[i] - 1 : x[i];
        borrow = y[i] > tmp || (borrow && x[i] == 0);
        dst[i] = tmp - y[i];
    }
    return borrow;
}

// Implementation of Knuth's Algorithm D (Division of nonnegative integers)
// from "Art of Computer Programming, Volume 2", section 4.3.1, p. 272.
// Note that this implementation is based on the APInt implementation from
// the LLVM project.
static void knuthDiv(uint32_t* u, uint32_t* v, uint32_t* q, uint32_t* r, uint32_t m, uint32_t n) {
    ASSERT(u, "Must provide dividend");
    ASSERT(v, "Must provide divisor");
    ASSERT(q, "Must provide quotient");
    ASSERT(u != v && u != q && v != q, "Must use different memory");
    ASSERT(n > 1, "n must be > 1");
    
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
    uint32_t shift = countLeadingZeros(v[n - 1]);
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
        // shift right here. In order to mak
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

