//------------------------------------------------------------------------------
// SVIntHelpers.h
// Contains internal helper functions for SVInt implementations
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <bit>
#include <cstdint>
#include <cstring>

#include "slang/numeric/SVInt.h"

#if defined(__x86_64__) || defined(_M_X64)
using calc_out_t = long long unsigned;

#    ifdef __GNUC__
#        include <x86intrin.h>
#    endif
#    define addcarry64(c, a, b, out) _addcarry_u64(c, a, b, out)
#    define subborrow64(c, a, b, out) _subborrow_u64(c, a, b, out)
#else
using calc_out_t = uint64_t;

// On other platforms, define the intrinsics ourselves.
static uint8_t addcarry64(uint8_t c, uint64_t a, uint64_t b, calc_out_t* out) {
    uint64_t tmp = b + (c != 0 ? 1 : 0);
    uint64_t result = a + tmp;
    *out = result;
    return (a > result) | (b > tmp);
}

static uint8_t subborrow64(uint8_t c, uint64_t a, uint64_t b, calc_out_t* out) {
    uint64_t tmp = b + (c != 0 ? 1 : 0);
    uint64_t result = a - tmp;
    *out = result;
    return (result > a) | (b > tmp);
}
#endif

#if defined(_MSC_VER) && defined(_M_IX86)
#    include <intrin.h>

uint64_t _umul128(uint64_t multiplier, uint64_t multiplicand, uint64_t* product_hi) {
    // multiplier   = ab = a * 2^32 + b
    // multiplicand = cd = c * 2^32 + d
    // ab * cd = a * c * 2^64 + (a * d + b * c) * 2^32 + b * d
    uint32_t a = (uint32_t)(multiplier >> 32);
    uint32_t b = (uint32_t)multiplier;
    uint32_t c = (uint32_t)(multiplicand >> 32);
    uint32_t d = (uint32_t)multiplicand;

    uint64_t ad = __emulu(a, d);
    uint64_t bd = __emulu(b, d);

    uint64_t adbc = ad + __emulu(b, c);
    uint64_t adbc_carry = (adbc < ad);

    // multiplier * multiplicand = product_hi * 2^64 + product_lo
    uint64_t product_lo = bd + (adbc << 32);
    uint64_t product_lo_carry = (product_lo < bd);
    *product_hi = __emulu(a, c) + (adbc >> 32) + (adbc_carry << 32) + product_lo_carry;

    return product_lo;
}
#endif

namespace slang {

/// Provides a temporary storage region of dynamic size. If that size is less than
/// the specified stack size, the memory will be entirely contained on the stack.
/// Otherwise, a heap allocation will be performed and then cleaned up in the destructor.
template<typename T, size_t StackCount>
class TempBuffer {
public:
    explicit TempBuffer(size_t size) : size(size) {
        if (size > StackCount)
            ptr = new T[size];
        else {
            ptr = reinterpret_cast<T*>(stackBase);
            std::ranges::uninitialized_default_construct_n(ptr, ptrdiff_t(size));
        }
    }

    void fill(uint8_t b) { memset(ptr, b, size * sizeof(T)); }

    ~TempBuffer() {
        if (size > StackCount)
            delete[] ptr;
        else
            std::ranges::destroy_n(ptr, ptrdiff_t(size));
    }

    T* get() const { return ptr; }

private:
    T* ptr;
    size_t size;
    alignas(T) char stackBase[StackCount * sizeof(T)];
};

static void lshrNear(uint64_t* dst, uint64_t* src, uint32_t words, uint32_t amount) {
    // fast case for logical right shift of a small amount (less than 64 bits)
    uint64_t carry = 0;
    for (int i = int(words - 1); i >= 0; i--) {
        uint64_t temp = src[i];
        dst[i] = (temp >> amount) | carry;
        carry = temp << (64 - amount);
    }
}

static void lshrFar(uint64_t* dst, uint64_t* src, uint32_t wordShift, uint32_t offset,
                    uint32_t start, uint32_t numWords) {
    // this function is split out so that if we have an unknown value we can reuse the code
    // optimization: move whole words
    if (wordShift == 0) {
        for (uint32_t i = start; i < start + numWords - offset; i++)
            dst[i] = src[i + offset];
    }
    else {
        // shift low order words
        uint32_t breakWord = start + numWords - offset - 1;
        for (uint32_t i = start; i < breakWord; i++) {
            dst[i] = (src[i + offset] >> wordShift) |
                     (src[i + offset + 1] << (SVInt::BITS_PER_WORD - wordShift));
        }

        // shift the "break" word
        dst[breakWord] = src[breakWord + offset] >> wordShift;
    }
}

static void shlFar(uint64_t* dst, uint64_t* src, uint32_t wordShift, uint32_t offset,
                   uint32_t start, uint32_t numWords) {
    // optimization: move whole words
    if (wordShift == 0) {
        for (uint32_t i = start + offset; i < start + numWords; i++)
            dst[i] = src[i - offset];
    }
    else {
        for (uint32_t i = start + numWords - 1; i > start + offset; i--) {
            dst[i] = src[i - offset] << wordShift |
                     src[i - offset - 1] >> (SVInt::BITS_PER_WORD - wordShift);
        }
        dst[start + offset] = src[start] << wordShift;
    }

    for (uint32_t i = start; i < start + offset; i++)
        dst[i] = 0;
}

static void signExtendCopy(uint64_t* output, const uint64_t* input, bitwidth_t oldBits,
                           uint32_t oldWords, uint32_t newWords) {
    // copy full words over
    memcpy(output, input, sizeof(uint64_t) * oldWords);

    // sign-extend the last word
    bitwidth_t lastWordBits = SVInt::BITS_PER_WORD - (((oldBits - 1) % SVInt::BITS_PER_WORD) + 1);
    output[oldWords - 1] = uint64_t(int64_t(output[oldWords - 1] << lastWordBits) >> lastWordBits);

    // fill the remaining words with the sign bit
    bool isNegative = output[oldWords - 1] >> (SVInt::BITS_PER_WORD - 1);
    memset(output + oldWords, isNegative ? -1 : 0, (newWords - oldWords) * sizeof(uint64_t));
}

// Check whether all the bits above word.bit is identical to word.bit.
static bool isSignExtended(const uint64_t* input, uint32_t numWords, uint32_t word, uint32_t bit,
                           uint64_t topWordMask) {
    bool sign = (input[word] & (1ULL << bit)) != 0;
    if (sign && numWords - 1 > word) {
        if (input[numWords - 1] != topWordMask)
            return false;
        numWords--;
        topWordMask = UINT64_MAX;
    }

    uint64_t mask = sign ? UINT64_MAX : 0;
    for (auto i = numWords - 1; i > word; i--) {
        if (input[i] != mask)
            return false;
    }

    if (numWords - 1 == word)
        mask &= topWordMask;
    mask >>= bit;
    return (input[word] >> bit) == mask;
}

// If word.bit is one, make all bits above word.bit become one.
static void signExtend(uint64_t* input, uint32_t numWords, uint32_t word, uint32_t bit,
                       uint64_t topWordMask) {
    if ((input[word] & (1ULL << bit)) == 0)
        return; // If word.bit is zero, don't change anything.

    if (numWords - 1 > word) {
        input[numWords - 1] = topWordMask;
        numWords--;
        topWordMask = UINT64_MAX;
    }

    uint64_t mask = UINT64_MAX;
    for (auto i = numWords - 1; i > word; i--)
        input[i] = mask;

    mask <<= bit;
    if (numWords - 1 == word)
        mask &= topWordMask;
    input[word] |= mask;
}

// Specialized adder for values <= 64.
static bool addOne(uint64_t* dst, uint64_t* src, uint32_t len, uint64_t value) {
    uint8_t carry = 0;
    for (uint32_t i = 0; i < len; i++) {
        calc_out_t result;
        carry = addcarry64(carry, src[i], value, &result);
        dst[i] = result;

        if (!carry)
            break;

        value = 0;
    }
    return carry;
}

// Specialized subtractor for values <= 64.
static bool subOne(uint64_t* dst, uint64_t* src, uint32_t len, uint64_t value) {
    uint8_t borrow = 0;
    for (uint32_t i = 0; i < len; i++) {
        calc_out_t result;
        borrow = subborrow64(borrow, src[i], value, &result);
        dst[i] = result;

        if (!borrow)
            break;

        value = 0;
    }
    return borrow;
}

// Generalized adder
SLANG_NO_SANITIZE("unsigned-integer-overflow")
static bool addGeneral(uint64_t* dst, const uint64_t* x, const uint64_t* y, uint32_t len) {
    uint8_t carry = 0;
    for (uint32_t i = 0; i < len; i++) {
        calc_out_t result;
        carry = addcarry64(carry, x[i], y[i], &result);
        dst[i] = result;
    }
    return carry;
}

// Generalized subtractor (x - y)
SLANG_NO_SANITIZE("unsigned-integer-overflow")
static bool subGeneral(uint64_t* dst, const uint64_t* x, const uint64_t* y, uint32_t len) {
    uint8_t borrow = 0;
    for (uint32_t i = 0; i < len; i++) {
        calc_out_t result;
        borrow = subborrow64(borrow, x[i], y[i], &result);
        dst[i] = result;
    }
    return borrow;
}

// One term of a multiply operation
SLANG_NO_SANITIZE("unsigned-integer-overflow")
static uint64_t mulTerm(uint64_t x, uint64_t y, uint64_t& carry) {
#ifdef _MSC_VER
    uint64_t high;
    uint64_t low = _umul128(x, y, &high);
    carry = high + addcarry64(0, low, carry, &low);
    return low;
#else
    using uint128_t = unsigned __int128;
    uint128_t p = uint128_t(x) * uint128_t(y) + carry;
    carry = uint64_t(p >> 64);
    return uint64_t(p);
#endif
}

// Multiply an integer array by a single uint64
static uint64_t mulOne(uint64_t* dst, const uint64_t* x, uint32_t len, uint64_t y) {
    uint64_t carry = 0;
    for (uint32_t i = 0; i < len; ++i)
        dst[i] = mulTerm(x[i], y, carry);
    return carry;
}

static void mulKaratsuba(uint64_t* dst, const uint64_t* x, uint32_t xlen, const uint64_t* y,
                         uint32_t ylen);

// Generalized multiplier
SLANG_NO_SANITIZE("unsigned-integer-overflow")
static void mul(uint64_t* dst, const uint64_t* x, uint32_t xlen, const uint64_t* y, uint32_t ylen) {
    if (xlen > 7 && ylen > 7) {
        mulKaratsuba(dst, x, xlen, y, ylen);
        return;
    }

    dst[xlen] = mulOne(dst, x, xlen, y[0]);
    for (uint32_t i = 1; i < ylen; i++) {
        uint64_t carry = 0;
        for (uint32_t j = 0; j < xlen; j++) {
            calc_out_t result;
            uint8_t c = addcarry64(0, mulTerm(x[j], y[i], carry), dst[i + j], &result);

            dst[i + j] = result;
            carry += c;
        }
        dst[i + xlen] = carry;
    }
}

static void unevenAdd(uint64_t* dst, const uint64_t* x, uint32_t xlen, const uint64_t* y,
                      uint32_t ylen) {
    if (xlen < ylen) {
        std::swap(xlen, ylen);
        std::swap(x, y);
    }

    uint32_t i;
    uint8_t carry = 0;
    for (i = 0; i < ylen; ++i) {
        calc_out_t result;
        carry = addcarry64(carry, x[i], y[i], &result);
        dst[i] = result;
    }
    for (; i < xlen; ++i) {
        calc_out_t result;
        carry = addcarry64(carry, x[i], 0, &result);
        dst[i] = result;
    }
    dst[i] = carry;
}

static void mulKaratsuba(uint64_t* dst, const uint64_t* x, uint32_t xlen, const uint64_t* y,
                         uint32_t ylen) {
    if (xlen > ylen) {
        std::swap(x, y);
        std::swap(xlen, ylen);
    }

    uint32_t shift = ylen >> 1;

    uint32_t xlSize = std::min(xlen, shift);
    uint32_t xhSize = xlen - xlSize;
    const uint64_t* xl = x;
    const uint64_t* xh = x + xlSize;

    uint32_t ylSize = std::min(ylen, shift);
    uint32_t yhSize = ylen - ylSize;
    const uint64_t* yl = y;
    const uint64_t* yh = y + ylSize;

    TempBuffer<uint64_t, 128> t1(xlen + ylen);
    t1.fill(0);
    mul(t1.get(), xh, xhSize, yh, yhSize);
    memset(dst, 0, (xlen + ylen) * sizeof(uint64_t));
    memcpy(dst + 2 * shift, t1.get(), (xhSize + yhSize) * sizeof(uint64_t));

    TempBuffer<uint64_t, 128> t2(xlen + ylen);
    t2.fill(0);
    mul(t2.get(), xl, xlSize, yl, ylSize);
    memcpy(dst, t2.get(), (xlSize + ylSize) * sizeof(uint64_t));

    uint32_t remaining = xlen + ylen - shift;
    subGeneral(dst + shift, dst + shift, t2.get(), remaining);
    subGeneral(dst + shift, dst + shift, t1.get(), remaining);

    t1.fill(0);
    unevenAdd(t1.get(), xh, xhSize, xl, xlSize);
    t2.fill(0);
    unevenAdd(t2.get(), yh, yhSize, yl, ylSize);

    SLANG_ASSERT(std::max(xlSize, xhSize) + 1 + std::max(ylSize, yhSize) + 1 < xlen + ylen);

    TempBuffer<uint64_t, 128> t3(xlen + ylen);
    t3.fill(0);
    mul(t3.get(), t1.get(), std::max(xlSize, xhSize) + 1, t2.get(), std::max(ylSize, yhSize) + 1);

    addGeneral(dst + shift, dst + shift, t3.get(), remaining);
}

// Implementation of Knuth's Algorithm D (Division of nonnegative integers)
// from "Art of Computer Programming, Volume 2", section 4.3.1, p. 272.
// Note that this implementation is based on the APInt implementation from
// the LLVM project.
SLANG_NO_SANITIZE("unsigned-integer-overflow")
static void knuthDiv(uint32_t* u, uint32_t* v, uint32_t* q, uint32_t* r, uint32_t m, uint32_t n) {
    SLANG_ASSERT(u);
    SLANG_ASSERT(v);
    SLANG_ASSERT(q);
    SLANG_ASSERT(u != v && u != q && v != q);
    SLANG_ASSERT(n > 1);

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
    uint32_t shift = (uint32_t)std::countl_zero(v[n - 1]);
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
    uint32_t j = m;
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
            borrow = int64_t(p >> 32) - (subres >> 32);
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
    } while (--j < UINT32_MAX);

    // D8. [Unnormalize]. Now q[...] is the desired quotient, and the desired
    // remainder may be obtained by dividing u[...] by d. If r is non-null we
    // compute the remainder (urem uses this).
    if (r) {
        // The value d is expressed by the "shift" value above since we avoided
        // multiplication by d by using a shift left. So, all we have to do is
        // shift right here.
        if (shift) {
            uint32_t carry = 0;
            for (int i = int(n - 1); i >= 0; i--) {
                r[i] = (u[i] >> shift) | carry;
                carry = u[i] << (32 - shift);
            }
        }
        else {
            for (int i = int(n - 1); i >= 0; i--)
                r[i] = u[i];
        }
    }
}

// Does a word-by-word copy, but using bit offsets and lengths.
static void bitcpy(uint64_t* dest, uint32_t destOffset, const uint64_t* src, uint32_t length,
                   uint32_t srcOffset = 0) {
    if (length == 0)
        return;

    // Get the first word we want to write to, and the remaining bits are an offset.
    const uint32_t BitsPerWord = SVInt::BITS_PER_WORD;
    dest += destOffset / BitsPerWord;
    destOffset %= BitsPerWord;
    src += srcOffset / BitsPerWord;
    srcOffset %= BitsPerWord;

    // Writing to the first word is a special case, due to the bit offset
    if (destOffset) {
        uint32_t bitsToWrite = std::min(length, BitsPerWord - destOffset);
        length -= bitsToWrite;

        uint64_t srcWord;
        if (srcOffset) {
            // Be careful not to read past the bounds of the array.
            srcWord = *src >> srcOffset;
            if (BitsPerWord - srcOffset < bitsToWrite)
                srcWord |= src[1] << (BitsPerWord - srcOffset);
        }
        else {
            srcWord = *src;
        }

        uint64_t mask = (1ull << bitsToWrite) - 1;
        *dest = (*dest & ~(mask << destOffset)) | ((srcWord & mask) << destOffset);

        dest++;
        srcOffset += bitsToWrite;
        src += srcOffset / BitsPerWord;
        srcOffset %= BitsPerWord;
    }

    // Do a bulk copy of whole words, with all writes to dest word-aligned.
    for (uint32_t i = 0; i < length / BitsPerWord; i++) {
        *dest = srcOffset ? (*src >> srcOffset) | (src[1] << (BitsPerWord - srcOffset)) : *src;
        dest++;
        src++;
    }

    // Handle leftover bits in the final word.
    if (length %= BitsPerWord) {
        uint64_t mask = (1ull << length) - 1;
        uint64_t srcWord;
        if (srcOffset) {
            // Be careful not to read past the bounds of the array.
            srcWord = *src >> srcOffset;
            if (BitsPerWord - srcOffset < length)
                srcWord |= src[1] << (BitsPerWord - srcOffset);
        }
        else {
            srcWord = *src;
        }

        *dest = (*dest & ~mask) | (srcWord & mask);
    }
}

// Sets all of the bits in the given range to one.
static void setBits(uint64_t* dest, uint32_t destOffset, uint32_t length) {
    if (length == 0)
        return;

    // Get the first word we want to write to, and the remaining bits are an offset.
    const uint32_t BitsPerWord = SVInt::BITS_PER_WORD;
    dest += destOffset / BitsPerWord;
    destOffset %= BitsPerWord;

    // Writing to the first word is a special case, due to the bit offset
    if (destOffset) {
        uint32_t bitsToWrite = std::min(length, BitsPerWord - destOffset);
        length -= bitsToWrite;

        *dest |= ((1ull << bitsToWrite) - 1) << destOffset;
        dest++;
    }

    // Do a bulk set of whole words, with all writes to dest word-aligned.
    for (uint32_t i = 0; i < length / BitsPerWord; i++)
        *dest++ = UINT64_MAX;

    // Handle leftover bits in the final word.
    if (length %= BitsPerWord)
        *dest |= (1ull << length) - 1;
}

static void clearBits(uint64_t* dest, uint32_t destOffset, uint32_t length) {
    if (length == 0)
        return;

    // Get the first word we want to write to, and the remaining bits are an offset.
    const uint32_t BitsPerWord = SVInt::BITS_PER_WORD;
    dest += destOffset / BitsPerWord;
    destOffset %= BitsPerWord;

    // Writing to the first word is a special case, due to the bit offset
    if (destOffset) {
        uint32_t bitsToWrite = std::min(length, BitsPerWord - destOffset);
        length -= bitsToWrite;

        *dest &= ~(((1ull << bitsToWrite) - 1) << destOffset);
        dest++;
    }

    // Do a bulk set of whole words, with all writes to dest word-aligned.
    for (uint32_t i = 0; i < length / BitsPerWord; i++)
        *dest++ = 0;

    // Handle leftover bits in the final word.
    if (length %= BitsPerWord)
        *dest &= ~((1ull << length) - 1);
}

template<typename TVal, int ExpBits, int MantissaBits, int Bias>
static SVInt fromIEEE754(bitwidth_t bits, TVal value, bool isSigned, bool round) {
    uint64_t ival = 0;
    memcpy(&ival, &value, sizeof(TVal));

    constexpr int FullBits = sizeof(TVal) * 8;
    constexpr int ExpMask = (1ull << ExpBits) - 1;

    bool neg = ival >> (FullBits - 1);
    int64_t exp = ((ival >> MantissaBits) & ExpMask) - Bias;
    uint64_t mantissa = (ival & ((1ull << MantissaBits) - 1)) | (1ull << MantissaBits);

    // If exponent is negative the value is less than 1. The SystemVerilog
    // spec says that values of exactly 0.5 round away from zero, so check
    // for an exponent of -1 (which sets us at 0.5) and return 1 in that case.
    if (exp == -1 && round) {
        SVInt result(bits, 1, isSigned);
        return neg ? -result : result;
    }

    // Also check for infinities / NaNs; the standard doesn't say what to do
    // with these, but all other tools I tried just convert to zero.
    if (exp < 0 || exp == Bias + 1)
        return SVInt(bits, 0, isSigned);

    // At an exponent of MantissaBits we no longer have any fractional bits,
    // so if it's less than that we still need to handle rounding.
    if (exp < MantissaBits) {
        int64_t shift = MantissaBits - exp;
        uint64_t remainder = mantissa & ((1ull << shift) - 1);
        uint64_t halfway = 1ull << (shift - 1);
        mantissa >>= shift;

        if (remainder >= halfway && round)
            mantissa++;

        SVInt result(bits, mantissa, isSigned);
        return neg ? -result : result;
    }

    // Otherwise just shift the bits to the right location, they're all integral.
    SVInt result(bits, mantissa, isSigned);
    result = result.shl(bitwidth_t(exp - MantissaBits));
    return neg ? -result : result;
}

template<typename TVal, int ExpBits, int MantissaBits, int Bias>
static TVal toIEEE754(SVInt value) {
    // If the value has unknown bits, flatten them out.
    if (value.hasUnknown())
        value.flattenUnknowns();

    // Optimize for single word case.
    if (value.isSigned()) {
        auto i64 = value.as<int64_t>();
        if (i64)
            return TVal(*i64);
    }
    else {
        auto u64 = value.as<uint64_t>();
        if (u64)
            return TVal(*u64);
    }

    // If the number is negative, invert it so that we can work with
    // just positive numbers below.
    bool neg = value.isSigned() && value.isNegative();
    if (neg)
        value = -value;

    // Get the top bits for the mantissa. If the number has more than MantissaBits in it,
    // we also need to properly round. There are three cases for rounding:
    // 1. If they are greater than half way (0b1000..0) then round up.
    // 2. If they are less than half way then round down.
    // 3. If they are exactly equal to the half way point, round to even.
    bitwidth_t bwidth = value.getActiveBits();
    SLANG_ASSERT(bwidth);

    uint64_t mantissa, remainder = 0, halfway = 1;
    uint32_t word = (bwidth - 1) / SVInt::BITS_PER_WORD;
    uint32_t bit = bwidth % SVInt::BITS_PER_WORD;
    if (bit == 0)
        bit = SVInt::BITS_PER_WORD;

    constexpr int FullMantissa = MantissaBits + 1;

    if (!word || bit >= FullMantissa) {
        mantissa = value.getRawPtr()[word];
        if (bit > FullMantissa) {
            uint32_t shift = bit - FullMantissa;
            remainder = mantissa & ((1ull << shift) - 1);
            halfway = 1ull << (shift - 1);
            mantissa >>= shift;
        }
    }
    else {
        uint64_t high = value.getRawPtr()[word] << (FullMantissa - bit);
        uint32_t shift = SVInt::BITS_PER_WORD - FullMantissa + bit;
        uint64_t low = value.getRawPtr()[word - 1] >> shift;
        mantissa = high | low;

        remainder = value.getRawPtr()[word - 1] & ((1ull << shift) - 1);
        halfway = 1ull << (shift - 1);
        word--;
    }

    if (remainder > halfway)
        mantissa++;
    else if (remainder == halfway) {
        // Two possibilities here; if the mantissa is odd we're going to
        // round up no matter what. Otherwise, check all remaining words
        // to see if they contain any bits, which would make the remainder
        // greater than the halfway point.
        if (mantissa & 1)
            mantissa++;
        else {
            for (uint32_t i = word; i > 0; i--) {
                if (value.getRawPtr()[word - 1] != 0) {
                    mantissa++;
                    break;
                }
            }
        }
    }

    // The exponent of the number is equivalent to the number of active bits in
    // the integer minus one. If rounding the mantissa caused it to just tick
    // over the max mantissa bits, shift it back down and bump the exponent.
    uint64_t exp = bwidth - 1;
    if (mantissa == (1ull << FullMantissa)) {
        mantissa >>= 1;
        exp++;
    }

    // Check for overflow of the exponent.
    if (exp > Bias) {
        if (neg)
            return -std::numeric_limits<TVal>::infinity();
        return std::numeric_limits<TVal>::infinity();
    }

    // Build the final bit pattern (IEEE754 format)
    constexpr int FullBits = sizeof(TVal) * 8;
    constexpr uint64_t MantissaMask = (1ull << MantissaBits) - 1;

    uint64_t sign = neg ? (1ull << (FullBits - 1)) : 0;
    uint64_t ival = sign | ((exp + Bias) << MantissaBits) | (mantissa & MantissaMask);

    TVal result;
    memcpy(&result, &ival, sizeof(TVal));
    return result;
}

// Reverses the bit ordering of the number.
static uint32_t reverseBits32(uint32_t x) {
    x = ((x & 0xaaaaaaaa) >> 1) | ((x & 0x55555555) << 1);
    x = ((x & 0xcccccccc) >> 2) | ((x & 0x33333333) << 2);
    x = ((x & 0xf0f0f0f0) >> 4) | ((x & 0x0f0f0f0f) << 4);
    x = ((x & 0xff00ff00) >> 8) | ((x & 0x00ff00ff) << 8);
    return (x >> 16) | (x << 16);
}

static uint64_t reverseBits64(uint64_t x) {
    return (uint64_t(reverseBits32(uint32_t(x))) << 32) | reverseBits32(uint32_t(x >> 32));
}

} // namespace slang
