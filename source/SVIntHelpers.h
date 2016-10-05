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
    return value;
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
    return value;
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