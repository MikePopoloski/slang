//------------------------------------------------------------------------------
// TypeHelpers.h
// Contains internal helper functions for Type implementations
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <numeric>

#include "slang/symbols/AllTypes.h"
#include "slang/symbols/VariableSymbols.h"

namespace slang {

/// Return {a, b} to model the size of a dynamic size with "aR+b" where "a" and "b" are compile-time
/// constants and "R" is runtime determined.

// destination=0: source type where "a" is the greatest common divisor of element sizes of
// all dynamically sized items and "b" is the sum of all fixed sizes.

// destination=1: destination type with all dynamically sized items empty. "a" is zero and "b" is
// the sum of all fixed sizes.

// destination=2: destination type with the first dynamically sized item filled and "a" is the
// element size of this first item. The remaining dynamically sized items are empty except ancestors
// of the first item needs to have size one. "b" is the sum of all fixed sizes plus sizes of
// siblings of the first item when their common parent is dynamically sized.

static std::pair<bitwidth_t, bitwidth_t> dynamicBitstreamSize(const Type& type,
                                                              unsigned int destination = 0) {
    auto fixedSize = type.getBitWidth();
    if (fixedSize > 0)
        return { 0, fixedSize };
    if (type.isString())
        return { destination == 1 ? 0 : CHAR_BIT, 0 };
    bitwidth_t multiplier = 0;
    // TODO: check for overflow
    if (type.isUnpackedArray()) {
        auto [multiplierElem, fixedSizeElem] =
            dynamicBitstreamSize(*type.getArrayElementType(), destination);
        const auto& ct = type.getCanonicalType();
        if (ct.kind == SymbolKind::FixedSizeUnpackedArrayType) { // fixed size packed array
            auto rw = ct.as<FixedSizeUnpackedArrayType>().range.width();
            multiplier = multiplierElem * rw; // multiply element values by packed array width
            fixedSize = fixedSizeElem * rw;
        }
        else if (destination) {    // dynamically sized destination type
            if (destination > 1) { // Fill first dynamically sized item otherwise keep empty
                if (!multiplierElem)
                    multiplier = fixedSizeElem; // element is fixed size
                else {
                    multiplier = multiplierElem; // element is dynamically sized
                    fixedSize = fixedSizeElem;
                }
            }
        }
        else
            multiplier = std::gcd(multiplierElem, fixedSizeElem); // dynamically sized source type
    }
    else if (type.isUnpackedStruct()) {
        auto& us = type.getCanonicalType().as<UnpackedStructType>();
        for (auto& field : us.membersOfType<FieldSymbol>()) {
            auto [multiplierElem, fixedSizeElem] =
                dynamicBitstreamSize(field.getType(), destination);
            if (destination > 1 && multiplierElem > 0)
                destination = 1; // dynamically sized field filled and rest should be empty
            multiplier = std::gcd(multiplier, multiplierElem);
            fixedSize += fixedSizeElem;
        }
    }
    // TODO: classes
    return { multiplier, fixedSize };
}

/// Compile-time check on dynamically sized bit-stream casting
static bool dynamicSizeMatch(const Type& destination, const Type& source) {
    auto [sourceMultiplier, sourceFixedSize] = dynamicBitstreamSize(source);
    auto [destEmptyMultiplier, destEmptyFixedSize] = dynamicBitstreamSize(destination, 1);
    ASSERT(!destEmptyMultiplier && !sourceMultiplier == source.isFixedSize());
    if (destEmptyFixedSize >= sourceFixedSize &&
        !((destEmptyFixedSize - sourceFixedSize) % sourceMultiplier))
        return true;
    auto [destFillMultiplier, destFillFixedSize] = dynamicBitstreamSize(destination, 2);
    ASSERT(!destFillMultiplier == destination.isFixedSize());
    /* Follow IEEE standard to check dynamic-sized types at compile-time.

     // runtime error
     struct {bit a[$]; shortint b;} a = {{1,2,3,4}, 67};
     int b = int'(a);
     // sourceMultiplier=1 sourceFixedSize=16 destEmptyMultiplier=0 destEmptyFixedSize=32
     // destFillMultiplier=0 destFillFixedSize=32

     // compile time error
     typedef struct {byte a[$]; bit b;} dest_t;
     int a;
     dest_t b = dest_t'(a);
     // sourceMultiplier=0 sourceFixedSize=32 destEmptyMultiplier=0 destEmptyFixedSize=1
     // destFillMultiplier=8 destFillFixedSize=1
     */
    return (destFillMultiplier >= sourceFixedSize || destFillMultiplier > 0) &&
           !((sourceFixedSize > destFillFixedSize ? sourceFixedSize - destFillFixedSize
                                                  : destFillFixedSize - sourceFixedSize) %
             std::gcd(sourceMultiplier, destFillMultiplier));
}

/// Validates sizes and returns remaining size for the first dynamic item in constant evaluation
static bitwidth_t bitstreamCastRemainingSize(const Type& destination, bitwidth_t srcSize) {
    bitwidth_t remain = 0;
    if (destination.isFixedSize()) {
        auto destSize = destination.bitstreamWidth();
        if (destSize != srcSize)
            return srcSize + 1; // cannot fit
    }
    else {
        auto [destEmptyMultiplier, destEmptyFixedSize] = dynamicBitstreamSize(destination, 1);
        if (destEmptyFixedSize > srcSize)
            return srcSize + 1;             // source size too small to fill destination fixed size
        if (destEmptyFixedSize < srcSize) { // Calculate remaining size to dynamically fill
            auto [destFillMultiplier, destFillFixedSize] = dynamicBitstreamSize(destination, 2);
            if (srcSize < destFillFixedSize ||
                (srcSize - destFillFixedSize) % destFillMultiplier != 0)
                return srcSize + 1;               // cannot fit
            remain = srcSize - destFillFixedSize; // Size to fill the first dynamically size item
        }
    }
    return remain;
}

static ConstantValue constContainer(const Type& type, span<ConstantValue> elems) {
    switch (type.kind) {
        case SymbolKind::FixedSizeUnpackedArrayType:
        case SymbolKind::DynamicArrayType:
        case SymbolKind::UnpackedStructType:
            return ConstantValue::Elements(elems.cbegin(), elems.cend());
        case SymbolKind::QueueType:
            return SVQueue(elems.cbegin(), elems.cend());
        default:
            THROW_UNREACHABLE;
    }
}

using PackVector = std::vector<const ConstantValue*>;

/// Performs pack operation to create a bit stream
static void pack(const ConstantValue& value, PackVector& packed) {
    if (value.isInteger())
        packed.push_back(&value);
    else if (value.isString()) {
        if (!value.str().empty())
            packed.push_back(&value);
    }
    else if (value.isUnpacked()) {
        for (const auto& cv : value.elements())
            pack(cv, packed);
    }
    else if (value.isMap()) {
        for (const auto& kv : *value.map()) {
            pack(kv.second, packed);
        }
    }
    else if (value.isQueue()) {
        for (const auto& cv : *value.queue())
            pack(cv, packed);
    }
    else {
        // TODO: classes
        THROW_UNREACHABLE;
    }
}

static SVInt slicePacked(PackVector::const_iterator& iter, bitwidth_t& bit, bitwidth_t width) {
    const ConstantValue* cp;
    for (;;) {
        cp = *iter;
        if (cp->isInteger()) {
            if (bit < cp->integer().getBitWidth())
                break;
        }
        else {
            if (bit < cp->str().length() * CHAR_BIT)
                break;
        }
        bit = 0;
        iter++;
    }
    if (cp->isInteger()) {
        const auto& ci = cp->integer();
        auto msb = ci.getBitWidth() - bit - 1;
        auto lsb = std::min(bit + width, ci.getBitWidth());
        lsb = ci.getBitWidth() - lsb;
        bit += msb - lsb + 1;
        ASSERT(bit <= ci.getBitWidth());
        return ci.slice(static_cast<int32_t>(msb), static_cast<int32_t>(lsb));
    }
    else {
        std::string_view str = cp->str();
        auto firstByte = bit / CHAR_BIT;
        auto lastByte = (bit + width - 1) / CHAR_BIT;
        bitwidth_t len;
        if (lastByte < str.length())
            len = lastByte - firstByte + 1;
        else {
            len = static_cast<bitwidth_t>(str.length() - firstByte);
            width = len * CHAR_BIT - bit % CHAR_BIT;
        }
        SmallVectorSized<byte, 8> buffer;
        const auto substr = str.substr(firstByte, len);
        for (auto it = substr.rbegin(); it != substr.rend(); it++)
            buffer.append(static_cast<byte>(*it));
        len *= CHAR_BIT;
        auto ci = SVInt(len, span<const byte>(buffer), false);
        auto msb = len - bit % CHAR_BIT - 1;
        auto lsb = CHAR_BIT - 1 - (bit + width - 1) % CHAR_BIT;
        bit += width;
        ASSERT(bit <= str.length() * CHAR_BIT);
        if (lsb > 0 || msb < len - 1)
            return ci.slice(static_cast<int32_t>(msb), static_cast<int32_t>(lsb));
        else
            return ci;
    }
}

/// Performs unpack operation on a bit stream
static ConstantValue unpack(const Type& type, PackVector::const_iterator& iter, bitwidth_t& bit,
                            bitwidth_t& dynamicSize) {

    auto concatPacked = [&](bitwidth_t width, bool isFourState) {
        SmallVectorSized<SVInt, 8> buffer;
        while (width > 0) {
            auto ci = slicePacked(iter, bit, width);
            ASSERT(ci.getBitWidth() <= width);
            width -= ci.getBitWidth();
            if (!isFourState)
                ci.flattenUnknowns();
            buffer.emplace(ci);
        }
        return SVInt::concat(span<SVInt const>(buffer.begin(), buffer.end()));
    };

    if (type.isIntegral()) {
        auto cc = concatPacked(type.getBitWidth(), type.isFourState());
        cc.setSigned(type.isSigned());
        return cc;
    }

    if (type.isString()) {
        if (!dynamicSize)
            return std::string();
        auto width = dynamicSize;
        ASSERT(width % CHAR_BIT == 0);
        dynamicSize = 0;
        return ConstantValue(concatPacked(width, false)).convertToStr();
    }

    if (type.isUnpackedArray()) {
        const auto& ct = type.getCanonicalType();
        SmallVectorSized<ConstantValue, 16> buffer;
        if (ct.kind != SymbolKind::FixedSizeUnpackedArrayType) {
            // dynamicSize is the remaining size: For unbounded dynamically sized types, the
            // conversion process is greedy: adjust the size of the first dynamically sized item in
            // the destination to the remaining size; any remaining dynamically sized items are left
            // empty.
            if (dynamicSize > 0) {
                auto elemWidth = type.getArrayElementType()->bitstreamWidth();
                if (!elemWidth)
                    elemWidth = dynamicSize;
                ASSERT(dynamicSize % elemWidth == 0);
                for (auto i = dynamicSize / elemWidth; i > 0; i--)
                    buffer.emplace(unpack(*type.getArrayElementType(), iter, bit, dynamicSize));
                ASSERT(!dynamicSize || type.getArrayElementType()->isFixedSize());
                dynamicSize = 0;
            }
        }
        else {
            const auto& ct1 = ct.as<FixedSizeUnpackedArrayType>();
            const auto& elem = ct1.elementType;
            for (auto width = ct1.range.width(); width > 0; width--)
                buffer.emplace(unpack(elem, iter, bit, dynamicSize));
        }
        return constContainer(ct, buffer);
    }

    if (type.isUnpackedStruct()) {
        SmallVectorSized<ConstantValue, 16> buffer;
        const auto& ct = type.getCanonicalType();
        auto& us = ct.as<UnpackedStructType>();
        for (auto& field : us.membersOfType<FieldSymbol>())
            buffer.emplace(unpack(field.getType(), iter, bit, dynamicSize));
        return constContainer(ct, buffer);
    }

    // TODO: classes
    return nullptr;
}

} // namespace slang
