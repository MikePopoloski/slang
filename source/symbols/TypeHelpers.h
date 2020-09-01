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

enum class BitstreamSizeMode { Source, DestEmpty, DestFill };

/// Return {a, b} to model the size of a dynamic type with "aR+b" where "a" and "b" are compile-time
/// constants and "R" is runtime determined.
///
/// If mode == Source:
///   "a" is the greatest common divisor of element sizes of all dynamically sized items
///   "b" is the sum of all fixed sizes.
///
/// If mode == DestEmpty:
///   "a" is zero
///   "b" is the sum of all fixed sizes.
///
/// If mode == DestFill:
///   "a" is the element size of this first item.
///   "b" is the sum of all fixed sizes plus sizes of siblings of the first
///       item when their common parent is dynamically sized.
static std::pair<bitwidth_t, bitwidth_t> dynamicBitstreamSize(const Type& type,
                                                              BitstreamSizeMode mode) {
    bitwidth_t fixedSize = type.getBitWidth();
    if (fixedSize > 0)
        return { 0, fixedSize };

    if (type.isString())
        return { mode == BitstreamSizeMode::DestEmpty ? 0 : CHAR_BIT, 0 };

    // TODO: check for overflow
    bitwidth_t multiplier = 0;
    if (type.isUnpackedArray()) {
        auto [multiplierElem, fixedSizeElem] =
            dynamicBitstreamSize(*type.getArrayElementType(), mode);

        const auto& ct = type.getCanonicalType();
        if (ct.kind == SymbolKind::FixedSizeUnpackedArrayType) {
            auto rw = ct.as<FixedSizeUnpackedArrayType>().range.width();
            multiplier = multiplierElem * rw;
            fixedSize = fixedSizeElem * rw;
        }
        else if (mode == BitstreamSizeMode::DestFill) {
            if (!multiplierElem)
                multiplier = fixedSizeElem; // element is fixed size
            else {
                multiplier = multiplierElem; // element is dynamically sized
                fixedSize = fixedSizeElem;
            }
        }
        else if (mode == BitstreamSizeMode::Source) {
            multiplier = std::gcd(multiplierElem, fixedSizeElem);
        }
    }
    else if (type.isUnpackedStruct()) {
        auto& us = type.getCanonicalType().as<UnpackedStructType>();
        for (auto& field : us.membersOfType<FieldSymbol>()) {
            auto [multiplierElem, fixedSizeElem] = dynamicBitstreamSize(field.getType(), mode);
            if (mode == BitstreamSizeMode::DestFill && multiplierElem > 0) {
                // dynamically sized field filled and rest should be empty
                mode = BitstreamSizeMode::DestEmpty;
            }

            multiplier = std::gcd(multiplier, multiplierElem);
            fixedSize += fixedSizeElem;
        }
    }

    // TODO: classes
    return { multiplier, fixedSize };
}

/// Compile-time check that the source and destination types have the same dynamic bit-stream sizes.
static bool dynamicSizesMatch(const Type& destination, const Type& source) {
    auto [sourceMultiplier, sourceFixedSize] =
        dynamicBitstreamSize(source, BitstreamSizeMode::Source);
    auto [destEmptyMultiplier, destEmptyFixedSize] =
        dynamicBitstreamSize(destination, BitstreamSizeMode::DestEmpty);
    ASSERT(!destEmptyMultiplier && !sourceMultiplier == source.isFixedSize());

    if (destEmptyFixedSize >= sourceFixedSize) {
        bitwidth_t diff = destEmptyFixedSize - sourceFixedSize;
        if (diff % sourceMultiplier == 0)
            return true;
    }

    auto [destFillMultiplier, destFillFixedSize] =
        dynamicBitstreamSize(destination, BitstreamSizeMode::DestFill);
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

    if (destFillMultiplier == 0 && sourceFixedSize == 0)
        return false;

    bitwidth_t remaining;
    if (sourceFixedSize > destFillFixedSize)
        remaining = sourceFixedSize - destFillFixedSize;
    else
        remaining = destFillFixedSize - sourceFixedSize;

    return remaining % std::gcd(sourceMultiplier, destFillMultiplier) == 0;
}

/// Validates sizes and returns remaining size for the first dynamic item in constant evaluation
static bitwidth_t bitstreamCastRemainingSize(const Type& destination, bitwidth_t srcSize) {
    if (destination.isFixedSize()) {
        auto destSize = destination.bitstreamWidth();
        if (destSize != srcSize)
            return srcSize + 1; // cannot fit

        return 0;
    }

    // Check for the source size being too small to fill destination fixed size.
    auto [destEmptyMultiplier, destEmptyFixedSize] =
        dynamicBitstreamSize(destination, BitstreamSizeMode::DestEmpty);
    if (destEmptyFixedSize > srcSize)
        return srcSize + 1; // cannot fit

    if (destEmptyFixedSize == srcSize)
        return 0;

    // Calculate remaining size to dynamically fill.
    auto [destFillMultiplier, destFillFixedSize] =
        dynamicBitstreamSize(destination, BitstreamSizeMode::DestFill);
    if (srcSize < destFillFixedSize || (srcSize - destFillFixedSize) % destFillMultiplier != 0)
        return srcSize + 1;

    // Size to fill the first dynamically sized item.
    return srcSize - destFillFixedSize;
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

/// Performs pack operation to create a bit-stream.
static void packBitstream(const ConstantValue& value, SmallVector<const ConstantValue*>& packed) {
    if (value.isInteger()) {
        packed.append(&value);
    }
    else if (value.isString()) {
        if (!value.str().empty())
            packed.append(&value);
    }
    else if (value.isUnpacked()) {
        for (const auto& cv : value.elements())
            packBitstream(cv, packed);
    }
    else if (value.isMap()) {
        for (const auto& kv : *value.map()) {
            packBitstream(kv.second, packed);
        }
    }
    else if (value.isQueue()) {
        for (const auto& cv : *value.queue())
            packBitstream(cv, packed);
    }
    else {
        // TODO: classes
        THROW_UNREACHABLE;
    }
}

using PackIterator = const ConstantValue* const*;

static SVInt slicePacked(PackIterator& iter, bitwidth_t& bit, bitwidth_t width) {
    const ConstantValue* cp;
    while (true) {
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
        bitwidth_t msb = ci.getBitWidth() - bit - 1;
        bitwidth_t lsb = std::min(bit + width, ci.getBitWidth());
        lsb = ci.getBitWidth() - lsb;
        bit += msb - lsb + 1;

        ASSERT(bit <= ci.getBitWidth());
        return ci.slice(static_cast<int32_t>(msb), static_cast<int32_t>(lsb));
    }

    string_view str = cp->str();
    bitwidth_t firstByte = bit / CHAR_BIT;
    bitwidth_t lastByte = (bit + width - 1) / CHAR_BIT;

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
    auto ci = SVInt(len, buffer, false);
    bitwidth_t msb = len - bit % CHAR_BIT - 1;
    bitwidth_t lsb = CHAR_BIT - 1 - (bit + width - 1) % CHAR_BIT;

    bit += width;
    ASSERT(bit <= str.length() * CHAR_BIT);
    if (lsb > 0 || msb < len - 1)
        return ci.slice(static_cast<int32_t>(msb), static_cast<int32_t>(lsb));

    return ci;
}

/// Performs unpack operation on a bit-stream.
static ConstantValue unpackBitstream(const Type& type, PackIterator& iter, bitwidth_t& bit,
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
        return SVInt::concat(buffer);
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
                for (auto i = dynamicSize / elemWidth; i > 0; i--) {
                    buffer.emplace(
                        unpackBitstream(*type.getArrayElementType(), iter, bit, dynamicSize));
                }

                ASSERT(!dynamicSize || type.getArrayElementType()->isFixedSize());
                dynamicSize = 0;
            }
        }
        else {
            const auto& fsua = ct.as<FixedSizeUnpackedArrayType>();
            const auto& elem = fsua.elementType;
            for (auto width = fsua.range.width(); width > 0; width--)
                buffer.emplace(unpackBitstream(elem, iter, bit, dynamicSize));
        }

        return constContainer(ct, buffer);
    }

    if (type.isUnpackedStruct()) {
        SmallVectorSized<ConstantValue, 16> buffer;
        const auto& ct = type.getCanonicalType();
        for (auto& field : ct.as<UnpackedStructType>().membersOfType<FieldSymbol>())
            buffer.emplace(unpackBitstream(field.getType(), iter, bit, dynamicSize));

        return constContainer(ct, buffer);
    }

    // TODO: classes
    return nullptr;
}

} // namespace slang
