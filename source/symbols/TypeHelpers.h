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

/// Model dynamic size of a type with aR+b where a and b are compile-time constants and R is runtime
/// determined.
static std::pair<bitwidth_t, bitwidth_t> linearCoefficients(const Type& type,
                                                            unsigned int destination = 0) {
    /* IEEE standard says for dynamic-sized types:
     // runtime check
     struct {bit a[$]; shortint b;} a = {{1,2,3,4}, 67};
     int b = int'(a);
     // compile time error
     typedef struct {byte a[$]; bit b;} dest_t;
     int a;
     dest_t b = dest_t'(a);
     */
    auto width = type.getBitWidth();
    if (width > 0)
        return { 0, width };
    if (type.isString())
        return { destination == 1 ? 0 : CHAR_BIT, 0 };
    bitwidth_t gcd = 0;
    // TODO: check for overflow
    if (type.isUnpackedArray()) {
        auto [gcd1, width1] = linearCoefficients(*type.getArrayElementType(), destination);
        const auto& ct = type.getCanonicalType();
        if (ct.kind == SymbolKind::FixedSizeUnpackedArrayType) {
            auto rw = ct.as<FixedSizeUnpackedArrayType>().range.width();
            gcd = gcd1 * rw;
            width = width1 * rw;
        }
        else if (destination) {
            if (destination > 1) {
                if (!gcd1)
                    gcd = width1;
                else {
                    gcd = gcd1;
                    width = width1;
                }
            }
        }
        else
            gcd = std::gcd(gcd1, width1);
    }
    else if (type.isUnpackedStruct()) {
        auto& us = type.getCanonicalType().as<UnpackedStructType>();
        for (auto& field : us.membersOfType<FieldSymbol>()) {
            auto [gcd1, width1] = linearCoefficients(field.getType(), destination);
            if (destination > 1 && gcd1 > 0)
                destination--;
            gcd = std::gcd(gcd, gcd1);
            width += width1;
        }
    }
    // TODO: classes
    return { gcd, width };
}

static ConstantValue constContainer(const Type& type, span<const ConstantValue> elems) {
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
                            bitwidth_t& dynamic) {

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
        if (!dynamic)
            return std::string();
        auto width = dynamic;
        ASSERT(width % CHAR_BIT == 0);
        dynamic = 0;
        return ConstantValue(concatPacked(width, false)).convertToStr();
    }

    if (type.isUnpackedArray()) {
        const auto& ct = type.getCanonicalType();
        SmallVectorSized<ConstantValue, 16> buffer;
        if (ct.kind != SymbolKind::FixedSizeUnpackedArrayType) {
            // dynamic is the remaining size: For unbounded dynamically sized types, the conversion
            // process is greedy: adjust the size of the first dynamically sized item in the
            // destination to the remaining size; any remaining dynamically sized items are left
            // empty.
            if (dynamic > 0) {
                auto elemWidth = type.getArrayElementType()->bitstreamWidth();
                if (!elemWidth)
                    elemWidth = dynamic;
                ASSERT(dynamic % elemWidth == 0);
                for (auto i = dynamic / elemWidth; i > 0; i--)
                    buffer.emplace(unpack(*type.getArrayElementType(), iter, bit, dynamic));
                ASSERT(!dynamic || type.getArrayElementType()->isFixedSize());
                dynamic = 0;
            }
        }
        else {
            const auto& ct1 = ct.as<FixedSizeUnpackedArrayType>();
            const auto& elem = ct1.elementType;
            for (auto width = ct1.range.width(); width > 0; width--)
                buffer.emplace(unpack(elem, iter, bit, dynamic));
        }
        return constContainer(ct, span<const ConstantValue>(buffer));
    }

    if (type.isUnpackedStruct()) {
        SmallVectorSized<ConstantValue, 16> buffer;
        const auto& ct = type.getCanonicalType();
        auto& us = ct.as<UnpackedStructType>();
        for (auto& field : us.membersOfType<FieldSymbol>())
            buffer.emplace(unpack(field.getType(), iter, bit, dynamic));
        return constContainer(ct, span<const ConstantValue>(buffer));
    }

    // TODO: classes
    return nullptr;
}

} // namespace slang
