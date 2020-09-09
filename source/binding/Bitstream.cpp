//------------------------------------------------------------------------------
// Bitstream.cpp
// Helpers for implementing bit-stream casting and streaming operators
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/Bitstream.h"

#include <numeric>

#include "slang/binding/OperatorExpressions.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
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
static std::pair<std::size_t, std::size_t> dynamicBitstreamSize(const Type& type,
                                                                BitstreamSizeMode mode) {
    std::size_t fixedSize = type.getBitWidth();
    if (fixedSize > 0)
        return { 0, fixedSize };

    if (type.isString())
        return { mode == BitstreamSizeMode::DestEmpty ? 0 : CHAR_BIT, 0 };

    // TODO: check for overflow
    std::size_t multiplier = 0;
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

static std::pair<std::size_t, std::size_t> dynamicBitstreamSize(
    const StreamingConcatenationExpression& concat, BitstreamSizeMode mode) {
    if (concat.isFixedSize())
        return { 0, concat.bitstreamWidth() };

    std::size_t multiplier = 0, fixedSize = 0;
    for (auto stream : concat.streams()) {
        auto [multiplierElem, fixedSizeElem] =
            stream->kind == ExpressionKind::Streaming
                ? dynamicBitstreamSize(stream->as<StreamingConcatenationExpression>(), mode)
                : dynamicBitstreamSize(*stream->type, mode);
        if (mode == BitstreamSizeMode::DestFill && multiplierElem > 0)
            mode = BitstreamSizeMode::DestEmpty;
        multiplier = std::gcd(multiplier, multiplierElem);
        fixedSize += fixedSizeElem;
    }

    return { multiplier, fixedSize };
}

template bool Bitstream::dynamicSizesMatch(const Type&, const Type&);
template bool Bitstream::dynamicSizesMatch(const StreamingConcatenationExpression&,
                                           const StreamingConcatenationExpression&);
template bool Bitstream::dynamicSizesMatch(const Type&, const StreamingConcatenationExpression&);

template<typename T1, typename T2>
bool Bitstream::dynamicSizesMatch(const T1& destination, const T2& source) {
    auto [sourceMultiplier, sourceFixedSize] =
        dynamicBitstreamSize(source, BitstreamSizeMode::Source);
    auto [destEmptyMultiplier, destEmptyFixedSize] =
        dynamicBitstreamSize(destination, BitstreamSizeMode::DestEmpty);
    ASSERT(!destEmptyMultiplier && !sourceMultiplier == source.isFixedSize());

    if (destEmptyFixedSize >= sourceFixedSize) {
        auto diff = destEmptyFixedSize - sourceFixedSize;
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

    std::size_t remaining;
    if (sourceFixedSize > destFillFixedSize)
        remaining = sourceFixedSize - destFillFixedSize;
    else
        remaining = destFillFixedSize - sourceFixedSize;

    return remaining % std::gcd(sourceMultiplier, destFillMultiplier) == 0;
}

/// Validates sizes and returns remaining size for the first dynamic item in constant evaluation
template<typename T>
static std::size_t bitstreamCastRemainingSize(const T& destination, std::size_t srcSize) {
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

static SVInt slicePacked(PackIterator& iter, const PackIterator iterEnd, bitwidth_t& bit,
                         bitwidth_t width) {
    const ConstantValue* cp;
    while (true) {
        if (iter == iterEnd)
            return SVInt(width, 0, false); // Only for implicit streaming concatenation conversion
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
static ConstantValue unpackBitstream(const Type& type, PackIterator& iter,
                                     const PackIterator iterEnd, bitwidth_t& bit,
                                     std::size_t& dynamicSize) {

    auto concatPacked = [&](bitwidth_t width, bool isFourState) {
        SmallVectorSized<SVInt, 8> buffer;
        while (width > 0) {
            auto ci = slicePacked(iter, iterEnd, bit, width);
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

        // For bit-stream casting, (dynamicSize % CHAR_BIT) == 0 and width = dynamicSize
        // For implicit streaming concatenation conversion, width is the smallest multiple of
        // CHAR_BIT greater than or equal to dynamicSize
        auto width = static_cast<bitwidth_t>((dynamicSize + CHAR_BIT - 1) / CHAR_BIT * CHAR_BIT);
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
                auto elemWidth = type.getArrayElementType()->isFixedSize()
                                     ? type.getArrayElementType()->bitstreamWidth()
                                     : dynamicSize;

                auto num = (dynamicSize + elemWidth - 1) / elemWidth;
                // If element is dynamically sized, num = 1
                // For bit-stream casting, dynamicSize % elemWidth == 0 and num = dynamicSize /
                // elemWidth For implicit streaming concatenation conversion, num is the smallest
                // number of elements that make it as wide as or wider than dynamicSize
                for (auto i = num; i > 0; i--) {
                    buffer.emplace(unpackBitstream(*type.getArrayElementType(), iter, iterEnd, bit,
                                                   dynamicSize));
                }

                ASSERT(!dynamicSize || type.getArrayElementType()->isFixedSize());
                dynamicSize = 0;
            }
        }
        else {
            const auto& fsua = ct.as<FixedSizeUnpackedArrayType>();
            const auto& elem = fsua.elementType;
            for (auto width = fsua.range.width(); width > 0; width--)
                buffer.emplace(unpackBitstream(elem, iter, iterEnd, bit, dynamicSize));
        }

        return constContainer(ct, buffer);
    }

    if (type.isUnpackedStruct()) {
        SmallVectorSized<ConstantValue, 16> buffer;
        const auto& ct = type.getCanonicalType();
        for (auto& field : ct.as<UnpackedStructType>().membersOfType<FieldSymbol>())
            buffer.emplace(unpackBitstream(field.getType(), iter, iterEnd, bit, dynamicSize));

        return constContainer(ct, buffer);
    }

    // TODO: classes
    return nullptr;
}

ConstantValue Bitstream::evaluateCast(const Type& type, const ConstantValue& value,
                                      SourceRange sourceRange, EvalContext& context,
                                      bool isImplicit) {
    auto srcSize = value.bitstreamWidth();
    std::size_t dynamicSize = 0;
    if (!isImplicit) { // Explicit bit-stream casting
        dynamicSize = bitstreamCastRemainingSize(type, srcSize);
        if (dynamicSize > srcSize) {
            context.addDiag(diag::ConstEvalBitstreamCastSize, sourceRange)
                << value.bitstreamWidth() << type;
            return nullptr;
        }
    }
    else { // implicit streaming concatenation conversion
        auto targetWidth = type.bitstreamWidth();
        if (targetWidth < srcSize) {
            if (type.isFixedSize()) {
                context.addDiag(diag::BadStreamSize, sourceRange) << targetWidth << srcSize;
                return nullptr;
            }
            dynamicSize = srcSize - targetWidth;
        }
    }

    SmallVectorSized<const ConstantValue*, 8> packed;
    packBitstream(value, packed);

    bitwidth_t bitOffset = 0;
    auto iter = packed.cbegin();
    auto cv = unpackBitstream(type, iter, packed.cend(), bitOffset, dynamicSize);
    ASSERT(!dynamicSize);
    if (isImplicit && iter == packed.cend())
        ASSERT(bitOffset == 0);
    else {
        ASSERT(bitOffset == ((*iter)->isInteger() ? (*iter)->integer().getBitWidth()
                                                  : (*iter)->str().length() * CHAR_BIT));
        ASSERT(iter != packed.cend() && ++iter == packed.cend());
    }
    return cv;
}

bool Bitstream::canBeTarget(const StreamingConcatenationExpression& lhs, const Expression& rhs,
                            const BindContext& context) {
    if (rhs.kind != ExpressionKind::Streaming && !rhs.type->isBitstreamType()) {
        context.addDiag(diag::BadStreamType, rhs.sourceRange) << std::string("source") << *rhs.type;
        return false;
    }

    auto targetWidth = lhs.as<StreamingConcatenationExpression>().bitstreamWidth();
    decltype(targetWidth) sourceWidth;
    bool good = true;

    if (rhs.kind != ExpressionKind::Streaming) {
        if (!rhs.type->isFixedSize())
            return true; // Sizes checked at constant evaluation or runtime
        sourceWidth = rhs.type->bitstreamWidth();
        good = targetWidth <= sourceWidth;
    }
    else {
        auto source = rhs.as<StreamingConcatenationExpression>();
        sourceWidth = source.bitstreamWidth();
        if (lhs.isFixedSize() && source.isFixedSize())
            good = targetWidth == sourceWidth;
        else
            good = dynamicSizesMatch(lhs, source);
    }

    if (!good)
        context.addDiag(diag::BadStreamSize, lhs.sourceRange) << targetWidth << sourceWidth;
    return good;
}

bool Bitstream::canBeSource(const Type& target, const StreamingConcatenationExpression& rhs,
                            const BindContext& context) {
    if (!target.isBitstreamType(true)) {
        context.addDiag(diag::BadStreamType, rhs.sourceRange) << std::string("target") << target;
        return false;
    }

    if (!target.isFixedSize())
        return true; // Sizes checked at constant evaluation or runtime
    auto targetWidth = target.bitstreamWidth();
    auto sourceWidth = rhs.bitstreamWidth();
    if (targetWidth < sourceWidth) {
        context.addDiag(diag::BadStreamSize, rhs.sourceRange) << targetWidth << sourceWidth;
        return false;
    }

    return true;
}

bool Bitstream::isBitstreamCast(const Type& type, const StreamingConcatenationExpression& arg) {
    if (!type.isBitstreamType(true))
        return false;
    if (type.isFixedSize() && arg.isFixedSize())
        return type.bitstreamWidth() == arg.bitstreamWidth();
    else
        return dynamicSizesMatch(type, arg);
}

ConstantValue Bitstream::reOrder(ConstantValue&& values, std::size_t sliceSize,
                                 std::size_t unpackWidth) {
    std::size_t totalWidth = values.bitstreamWidth();
    ASSERT(unpackWidth <= totalWidth);
    auto numBlocks = ((unpackWidth ? unpackWidth : totalWidth) + sliceSize - 1) / sliceSize;
    if (numBlocks <= 1)
        return std::move(values);

    auto getWidth = [](const ConstantValue& v) {
        if (v.isInteger())
            return v.integer().getBitWidth();
        else
            return static_cast<bitwidth_t>(v.str().length() * CHAR_BIT);
    };

    SmallVectorSized<const ConstantValue*, 8> packed;
    packBitstream(values, packed);

    auto rightIndex = packed.size() - 1; // Right-to-left
    bitwidth_t rightWidth = getWidth(*packed.back());
    std::size_t extraBits = 0;
    if (unpackWidth) {
        if (unpackWidth < totalWidth) { // left-aligned so trim rightmost
            auto trimWidth = totalWidth - unpackWidth;
            while (trimWidth >= rightWidth) {
                rightIndex--;
                trimWidth -= rightWidth;
                rightWidth = getWidth(*packed[rightIndex]);
            }
            rightWidth -= trimWidth;
        }
        // For unpack, extraBits is for the first block
        // For pack, extraBits is for the last block
        extraBits = unpackWidth % sliceSize;
    }

    SmallVectorSized<ConstantValue, 8> result;
    result.reserve(std::max(packed.size(), numBlocks));
    auto sliceOrAppend = [&](PackIterator iter) {
        if (rightWidth == getWidth(**iter))
            result.append(**iter);
        else {
            bitwidth_t bit = 0;
            result.append(slicePacked(iter, packed.cend(), bit, rightWidth));
        }
    };

    while (numBlocks > 1) {
        auto index = rightIndex;
        auto width = rightWidth;
        auto slice = sliceSize;
        if (extraBits) {
            slice = extraBits;
            extraBits = 0;
        }
        while (slice >= width) {
            index--;
            slice -= width;
            width = getWidth(*packed[index]);
        }

        // A block composed of bits from the last "slice" bits of packed[index] to the first
        // "rightWidth" bits of packed[rightIndex]
        auto iter = packed.cbegin() + index;
        if (slice) {
            bitwidth_t bit = static_cast<bitwidth_t>(width - slice);
            result.append(slicePacked(iter, packed.cend(), bit, static_cast<bitwidth_t>(slice)));
            width -= slice;
        }
        iter++;
        auto nextIndex = index;
        while (++index < rightIndex)
            result.append(**iter++);
        if (index == rightIndex)
            sliceOrAppend(iter);
        rightIndex = nextIndex;
        rightWidth = width;
        numBlocks--;
    }

    // For pack, the last block may be smaller than slice size
    auto iter = packed.cbegin();
    for (std::size_t i = 0; i < rightIndex; i++)
        result.append(**iter++);
    sliceOrAppend(iter);

    return std::vector(result.begin(), result.end());
}

/// Performs unpack operation of streaming concatenation target on a bit-stream.
static bool unpackConcatenation(const StreamingConcatenationExpression& lhs, PackIterator& iter,
                                const PackIterator iterEnd, bitwidth_t& bitOffset,
                                std::size_t& dynamicSize, EvalContext& context,
                                SmallVector<ConstantValue>* dryRun = nullptr) {
    for (auto stream : lhs.streams()) {
        if (stream->kind == ExpressionKind::Streaming) {
            auto concat = stream->as<StreamingConcatenationExpression>();
            if (dryRun || !concat.sliceSize) {
                if (!unpackConcatenation(stream->as<StreamingConcatenationExpression>(), iter,
                                         iterEnd, bitOffset, dynamicSize, context, dryRun))
                    return false;
            }

            // A dry run collects rvalue without storing lvalue
            auto dynamicSizeSave = dynamicSize;
            SmallVectorSized<ConstantValue, 8> toBeOrdered;
            if (!unpackConcatenation(stream->as<StreamingConcatenationExpression>(), iter, iterEnd,
                                     bitOffset, dynamicSize, context, &toBeOrdered))
                return false;

            // Re-order to a new rvalue with the slice size
            ConstantValue cv = std::vector(toBeOrdered.begin(), toBeOrdered.end());
            auto rvalue = Bitstream::reOrder(std::move(cv), concat.sliceSize, cv.bitstreamWidth());
            SmallVectorSized<const ConstantValue*, 8> packed;
            packBitstream(rvalue, packed);

            // A real pass stores lvalue from new rvalue
            auto iterConcat = packed.cbegin();
            bitwidth_t bit = 0;
            if (!unpackConcatenation(concat, iterConcat, packed.cend(), bit, dynamicSizeSave,
                                     context))
                return false;
            ASSERT(dynamicSizeSave == dynamicSize);
            ASSERT(bit == (*iterConcat)->integer().getBitWidth());
            ASSERT(iterConcat != packed.cend() && ++iterConcat == packed.cend());
        }
        else {
            auto rvalue = unpackBitstream(*stream->type, iter, iterEnd, bitOffset, dynamicSize);
            if (dryRun)
                dryRun->append(rvalue);
            else {
                LValue lvalue = stream->evalLValue(context);
                if (!lvalue)
                    return false;
                lvalue.store(rvalue);
            }
        }
    }
    return true;
}

ConstantValue Bitstream::evaluateTarget(const StreamingConcatenationExpression& lhs,
                                        const Expression& rhs, EvalContext& context) {

    ConstantValue rvalue = rhs.eval(context);
    if (!rvalue)
        return nullptr;

    auto srcSize = rvalue.bitstreamWidth();
    auto targetWidth = lhs.bitstreamWidth();
    std::size_t dynamicSize = 0;
    if (rhs.kind == ExpressionKind::Streaming) { // srcSize == targetWidth + dynamicSize
        dynamicSize = bitstreamCastRemainingSize(lhs, srcSize);
        if (dynamicSize > srcSize) {
            context.addDiag(diag::BadStreamSize, lhs.sourceRange)
                << lhs.bitstreamWidth() << srcSize;
            return nullptr;
        }
    }
    else { // srcSize >= targetWidth + dynamicSize
        if (targetWidth > srcSize) {
            context.addDiag(diag::BadStreamSize, lhs.sourceRange) << targetWidth << srcSize;
            return nullptr;
        }
        else if (!lhs.isFixedSize()) {
            dynamicSize = srcSize - targetWidth;
            auto [firstDynamicElemSize, doNotUse] =
                dynamicBitstreamSize(lhs, BitstreamSizeMode::DestFill);
            dynamicSize -= dynamicSize % firstDynamicElemSize; // do not exceed srcSize
        }
    }

    if (lhs.sliceSize > 0)
        rvalue = reOrder(std::move(rvalue), lhs.sliceSize, targetWidth + dynamicSize);

    SmallVectorSized<const ConstantValue*, 8> packed;
    packBitstream(rvalue, packed);

    bitwidth_t bitOffset = 0;
    auto iter = packed.cbegin();
    if (!unpackConcatenation(lhs, iter, packed.cend(), bitOffset, dynamicSize, context))
        return nullptr;
    return rvalue;
}

} // namespace slang
