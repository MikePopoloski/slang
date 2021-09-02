//------------------------------------------------------------------------------
// Bitstream.cpp
// Helpers for implementing bit-stream casting and streaming operators
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/Bitstream.h"

#include "../text/FormatBuffer.h"
#include <numeric>

#include "slang/binding/SelectExpressions.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/types/AllTypes.h"

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
static std::pair<size_t, size_t> dynamicBitstreamSize(const Type& type, BitstreamSizeMode mode) {
    size_t fixedSize = type.getBitWidth();
    if (fixedSize > 0)
        return { 0, fixedSize };

    if (type.isString())
        return { mode == BitstreamSizeMode::DestEmpty ? 0 : CHAR_BIT, 0 };

    // TODO: check for overflow
    size_t multiplier = 0;
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
    else if (type.isClass()) {
        auto& ct = type.getCanonicalType().as<ClassType>();
        for (auto& prop : ct.membersOfType<ClassPropertySymbol>()) {
            auto [multiplierElem, fixedSizeElem] = dynamicBitstreamSize(prop.getType(), mode);
            multiplier = std::gcd(multiplier, multiplierElem);
            fixedSize += fixedSizeElem;
        }
    }

    return { multiplier, fixedSize };
}

static std::pair<size_t, size_t> dynamicBitstreamSize(
    const StreamingConcatenationExpression& concat, BitstreamSizeMode mode) {
    if (concat.isFixedSize())
        return { 0, concat.bitstreamWidth() };

    size_t multiplier = 0, fixedSize = 0;
    for (auto stream : concat.streams()) {
        auto& operand = *stream->operand;
        size_t multiplierStream = 0, fixedSizeStream = 0;

        if (stream->with) {
            auto [multiplierElem, fixedSizeElem] =
                dynamicBitstreamSize(*operand.type->getArrayElementType(), mode);
            ASSERT(!multiplierElem);
            if (stream->with->width) {
                auto rw = static_cast<size_t>(*stream->with->width);
                multiplierStream = multiplierElem * rw;
                fixedSizeStream = fixedSizeElem * rw;
            }
            else {
                multiplierStream = fixedSizeElem;
                fixedSizeStream = fixedSizeElem;
            }
        }
        else {
            std::tie(multiplierStream, fixedSizeStream) =
                operand.kind == ExpressionKind::Streaming
                    ? dynamicBitstreamSize(operand.as<StreamingConcatenationExpression>(), mode)
                    : dynamicBitstreamSize(*operand.type, mode);
            if (mode == BitstreamSizeMode::DestFill && multiplierStream > 0)
                mode = BitstreamSizeMode::DestEmpty;
        }

        multiplier = std::gcd(multiplier, multiplierStream);
        fixedSize += fixedSizeStream;
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

    if (destEmptyFixedSize >= sourceFixedSize) {
        auto diff = destEmptyFixedSize - sourceFixedSize;
        if (!sourceMultiplier)
            return diff == 0;
        if (diff % sourceMultiplier == 0)
            return true;
    }

    if (destEmptyMultiplier > 0) { // only for "with" range
        auto diff = destEmptyFixedSize > sourceFixedSize ? destEmptyFixedSize - sourceFixedSize
                                                         : sourceFixedSize - destEmptyFixedSize;
        if (diff % std::gcd(sourceMultiplier, destEmptyMultiplier) == 0)
            return true;
    }

    auto [destFillMultiplier, destFillFixedSize] =
        dynamicBitstreamSize(destination, BitstreamSizeMode::DestFill);

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

    size_t remaining;
    if (sourceFixedSize > destFillFixedSize)
        remaining = sourceFixedSize - destFillFixedSize;
    else
        remaining = destFillFixedSize - sourceFixedSize;

    return remaining % std::gcd(sourceMultiplier, destFillMultiplier) == 0;
}

/// Validates sizes and returns remaining size for the first dynamic item in constant evaluation
template<typename T>
static size_t bitstreamCastRemainingSize(const T& destination, size_t srcSize) {
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
    if (srcSize < destFillFixedSize || (srcSize - destFillFixedSize) % destFillMultiplier != 0) {
        if (destEmptyMultiplier > 0 && (srcSize - destEmptyFixedSize) % destEmptyMultiplier == 0)
            return 0; // only for "with" range
        return srcSize + 1;
    }

    // Size to fill the first dynamically sized item.
    return srcSize - destFillFixedSize;
}

/// Formats the width of a dynamically-sized bitstream to a formula like 8×n+3 in an error message
template<typename T>
static std::string formatWidth(const T& bitstream, BitstreamSizeMode mode) {
    FormatBuffer buffer;
    auto [multiplier, fixedSize] = dynamicBitstreamSize(bitstream, mode);
    if (!multiplier)
        buffer.format("{}", fixedSize);
    else if (!fixedSize)
        buffer.format("{}*n", multiplier);
    else
        buffer.format("{}*n+{}", multiplier, fixedSize);
    return buffer.str();
}

static ConstantValue constContainer(const Type& type, span<ConstantValue> elems) {
    auto& ct = type.getCanonicalType();
    switch (ct.kind) {
        case SymbolKind::FixedSizeUnpackedArrayType:
        case SymbolKind::DynamicArrayType:
        case SymbolKind::UnpackedStructType:
            return ConstantValue::Elements(elems.cbegin(), elems.cend());
        case SymbolKind::QueueType: {
            SVQueue result(elems.cbegin(), elems.cend());
            result.maxBound = ct.as<QueueType>().maxBound;
            result.resizeToBound();
            return result;
        }
        default:
            THROW_UNREACHABLE;
    }
}

/// Performs pack operation to create a bit-stream.
static void packBitstream(ConstantValue& value, SmallVector<ConstantValue*>& packed) {
    if (value.isInteger()) {
        packed.append(&value);
    }
    else if (value.isString()) {
        if (!value.str().empty())
            packed.append(&value);
    }
    else if (value.isUnpacked()) {
        for (auto& cv : value.elements())
            packBitstream(cv, packed);
    }
    else if (value.isMap()) {
        for (auto& kv : *value.map()) {
            packBitstream(kv.second, packed);
        }
    }
    else if (value.isQueue()) {
        for (auto& cv : *value.queue())
            packBitstream(cv, packed);
    }
    else if (value.isUnion()) {
        packBitstream(value.unionVal()->value, packed);
    }
}

using PackIterator = ConstantValue* const*;

static SVInt slicePacked(PackIterator& iter, const PackIterator iterEnd, bitwidth_t& bit,
                         bitwidth_t width) {
    if (iter == iterEnd) {
        // Only for implicit streaming concatenation conversion
        bit += width;                  // Informs the caller how many zeros are appended.
        return SVInt(width, 0, false); // filling with zero bits on the right
    }

    ConstantValue cp = **iter;
    if (cp.isString())
        cp = cp.convertToInt();

    auto& ci = cp.integer();
    ASSERT(bit < ci.getBitWidth());
    bitwidth_t msb = ci.getBitWidth() - bit - 1;
    bitwidth_t lsb = std::min(bit + width, ci.getBitWidth());
    lsb = ci.getBitWidth() - lsb;
    bit += msb - lsb + 1;

    ASSERT(bit <= ci.getBitWidth());
    if (bit == ci.getBitWidth()) {
        iter++;
        bit = 0;
    }

    if (lsb == 0 && msb == ci.getBitWidth() - 1)
        return std::move(ci);

    return ci.slice(static_cast<int32_t>(msb), static_cast<int32_t>(lsb));
}

/// Performs unpack operation on a bit-stream.
static ConstantValue unpackBitstream(const Type& type, PackIterator& iter,
                                     const PackIterator iterEnd, bitwidth_t& bit,
                                     size_t& dynamicSize) {

    auto concatPacked = [&](bitwidth_t width, bool isFourState) {
        SmallVectorSized<SVInt, 8> buffer;
        while (width > 0) {
            auto ci = slicePacked(iter, iterEnd, bit, width);
            ASSERT(ci.getBitWidth() <= width);
            width -= ci.getBitWidth();
            if (!isFourState)
                ci.flattenUnknowns();

            buffer.emplace(std::move(ci));
        }

        ASSERT(!buffer.empty());
        if (buffer.size() == 1)
            return buffer.front();

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

        // For bit-stream casting, (dynamicSize % CHAR_BIT) == 0 and width == dynamicSize.
        // For implicit streaming concatenation conversion, width is the smallest multiple of
        // CHAR_BIT greater than or equal to dynamicSize.
        auto width = static_cast<bitwidth_t>((dynamicSize + CHAR_BIT - 1) / CHAR_BIT);
        dynamicSize = 0;
        if (!bit && iter != iterEnd && (*iter)->isString() && (*iter)->str().length() == width)
            return std::move(**iter);

        return ConstantValue(concatPacked(width * CHAR_BIT, false)).convertToStr();
    }

    if (type.isUnpackedArray()) {
        auto& ct = type.getCanonicalType();
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

                // If element is dynamically sized, num = 1
                // For bit-stream casting, dynamicSize % elemWidth == 0 and num = dynamicSize /
                // elemWidth For implicit streaming concatenation conversion, num is the smallest
                // number of elements that make it as wide as or wider than dynamicSize
                size_t num = (dynamicSize + elemWidth - 1) / elemWidth;
                for (size_t i = num; i > 0; i--) {
                    buffer.emplace(unpackBitstream(*type.getArrayElementType(), iter, iterEnd, bit,
                                                   dynamicSize));
                }

                ASSERT(!dynamicSize || type.getArrayElementType()->isFixedSize());
                dynamicSize = 0;
            }
        }
        else {
            auto& fsua = ct.as<FixedSizeUnpackedArrayType>();
            auto& elem = fsua.elementType;
            for (auto width = fsua.range.width(); width > 0; width--)
                buffer.emplace(unpackBitstream(elem, iter, iterEnd, bit, dynamicSize));
        }

        return constContainer(ct, buffer);
    }

    if (type.isUnpackedStruct()) {
        SmallVectorSized<ConstantValue, 16> buffer;
        auto& ct = type.getCanonicalType();
        for (auto& field : ct.as<UnpackedStructType>().membersOfType<FieldSymbol>())
            buffer.emplace(unpackBitstream(field.getType(), iter, iterEnd, bit, dynamicSize));

        return constContainer(ct, buffer);
    }

    return nullptr;
}

ConstantValue Bitstream::evaluateCast(const Type& type, ConstantValue&& value,
                                      SourceRange sourceRange, EvalContext& context,
                                      bool isImplicit) {
    auto srcSize = value.bitstreamWidth();
    size_t dynamicSize = 0;
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

    SmallVectorSized<ConstantValue*, 8> packed;
    packBitstream(value, packed);

    bitwidth_t bitOffset = 0;
    auto iter = packed.cbegin();
    auto cv = unpackBitstream(type, iter, packed.cend(), bitOffset, dynamicSize);
    ASSERT(!dynamicSize);
    ASSERT(isImplicit || (iter == packed.cend() && !bitOffset));
    return cv;
}

static bool withAfterDynamic(const StreamingConcatenationExpression& lhs,
                             const SourceRange*& dynamic, const SourceRange*& with) {
    // The expression within the "with" is evaluated immediately before its corresponding array is
    // streamed. The first dynamically sized item without "with" constraints accept all the
    // available data. If the former appears after the latter, evaluation order has conflict.
    for (auto stream : lhs.streams()) {
        auto& operand = *stream->operand;
        if (operand.kind == ExpressionKind::Streaming) {
            if (withAfterDynamic(operand.as<StreamingConcatenationExpression>(), dynamic, with))
                return true;
        }
        else if (stream->with) {
            with = &stream->with->left->sourceRange;
            if (dynamic)
                return true;
        }
        else if (!dynamic && !operand.type->isFixedSize()) {
            dynamic = &operand.sourceRange;
        }
    }
    return false;
}

bool Bitstream::canBeTarget(const StreamingConcatenationExpression& lhs, const Expression& rhs,
                            SourceLocation assignLoc, const BindContext& context) {
    if (rhs.kind != ExpressionKind::Streaming && !rhs.type->isBitstreamType()) {
        context.addDiag(diag::BadStreamSourceType, assignLoc) << *rhs.type << lhs.sourceRange;
        return false;
    }

    const SourceRange *dynamic = nullptr, *with = nullptr;
    if (withAfterDynamic(lhs, dynamic, with)) {
        context.addDiag(diag::BadStreamWithOrder, *with) << *dynamic;
        return false;
    }

    if (context.inUnevaluatedBranch())
        return true; // No size check in an unevaluated conditional branch

    size_t targetWidth = lhs.bitstreamWidth();
    size_t sourceWidth;
    bool good = true;

    if (rhs.kind != ExpressionKind::Streaming) {
        if (!rhs.type->isFixedSize())
            return true; // Sizes checked at constant evaluation or runtime

        sourceWidth = rhs.type->bitstreamWidth();
        good = targetWidth <= sourceWidth;
    }
    else {
        auto& source = rhs.as<StreamingConcatenationExpression>();
        sourceWidth = source.bitstreamWidth();
        if (lhs.isFixedSize() && source.isFixedSize())
            good = targetWidth == sourceWidth;
        else
            good = dynamicSizesMatch(lhs, source);
    }

    if (!good) {
        auto& diag = context.addDiag(diag::BadStreamSize, assignLoc);
        if (rhs.kind != ExpressionKind::Streaming)
            diag << targetWidth << sourceWidth;
        else {
            diag << formatWidth(lhs, BitstreamSizeMode::DestFill)
                 << formatWidth(rhs.as<StreamingConcatenationExpression>(),
                                BitstreamSizeMode::Source);
        }

        diag << lhs.sourceRange;
        if (rhs.kind == ExpressionKind::Streaming)
            diag << rhs.sourceRange;
    }

    return good;
}

bool Bitstream::canBeSource(const Type& target, const StreamingConcatenationExpression& rhs,
                            SourceLocation assignLoc, const BindContext& context) {
    if (!target.isBitstreamType(true)) {
        context.addDiag(diag::BadStreamTargetType, assignLoc) << target << rhs.sourceRange;
        return false;
    }

    if (context.inUnevaluatedBranch())
        return true; // No size check in an unevaluated conditional branch
    if (!target.isFixedSize())
        return true; // Sizes checked at constant evaluation or runtime

    auto targetWidth = target.bitstreamWidth();
    auto sourceWidth = rhs.bitstreamWidth();
    if (targetWidth < sourceWidth) {
        auto& diag = context.addDiag(diag::BadStreamSize, assignLoc) << targetWidth << sourceWidth;
        diag << rhs.sourceRange;
        return false;
    }

    return true;
}

bool Bitstream::isBitstreamCast(const Type& type, const StreamingConcatenationExpression& arg) {
    if (!type.isBitstreamType(true))
        return false;

    if (type.isFixedSize() && arg.isFixedSize())
        return type.bitstreamWidth() == arg.bitstreamWidth();

    return dynamicSizesMatch(type, arg);
}

ConstantValue Bitstream::reOrder(ConstantValue&& value, size_t sliceSize, size_t unpackWidth) {
    size_t totalWidth = value.bitstreamWidth();
    ASSERT(unpackWidth <= totalWidth);

    size_t numBlocks = ((unpackWidth ? unpackWidth : totalWidth) + sliceSize - 1) / sliceSize;
    if (numBlocks <= 1)
        return std::move(value);

    SmallVectorSized<ConstantValue*, 8> packed;
    packBitstream(value, packed);
    if (packed.empty())
        return std::move(value);

    size_t rightIndex = packed.size() - 1; // Right-to-left
    bitwidth_t rightWidth = static_cast<bitwidth_t>(packed.back()->bitstreamWidth());
    size_t extraBits = 0;

    if (unpackWidth) {
        if (unpackWidth < totalWidth) { // left-aligned so trim rightmost
            auto trimWidth = totalWidth - unpackWidth;
            while (trimWidth >= rightWidth) {
                rightIndex--;
                trimWidth -= rightWidth;
                rightWidth = static_cast<bitwidth_t>(packed[rightIndex]->bitstreamWidth());
            }
            rightWidth -= static_cast<bitwidth_t>(trimWidth);
        }

        // For unpack, extraBits is for the first block.
        // For pack, extraBits is for the last block.
        extraBits = unpackWidth % sliceSize;
    }

    std::vector<ConstantValue> result;
    result.reserve(std::max(packed.size(), numBlocks));
    auto sliceOrAppend = [&](PackIterator iter) {
        if (rightWidth == (*iter)->bitstreamWidth())
            result.emplace_back(std::move(**iter));
        else {
            bitwidth_t bit = 0;
            result.emplace_back(slicePacked(iter, packed.cend(), bit, rightWidth));
        }
    };

    while (numBlocks > 1) {
        size_t index = rightIndex;
        bitwidth_t width = rightWidth;
        size_t slice = sliceSize;
        if (extraBits) {
            slice = extraBits;
            extraBits = 0;
        }
        while (slice >= width) {
            index--;
            slice -= width;
            width = static_cast<bitwidth_t>(packed[index]->bitstreamWidth());
        }

        // A block composed of bits from the last "slice" bits of packed[index] to the first
        // "rightWidth" bits of packed[rightIndex].
        auto iter = packed.cbegin() + index;
        if (slice) {
            auto bit = static_cast<bitwidth_t>(width - slice);
            result.emplace_back(
                slicePacked(iter, packed.cend(), bit, static_cast<bitwidth_t>(slice)));
            width -= static_cast<bitwidth_t>(slice);
        }

        iter++;
        auto nextIndex = index;
        while (++index < rightIndex)
            result.emplace_back(std::move(**iter++));

        if (index == rightIndex)
            sliceOrAppend(iter);

        rightIndex = nextIndex;
        rightWidth = width;
        numBlocks--;
    }

    // For pack, the last block may be smaller than slice size.
    auto iter = packed.cbegin();
    for (size_t i = 0; i < rightIndex; i++)
        result.emplace_back(std::move(**iter++));
    sliceOrAppend(iter);

    return result;
}

/// Performs unpack operation of streaming concatenation target on a bit-stream.
static bool unpackConcatenation(const StreamingConcatenationExpression& lhs, PackIterator& iter,
                                const PackIterator iterEnd, bitwidth_t& bitOffset,
                                size_t& dynamicSize, EvalContext& context,
                                SmallVector<ConstantValue>* dryRun = nullptr) {
    for (auto stream : lhs.streams()) {
        auto& operand = *stream->operand;
        if (operand.kind == ExpressionKind::Streaming) {
            auto& concat = operand.as<StreamingConcatenationExpression>();
            if (dryRun || !concat.sliceSize) {
                if (!unpackConcatenation(concat, iter, iterEnd, bitOffset, dynamicSize, context,
                                         dryRun))
                    return false;
                continue;
            }

            // A dry run collects rvalue without storing lvalue
            size_t dynamicSizeSave = dynamicSize;
            SmallVectorSized<ConstantValue, 8> toBeOrdered;
            if (!unpackConcatenation(concat, iter, iterEnd, bitOffset, dynamicSize, context,
                                     &toBeOrdered)) {
                return false;
            }

            // Re-order to a new rvalue with the slice size
            ConstantValue cv = std::vector(toBeOrdered.begin(), toBeOrdered.end());
            auto rvalue = Bitstream::reOrder(std::move(cv), concat.sliceSize, cv.bitstreamWidth());

            SmallVectorSized<ConstantValue*, 8> packed;
            packBitstream(rvalue, packed);

            // A real pass stores lvalue from new rvalue
            auto iterConcat = packed.cbegin();
            bitwidth_t bit = 0;
            if (!unpackConcatenation(concat, iterConcat, packed.cend(), bit, dynamicSizeSave,
                                     context)) {
                return false;
            }

            ASSERT(dynamicSizeSave == dynamicSize);
            ASSERT(iterConcat == packed.cend() && !bit);
        }
        else {
            auto& arrayType = *operand.type;
            const Type* elemType = nullptr;
            ConstantRange with;
            ConstantValue rvalue;
            if (stream->with) {
                auto range = Bitstream::evaluateWith(arrayType, *stream->with, context);
                if (!range)
                    return false;

                with = *range;
                elemType = arrayType.getArrayElementType();
                ASSERT(elemType != nullptr);

                if (dynamicSize > 0 && !stream->with->width) {
                    auto withSize = elemType->bitstreamWidth() * with.width();
                    if (withSize >= dynamicSize)
                        dynamicSize = 0;
                    else
                        dynamicSize -= withSize;
                }

                if (with.left == with.right)
                    rvalue = unpackBitstream(*elemType, iter, iterEnd, bitOffset, dynamicSize);
                else {
                    rvalue = unpackBitstream(FixedSizeUnpackedArrayType(*elemType, with), iter,
                                             iterEnd, bitOffset, dynamicSize);
                }
            }
            else {
                rvalue = unpackBitstream(arrayType, iter, iterEnd, bitOffset, dynamicSize);
            }

            if (dryRun)
                dryRun->emplace(std::move(rvalue));
            else {
                LValue lvalue = operand.evalLValue(context);
                if (!lvalue)
                    return false;

                if (stream->with) {
                    if (with.left != with.right && arrayType.isQueue() && !rvalue.isQueue())
                        rvalue = constContainer(arrayType, rvalue.elements());

                    if (!arrayType.hasFixedRange()) {
                        // When the array is a variable-size array, it shall be resized to
                        // accommodate the range expression.
                        ASSERT(with.left <= with.right);
                        auto oldValue = lvalue.load();
                        if (oldValue.size() <= static_cast<uint32_t>(with.right)) {
                            auto newValue =
                                Bitstream::resizeToRange(std::move(oldValue), { 0, with.right },
                                                         elemType->getDefaultValue(), true);
                            lvalue.store(newValue);
                        }
                    }

                    if (with.left == with.right)
                        lvalue.addIndex(with.left, elemType->getDefaultValue());
                    else
                        lvalue.addArraySlice(with, elemType->getDefaultValue());
                }

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
    size_t dynamicSize = 0;

    if (rhs.kind == ExpressionKind::Streaming) {
        // Check srcSize == targetWidth + dynamicSize, then issue an error if not.
        dynamicSize = bitstreamCastRemainingSize(lhs, srcSize);
        if (dynamicSize > srcSize) {
            auto& diag = context.addDiag(diag::BadStreamSize, lhs.sourceRange);
            diag << formatWidth(lhs, BitstreamSizeMode::DestFill);
            diag << srcSize;
            return nullptr;
        }
    }
    else {
        // Check srcSize >= targetWidth + dynamicSize, then issue an error if not.
        if (targetWidth > srcSize) {
            context.addDiag(diag::BadStreamSize, lhs.sourceRange) << targetWidth << srcSize;
            return nullptr;
        }

        if (!lhs.isFixedSize()) {
            dynamicSize = srcSize - targetWidth;
            auto [firstDynamicElemSize, notUsed] =
                dynamicBitstreamSize(lhs, BitstreamSizeMode::DestFill);
            if (firstDynamicElemSize)
                dynamicSize -= dynamicSize % firstDynamicElemSize; // do not exceed srcSize
        }
    }

    if (lhs.sliceSize > 0)
        rvalue = reOrder(std::move(rvalue), lhs.sliceSize, targetWidth + dynamicSize);

    SmallVectorSized<ConstantValue*, 8> packed;
    packBitstream(rvalue, packed);

    bitwidth_t bitOffset = 0;
    auto iter = packed.cbegin();
    auto iterEnd = packed.cend();
    if (!unpackConcatenation(lhs, iter, iterEnd, bitOffset, dynamicSize, context))
        return nullptr;

    // (iter==iterEnd && !bitOffset) implies target and source have exactly the same size.
    if (iter == iterEnd) {
        ASSERT(dynamicSize == 0);
        if (bitOffset > 0) {
            // Target longer than source
            context.addDiag(diag::BadStreamSize, lhs.sourceRange) << srcSize + bitOffset << srcSize;
        }
    }
    else if (rhs.kind == ExpressionKind::Streaming) {
        // Target shorter than source; this is legal unless rhs is a streaming concatenation.
        ASSERT(srcSize >= (*iter)->bitstreamWidth());
        auto tSize = srcSize - (*iter++)->bitstreamWidth() + bitOffset;
        while (iter != iterEnd)
            tSize -= (*iter++)->bitstreamWidth();
        context.addDiag(diag::BadStreamSize, lhs.sourceRange) << tSize << srcSize;
    }

    return rvalue;
}

bool Bitstream::validStreamWithRange(const Type& arrayType, WithRangeKind kind,
                                     optional<int32_t> left, optional<int32_t> right,
                                     std::variant<const BindContext*, EvalContext*> context,
                                     SourceRange leftRange, SourceRange rightRange) {

    auto addDiag = [&](DiagCode code, SourceRange range) -> Diagnostic& {
        if (std::holds_alternative<const BindContext*>(context))
            return std::get<const BindContext*>(context)->addDiag(code, range);
        else
            return std::get<EvalContext*>(context)->addDiag(code, range);
    };

    auto validateIndex = [&](int32_t value, SourceRange range) {
        if (arrayType.hasFixedRange()) {
            // evaluate to values that lie within the bounds of a fixed-size array
            if (!arrayType.getFixedRange().containsPoint(value)) {
                addDiag(diag::IndexValueInvalid, range) << value << arrayType;
                return false;
            }
        }
        else if (value < 0) {
            // or to positive values for dynamic arrays or queues
            addDiag(diag::ValueMustBePositive, range);
            return false;
        }

        return true;
    };

    if (left) {
        if (!validateIndex(*left, leftRange))
            return false;
    }

    if (right) {
        SourceRange errorRange{ leftRange.start(), rightRange.end() };

        if (kind == WithRangeKind::IndexedUp || kind == WithRangeKind::IndexedDown) {
            // Reference RangeSelectExpression::fromSyntax for similar constraints of indexed
            // part-select
            if (*right <= 0) {
                addDiag(diag::ValueMustBePositive, rightRange);
                return false;
            }

            auto width = *right;
            if (arrayType.hasFixedRange() &&
                (bitwidth_t)width > arrayType.getFixedRange().width()) {
                addDiag(diag::RangeWidthTooLarge, rightRange) << width << arrayType;
                return false;
            }

            if (left && arrayType.hasFixedRange()) {
                auto selection = ConstantRange::getIndexedRange(
                    *left, width, arrayType.getFixedRange().isLittleEndian(),
                    kind == WithRangeKind::IndexedUp);

                auto bound = selection.right == *left ? selection.left : selection.right;
                if (!arrayType.getFixedRange().containsPoint(bound)) {
                    auto& diag = addDiag(diag::BadRangeExpression, errorRange);
                    diag << selection.left << selection.right;
                    diag << arrayType;
                    return false;
                }
            }
        }
        else {
            // Reference RangeSelectExpression::fromSyntax for similar constraints of simple
            // part-select
            if (!validateIndex(*right, rightRange))
                return false;

            if (left) {
                ConstantRange selection = { *left, *right };
                bool expectLittleEndian = false;
                if (arrayType.hasFixedRange())
                    expectLittleEndian = arrayType.getFixedRange().isLittleEndian();

                if (selection.width() > 1 && selection.isLittleEndian() != expectLittleEndian) {
                    auto& diag = addDiag(diag::SelectEndianMismatch, errorRange);
                    diag << arrayType;
                    return false;
                }
            }
        }
    }

    return true;
}

optional<int32_t> Bitstream::withRangeWidth(WithRangeKind kind, optional<int32_t> left,
                                            optional<int32_t> right) {
    if (kind == WithRangeKind::Bit)
        return 1;

    if (kind == WithRangeKind::IndexedUp || kind == WithRangeKind::IndexedDown)
        return right;

    if (left && right) {
        ConstantRange range = { *left, *right };
        return range.width();
    }

    return std::nullopt;
}

optional<ConstantRange> Bitstream::evaluateWith(
    const Type& arrayType, const StreamingConcatenationExpression::WithExpression& with,
    EvalContext& context) {

    auto evalInt = [&](const Expression& expr) -> optional<int32_t> {
        auto cs = expr.eval(context);
        if (!cs)
            return std::nullopt;

        auto index = cs.integer().as<int32_t>();
        if (!index)
            context.addDiag(diag::ConstEvalArrayIndexInvalid, expr.sourceRange) << cs << arrayType;

        return index;
    };

    auto cl = evalInt(*with.left);
    if (!cl)
        return std::nullopt;

    optional<int32_t> cr = std::nullopt;
    auto rightRange = with.left->sourceRange;
    if (with.right) {
        cr = evalInt(*with.right);
        if (!cr)
            return std::nullopt;

        rightRange = with.right->sourceRange;
    }

    if (!validStreamWithRange(arrayType, with.kind, cl, cr, &context, with.left->sourceRange,
                              rightRange)) {
        return std::nullopt;
    }

    if (!cr)
        cr = *cl;

    ConstantRange result = { *cl, *cr };
    if (with.kind == WithRangeKind::IndexedUp || with.kind == WithRangeKind::IndexedDown) {
        result = ConstantRange::getIndexedRange(
            result.left, result.right,
            arrayType.hasFixedRange() ? arrayType.getFixedRange().isLittleEndian() : false,
            with.kind == WithRangeKind::IndexedUp);
    }

    if (arrayType.hasFixedRange()) {
        auto valueRange = arrayType.getFixedRange().reverse();
        result.left = valueRange.translateIndex(result.left);
        result.right = valueRange.translateIndex(result.right);
    }

    ASSERT(with.kind != WithRangeKind::Bit || result.left == result.right);
    ASSERT(result.left >= 0 && result.right >= 0);
    return result;
}

ConstantValue Bitstream::resizeToRange(ConstantValue&& value, ConstantRange range,
                                       ConstantValue defaultValue, bool keepArray) {
    if (range.left == range.right && !keepArray) {
        if (size_t(range.left) >= value.size())
            return defaultValue;
        else
            return std::move(value).at(size_t(range.left));
    }

    if (range.lower() > 0 || range.width() != value.size()) {
        auto upper = static_cast<uint32_t>(range.upper());
        auto lower = static_cast<uint32_t>(range.lower());
        auto size = static_cast<uint32_t>(value.size());
        auto more = upper >= size ? upper - size + 1 : 0;
        upper = std::min(upper + 1, size);

        if (value.isUnpacked()) {
            const auto old = value.elements();
            ConstantValue::Elements sliceValue;
            sliceValue.reserve(range.width());
            sliceValue.insert(sliceValue.end(), old.cbegin() + lower, old.cbegin() + upper);
            sliceValue.insert(sliceValue.end(), more, defaultValue);
            ASSERT(sliceValue.size() == range.width());
            return sliceValue;
        }
        else {
            ASSERT(value.isQueue());
            const auto& old = value.queue();
            SVQueue sliceValue(old->cbegin() + lower, old->cbegin() + upper);
            sliceValue.insert(sliceValue.end(), more, defaultValue);
            ASSERT(sliceValue.size() == range.width());
            return sliceValue;
        }
    }

    return std::move(value);
}

} // namespace slang
