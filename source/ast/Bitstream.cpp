//------------------------------------------------------------------------------
// Bitstream.cpp
// Helpers for implementing bit-stream casting and streaming operators
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Bitstream.h"

#include <numeric>

#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/numeric/MathUtils.h"
#include "slang/text/FormatBuffer.h"

namespace slang::ast {

enum class BitstreamSizeMode { Source, DestEmpty, DestFill };

/// Represents {a, b} to model the size of a dynamic type with "aR+b"
/// where "a" and "b" are compile-time constants and "R" is runtime determined.
struct DynamicSize {
    uint64_t multiplier = 0;
    uint64_t fixed = 0;
    bool isValid = false;

    DynamicSize() = default;
    DynamicSize(uint64_t multiplier, uint64_t fixed) :
        multiplier(multiplier), fixed(fixed), isValid(true) {}

    explicit operator bool() const { return isValid; }
};

/// Returns the dynamic size of the given type.
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
static DynamicSize dynamicBitstreamSize(const Type& type, BitstreamSizeMode mode) {
    uint64_t multiplier = 0;
    uint64_t fixedSize = type.getBitWidth();
    if (fixedSize > 0)
        return {0, fixedSize};

    if (type.isString())
        return {mode == BitstreamSizeMode::DestEmpty ? 0u : CHAR_BIT, 0u};

    auto handleField = [&](const ValueSymbol& field) {
        auto elemSize = dynamicBitstreamSize(field.getType(), mode);
        if (!elemSize)
            return false;

        // If a dynamically sized field is filled the rest should be empty.
        if (mode == BitstreamSizeMode::DestFill && elemSize.multiplier > 0)
            mode = BitstreamSizeMode::DestEmpty;

        multiplier = std::gcd(multiplier, elemSize.multiplier);
        fixedSize += elemSize.fixed;
        if (fixedSize > Type::MaxBitWidth)
            return false;

        return true;
    };

    if (type.isUnpackedArray()) {
        auto elemSize = dynamicBitstreamSize(*type.getArrayElementType(), mode);
        if (!elemSize)
            return elemSize;

        const auto& ct = type.getCanonicalType();
        if (ct.kind == SymbolKind::FixedSizeUnpackedArrayType) {
            auto rw = ct.as<FixedSizeUnpackedArrayType>().range.width();
            auto mul = checkedMulU64(elemSize.multiplier, rw);
            auto fixed = checkedMulU64(elemSize.fixed, rw);
            if (!mul || !fixed || mul > Type::MaxBitWidth || fixed > Type::MaxBitWidth)
                return {};

            multiplier = *mul;
            fixedSize = *fixed;
        }
        else if (mode == BitstreamSizeMode::DestFill) {
            if (!elemSize.multiplier) {
                multiplier = elemSize.fixed; // element is fixed size
            }
            else {
                multiplier = elemSize.multiplier; // element is dynamically sized
                fixedSize = elemSize.fixed;
            }
        }
        else if (mode == BitstreamSizeMode::Source) {
            multiplier = std::gcd(elemSize.multiplier, elemSize.fixed);
        }
    }
    else if (type.isUnpackedStruct()) {
        auto& us = type.getCanonicalType().as<UnpackedStructType>();
        for (auto field : us.fields) {
            if (!handleField(*field))
                return {};
        }
    }
    else if (type.isClass()) {
        auto& ct = type.getCanonicalType().as<ClassType>();
        SLANG_ASSERT(!ct.hasCycles());
        for (auto& prop : ct.membersOfType<ClassPropertySymbol>()) {
            if (!handleField(prop))
                return {};
        }
    }

    return {multiplier, fixedSize};
}

static DynamicSize dynamicBitstreamSize(const StreamingConcatenationExpression& concat,
                                        BitstreamSizeMode mode) {
    if (concat.isFixedSize())
        return {0, concat.getBitstreamWidth()};

    DynamicSize result;
    for (auto& stream : concat.streams()) {
        DynamicSize opSize;
        auto& operand = *stream.operand;

        if (stream.withExpr) {
            // With expression creation checks for a fixed size type so
            // we should always get a valid result here.
            opSize = dynamicBitstreamSize(*operand.type->getArrayElementType(), mode);
            SLANG_ASSERT(opSize);
            SLANG_ASSERT(!opSize.multiplier);

            if (stream.constantWithWidth) {
                // Overflow is checked at stream expression creation time.
                opSize.multiplier = 0;
                opSize.fixed *= *stream.constantWithWidth;
            }
            else {
                opSize.multiplier = opSize.fixed;
                opSize.fixed = 0;
            }
        }
        else {
            opSize = operand.kind == ExpressionKind::Streaming
                         ? dynamicBitstreamSize(operand.as<StreamingConcatenationExpression>(),
                                                mode)
                         : dynamicBitstreamSize(*operand.type, mode);
            if (!opSize)
                return opSize;

            if (mode == BitstreamSizeMode::DestFill && opSize.multiplier > 0)
                mode = BitstreamSizeMode::DestEmpty;
        }

        result.multiplier = std::gcd(result.multiplier, opSize.multiplier);
        result.fixed += opSize.fixed;
        result.isValid = true;

        if (result.fixed > Type::MaxBitWidth)
            return {};
    }

    return result;
}

template bool Bitstream::dynamicSizesMatch(const Type&, const Type&);
template bool Bitstream::dynamicSizesMatch(const StreamingConcatenationExpression&,
                                           const StreamingConcatenationExpression&);
template bool Bitstream::dynamicSizesMatch(const Type&, const StreamingConcatenationExpression&);

template<typename T1, typename T2>
bool Bitstream::dynamicSizesMatch(const T1& destination, const T2& source) {
    auto sourceSize = dynamicBitstreamSize(source, BitstreamSizeMode::Source);
    auto destEmpty = dynamicBitstreamSize(destination, BitstreamSizeMode::DestEmpty);
    if (!sourceSize || !destEmpty)
        return false;

    if (destEmpty.fixed >= sourceSize.fixed) {
        auto diff = destEmpty.fixed - sourceSize.fixed;
        if (!sourceSize.multiplier)
            return diff == 0;
        if (diff % sourceSize.multiplier == 0)
            return true;
    }

    if (destEmpty.multiplier > 0) { // only for "with" range
        auto diff = destEmpty.fixed > sourceSize.fixed ? destEmpty.fixed - sourceSize.fixed
                                                       : sourceSize.fixed - destEmpty.fixed;
        if (diff % std::gcd(sourceSize.multiplier, destEmpty.multiplier) == 0)
            return true;
    }

    auto destFill = dynamicBitstreamSize(destination, BitstreamSizeMode::DestFill);
    if (!destFill)
        return false;

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

    uint64_t remaining;
    if (sourceSize.fixed > destFill.fixed)
        remaining = sourceSize.fixed - destFill.fixed;
    else
        remaining = destFill.fixed - sourceSize.fixed;

    if (sourceSize.multiplier == 0 && destFill.multiplier == 0)
        return remaining == 0;

    return remaining % std::gcd(sourceSize.multiplier, destFill.multiplier) == 0;
}

/// Validates sizes and returns remaining size for the first dynamic item in constant evaluation
template<typename T>
static uint64_t bitstreamCastRemainingSize(const T& destination, uint64_t srcSize) {
    if (destination.isFixedSize()) {
        auto destSize = destination.getBitstreamWidth();
        if (destSize != srcSize)
            return UINT64_MAX;

        return 0;
    }

    // Check for the source size being too small to fill destination fixed size.
    auto destEmpty = dynamicBitstreamSize(destination, BitstreamSizeMode::DestEmpty);
    if (!destEmpty || destEmpty.fixed > srcSize)
        return UINT64_MAX;

    if (destEmpty.fixed == srcSize)
        return 0;

    // Calculate remaining size to dynamically fill.
    auto destFill = dynamicBitstreamSize(destination, BitstreamSizeMode::DestFill);
    if (!destFill)
        return UINT64_MAX;

    if (srcSize < destFill.fixed ||
        (destFill.multiplier > 0 && (srcSize - destFill.fixed) % destFill.multiplier != 0)) {
        if (destEmpty.multiplier > 0 && (srcSize - destEmpty.fixed) % destEmpty.multiplier == 0)
            return 0; // only for "with" range

        return UINT64_MAX;
    }

    // Size to fill the first dynamically sized item.
    return srcSize - destFill.fixed;
}

/// Formats the width of a dynamically-sized bitstream to a formula like 8×n+3 in an error message
template<typename T>
static std::string formatWidth(const T& bitstream, BitstreamSizeMode mode) {
    FormatBuffer buffer;
    auto size = dynamicBitstreamSize(bitstream, mode);
    if (!size)
        buffer.format("<overflow>");
    else if (!size.multiplier)
        buffer.format("{}", size.fixed);
    else if (!size.fixed)
        buffer.format("{}*n", size.multiplier);
    else
        buffer.format("{}*n+{}", size.multiplier, size.fixed);
    return buffer.str();
}

static ConstantValue constContainer(const Type& type, std::span<ConstantValue> elems) {
    auto& ct = type.getCanonicalType();
    switch (ct.kind) {
        case SymbolKind::FixedSizeUnpackedArrayType:
        case SymbolKind::DynamicArrayType:
        case SymbolKind::UnpackedStructType:
            return ConstantValue::Elements(elems.begin(), elems.end());
        case SymbolKind::QueueType: {
            SVQueue result(elems.begin(), elems.end());
            result.maxBound = ct.as<QueueType>().maxBound;
            result.resizeToBound();
            return result;
        }
        default:
            SLANG_UNREACHABLE;
    }
}

/// Performs pack operation to create a bit-stream.
static void packBitstream(ConstantValue& value, SmallVectorBase<ConstantValue*>& packed) {
    if (value.isInteger()) {
        packed.push_back(&value);
    }
    else if (value.isString()) {
        if (!value.str().empty())
            packed.push_back(&value);
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

static SVInt slicePacked(PackIterator& iter, const PackIterator iterEnd, uint64_t& bit,
                         uint64_t width) {
    if (iter == iterEnd) {
        // Only for implicit streaming concatenation conversion
        bit += width; // Informs the caller how many zeros are appended.
        return SVInt(bitwidth_t(width), 0, false); // filling with zero bits on the right
    }

    ConstantValue cp = **iter;
    if (cp.isString())
        cp = cp.convertToInt();

    auto& ci = cp.integer();
    SLANG_ASSERT(bit < ci.getBitWidth());
    uint64_t msb = ci.getBitWidth() - bit - 1;
    uint64_t lsb = std::min<uint64_t>(bit + width, ci.getBitWidth());
    lsb = ci.getBitWidth() - lsb;
    bit += msb - lsb + 1;

    SLANG_ASSERT(bit <= ci.getBitWidth());
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
                                     const PackIterator iterEnd, uint64_t& bit,
                                     uint64_t& dynamicSize) {

    auto concatPacked = [&](bitwidth_t width, bool isFourState) {
        SmallVector<SVInt> buffer;
        while (width > 0) {
            auto ci = slicePacked(iter, iterEnd, bit, width);
            SLANG_ASSERT(ci.getBitWidth() <= width);
            width -= ci.getBitWidth();
            if (!isFourState)
                ci.flattenUnknowns();

            buffer.emplace_back(std::move(ci));
        }

        SLANG_ASSERT(!buffer.empty());
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
        auto width = (dynamicSize + CHAR_BIT - 1) / CHAR_BIT;
        dynamicSize = 0;
        if (!bit && iter != iterEnd && (*iter)->isString() && (*iter)->str().length() == width)
            return std::move(**iter);

        return ConstantValue(concatPacked(bitwidth_t(width * CHAR_BIT), false)).convertToStr();
    }

    if (type.isUnpackedArray()) {
        auto& ct = type.getCanonicalType();
        SmallVector<ConstantValue> buffer;
        if (ct.kind != SymbolKind::FixedSizeUnpackedArrayType) {
            // dynamicSize is the remaining size: For unbounded dynamically sized types,
            // the conversion process is greedy: adjust the size of the first dynamically
            // sized item in the destination to the remaining size; any remaining dynamically
            // sized items are left empty.
            if (dynamicSize > 0) {
                auto elemWidth = type.getArrayElementType()->isFixedSize()
                                     ? type.getArrayElementType()->getBitstreamWidth()
                                     : dynamicSize;

                // If element is dynamically sized, num = 1
                // For bit-stream casting, dynamicSize % elemWidth == 0 and num = dynamicSize /
                // elemWidth. For implicit streaming concatenation conversion, num is the smallest
                // number of elements that make it as wide as or wider than dynamicSize.
                uint64_t num = (dynamicSize + elemWidth - 1) / elemWidth;
                for (uint64_t i = num; i > 0; i--) {
                    buffer.emplace_back(unpackBitstream(*type.getArrayElementType(), iter, iterEnd,
                                                        bit, dynamicSize));
                }

                SLANG_ASSERT(!dynamicSize || type.getArrayElementType()->isFixedSize());
                dynamicSize = 0;
            }
        }
        else {
            auto& fsua = ct.as<FixedSizeUnpackedArrayType>();
            auto& elem = fsua.elementType;
            for (auto width = fsua.range.width(); width > 0; width--)
                buffer.emplace_back(unpackBitstream(elem, iter, iterEnd, bit, dynamicSize));
        }

        return constContainer(ct, buffer);
    }

    if (type.isUnpackedStruct()) {
        SmallVector<ConstantValue> buffer;
        auto& ct = type.getCanonicalType();
        for (auto field : ct.as<UnpackedStructType>().fields)
            buffer.emplace_back(unpackBitstream(field->getType(), iter, iterEnd, bit, dynamicSize));

        return constContainer(ct, buffer);
    }

    // All other types should have been filtered out as errors before getting here.
    SLANG_UNREACHABLE;
}

ConstantValue Bitstream::evaluateCast(const Type& type, ConstantValue&& value,
                                      SourceRange sourceRange, EvalContext& context,
                                      bool isImplicit) {
    auto srcSize = value.getBitstreamWidth();
    uint64_t dynamicSize = 0;
    if (!isImplicit) { // Explicit bit-stream casting
        dynamicSize = bitstreamCastRemainingSize(type, srcSize);
        if (dynamicSize > srcSize) {
            context.addDiag(diag::ConstEvalBitstreamCastSize, sourceRange)
                << value.getBitstreamWidth() << type;
            return nullptr;
        }
    }
    else { // implicit streaming concatenation conversion
        auto targetWidth = type.getBitstreamWidth();
        if (targetWidth < srcSize) {
            if (type.isFixedSize()) {
                context.addDiag(diag::BadStreamSize, sourceRange) << targetWidth << srcSize;
                return nullptr;
            }
            dynamicSize = srcSize - targetWidth;
        }
    }

    SmallVector<ConstantValue*> packed;
    packBitstream(value, packed);

    uint64_t bitOffset = 0;
    auto iter = std::cbegin(packed);
    auto cv = unpackBitstream(type, iter, std::cend(packed), bitOffset, dynamicSize);
    SLANG_ASSERT(!dynamicSize);
    SLANG_ASSERT(isImplicit || (iter == std::cend(packed) && !bitOffset));
    return cv;
}

static bool withAfterDynamic(const StreamingConcatenationExpression& lhs,
                             const SourceRange*& dynamic, const SourceRange*& with) {
    // The expression within the "with" is evaluated immediately before its corresponding array is
    // streamed. The first dynamically sized item without "with" constraints accept all the
    // available data. If the former appears after the latter, evaluation order has conflict.
    for (auto& stream : lhs.streams()) {
        auto& operand = *stream.operand;
        if (operand.kind == ExpressionKind::Streaming) {
            if (withAfterDynamic(operand.as<StreamingConcatenationExpression>(), dynamic, with))
                return true;
        }
        else if (stream.withExpr) {
            with = &stream.withExpr->sourceRange;
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
                            SourceRange assignmentRange, const ASTContext& context) {
    if (rhs.kind != ExpressionKind::Streaming) {
        if (!rhs.type->isBitstreamType()) {
            context.addDiag(diag::BadStreamSourceType, assignmentRange)
                << *rhs.type << lhs.sourceRange;
            return false;
        }

        if (!checkClassAccess(*rhs.type, context, rhs.sourceRange))
            return false;
    }

    const SourceRange *dynamic = nullptr, *with = nullptr;
    if (withAfterDynamic(lhs, dynamic, with)) {
        context.addDiag(diag::BadStreamWithOrder, *with) << *dynamic;
        return false;
    }

    if (context.inUnevaluatedBranch())
        return true; // No size check in an unevaluated conditional branch

    uint64_t targetWidth = lhs.getBitstreamWidth();
    uint64_t sourceWidth;
    bool good = true;

    if (rhs.kind != ExpressionKind::Streaming) {
        if (!rhs.type->isFixedSize())
            return true; // Sizes checked at constant evaluation or runtime

        sourceWidth = rhs.type->getBitstreamWidth();
        good = targetWidth <= sourceWidth;
    }
    else {
        auto& source = rhs.as<StreamingConcatenationExpression>();
        sourceWidth = source.getBitstreamWidth();
        if (lhs.isFixedSize() && source.isFixedSize())
            good = targetWidth == sourceWidth;
        else
            good = dynamicSizesMatch(lhs, source);
    }

    if (!good) {
        auto& diag = context.addDiag(diag::BadStreamSize, assignmentRange);
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
                            SourceRange assignmentRange, const ASTContext& context) {
    // No need to checkClassAccess here because a class is never a valid
    // destination bitstream type.
    if (!target.isBitstreamType(true)) {
        context.addDiag(diag::BadStreamTargetType, assignmentRange) << target << rhs.sourceRange;
        return false;
    }

    if (context.inUnevaluatedBranch())
        return true; // No size check in an unevaluated conditional branch
    if (!target.isFixedSize())
        return true; // Sizes checked at constant evaluation or runtime

    auto targetWidth = target.getBitstreamWidth();
    auto sourceWidth = rhs.getBitstreamWidth();
    if (targetWidth < sourceWidth) {
        auto& diag = context.addDiag(diag::BadStreamSize, assignmentRange)
                     << targetWidth << sourceWidth;
        diag << rhs.sourceRange;
        return false;
    }

    return true;
}

bool Bitstream::isBitstreamCast(const Type& type, const StreamingConcatenationExpression& arg) {
    if (!type.isBitstreamType(true))
        return false;

    if (type.isFixedSize() && arg.isFixedSize())
        return type.getBitstreamWidth() == arg.getBitstreamWidth();

    return dynamicSizesMatch(type, arg);
}

bool Bitstream::checkClassAccess(const Type& type, const ASTContext& context,
                                 SourceRange sourceRange) {
    if (!type.isClass())
        return true;

    auto& ct = type.getCanonicalType().as<ClassType>();
    for (auto& prop : ct.membersOfType<ClassPropertySymbol>()) {
        if (prop.visibility != Visibility::Public && prop.lifetime == VariableLifetime::Automatic) {
            if (!Lookup::isVisibleFrom(prop, *context.scope)) {
                context.addDiag(diag::ClassPrivateMembersBitstream, sourceRange) << type;
                return false;
            }
        }
    }
    return true;
}

ConstantValue Bitstream::reOrder(ConstantValue&& value, uint64_t sliceSize, uint64_t unpackWidth) {
    uint64_t totalWidth = value.getBitstreamWidth();
    SLANG_ASSERT(unpackWidth <= totalWidth);

    uint64_t numBlocks = ((unpackWidth ? unpackWidth : totalWidth) + sliceSize - 1) / sliceSize;
    if (numBlocks <= 1)
        return std::move(value);

    SmallVector<ConstantValue*> packed;
    packBitstream(value, packed);
    if (packed.empty())
        return std::move(value);

    size_t rightIndex = packed.size() - 1; // Right-to-left
    uint64_t rightWidth = packed.back()->getBitstreamWidth();
    uint64_t extraBits = 0;

    if (unpackWidth) {
        if (unpackWidth < totalWidth) { // left-aligned so trim rightmost
            auto trimWidth = totalWidth - unpackWidth;
            while (trimWidth >= rightWidth) {
                rightIndex--;
                trimWidth -= rightWidth;
                rightWidth = packed[rightIndex]->getBitstreamWidth();
            }
            rightWidth -= trimWidth;
        }

        // For unpack, extraBits is for the first block.
        // For pack, extraBits is for the last block.
        extraBits = unpackWidth % sliceSize;
    }

    std::vector<ConstantValue> result;
    result.reserve(std::max<size_t>(packed.size(), numBlocks));
    auto sliceOrAppend = [&](PackIterator iter) {
        if (rightWidth == (*iter)->getBitstreamWidth())
            result.emplace_back(std::move(**iter));
        else {
            uint64_t bit = 0;
            result.emplace_back(slicePacked(iter, std::cend(packed), bit, rightWidth));
        }
    };

    while (numBlocks > 1) {
        size_t index = rightIndex;
        uint64_t width = rightWidth;
        uint64_t slice = sliceSize;
        if (extraBits) {
            slice = extraBits;
            extraBits = 0;
        }
        while (slice >= width) {
            index--;
            slice -= width;
            width = packed[index]->getBitstreamWidth();
        }

        // A block composed of bits from the last "slice" bits of packed[index] to the first
        // "rightWidth" bits of packed[rightIndex].
        auto iter = std::cbegin(packed) + index;
        if (slice) {
            auto bit = width - slice;
            result.emplace_back(slicePacked(iter, std::cend(packed), bit, slice));
            width -= slice;
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
    auto iter = std::cbegin(packed);
    for (size_t i = 0; i < rightIndex; i++)
        result.emplace_back(std::move(**iter++));
    sliceOrAppend(iter);

    return result;
}

/// Performs unpack operation of streaming concatenation target on a bit-stream.
static bool unpackConcatenation(const StreamingConcatenationExpression& lhs, PackIterator& iter,
                                const PackIterator iterEnd, uint64_t& bitOffset,
                                uint64_t& dynamicSize, EvalContext& context,
                                SmallVectorBase<ConstantValue>* dryRun = nullptr) {
    for (auto& stream : lhs.streams()) {
        auto& operand = *stream.operand;
        if (operand.kind == ExpressionKind::Streaming) {
            auto& concat = operand.as<StreamingConcatenationExpression>();
            if (dryRun || !concat.getSliceSize()) {
                if (!unpackConcatenation(concat, iter, iterEnd, bitOffset, dynamicSize, context,
                                         dryRun)) {
                    return false;
                }
                continue;
            }

            // A dry run collects rvalue without storing lvalue
            uint64_t dynamicSizeSave = dynamicSize;
            SmallVector<ConstantValue> toBeOrdered;
            if (!unpackConcatenation(concat, iter, iterEnd, bitOffset, dynamicSize, context,
                                     &toBeOrdered)) {
                return false;
            }

            // Re-order to a new rvalue with the slice size
            ConstantValue cv = std::vector(toBeOrdered.begin(), toBeOrdered.end());
            uint64_t streamWidth = cv.getBitstreamWidth();
            auto rvalue = Bitstream::reOrder(std::move(cv), concat.getSliceSize(), streamWidth);

            SmallVector<ConstantValue*> packed;
            packBitstream(rvalue, packed);

            // A real pass stores lvalue from new rvalue
            auto iterConcat = std::cbegin(packed);
            uint64_t bit = 0;
            if (!unpackConcatenation(concat, iterConcat, std::cend(packed), bit, dynamicSizeSave,
                                     context)) {
                return false;
            }

            SLANG_ASSERT(dynamicSizeSave == dynamicSize);
            SLANG_ASSERT(iterConcat == std::cend(packed) && !bit);
        }
        else {
            auto& arrayType = *operand.type;
            ConstantRange with;
            ConstantValue rvalue;
            if (stream.withExpr) {
                auto range = stream.withExpr->evalSelector(context, /* enforceBounds */ false);
                if (!range)
                    return false;

                with = *range;

                auto elemType = arrayType.getArrayElementType();
                SLANG_ASSERT(elemType);

                auto withSize = checkedMulU64(elemType->getBitstreamWidth(), with.width());
                if (!withSize || withSize > Type::MaxBitWidth) {
                    context.addDiag(diag::ObjectTooLarge, stream.withExpr->sourceRange);
                    return false;
                }

                if (dynamicSize > 0 && !stream.constantWithWidth) {
                    if (withSize >= dynamicSize)
                        dynamicSize = 0;
                    else
                        dynamicSize -= *withSize;
                }

                if (with.left == with.right) {
                    rvalue = unpackBitstream(*elemType, iter, iterEnd, bitOffset, dynamicSize);
                }
                else {
                    // We already checked for overflow earlier so it's fine to create this
                    // temporary array result type as-is.
                    FixedSizeUnpackedArrayType rvalueType(
                        *elemType, with, elemType->getSelectableWidth() * with.width(), *withSize);

                    rvalue = unpackBitstream(rvalueType, iter, iterEnd, bitOffset, dynamicSize);
                }
            }
            else {
                rvalue = unpackBitstream(arrayType, iter, iterEnd, bitOffset, dynamicSize);
            }

            if (dryRun) {
                dryRun->emplace_back(std::move(rvalue));
                continue;
            }

            LValue lvalue = operand.evalLValue(context);
            if (!lvalue)
                return false;

            if (stream.withExpr) {
                if (with.left != with.right && arrayType.isQueue() && !rvalue.isQueue())
                    rvalue = constContainer(arrayType, rvalue.elements());

                auto elemType = arrayType.getArrayElementType();
                if (!arrayType.hasFixedRange()) {
                    // When the array is a variable-size array, it shall be resized to
                    // accommodate the range expression.
                    SLANG_ASSERT(with.left <= with.right);
                    auto oldValue = lvalue.load();
                    if (oldValue.size() <= static_cast<uint32_t>(with.right)) {
                        auto newValue = Bitstream::resizeToRange(std::move(oldValue),
                                                                 {0, with.right},
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

    return true;
}

ConstantValue Bitstream::evaluateTarget(const StreamingConcatenationExpression& lhs,
                                        const Expression& rhs, EvalContext& context) {
    ConstantValue rvalue = rhs.eval(context);
    if (!rvalue)
        return nullptr;

    auto srcSize = rvalue.getBitstreamWidth();
    auto targetWidth = lhs.getBitstreamWidth();
    uint64_t dynamicSize = 0;

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
        // Source size must be at least as large as the target size.
        if (targetWidth > srcSize) {
            context.addDiag(diag::BadStreamSize, lhs.sourceRange) << targetWidth << srcSize;
            return nullptr;
        }

        if (!lhs.isFixedSize()) {
            auto elemSize = dynamicBitstreamSize(lhs, BitstreamSizeMode::DestFill);
            if (!elemSize) {
                auto& diag = context.addDiag(diag::BadStreamSize, lhs.sourceRange);
                diag << formatWidth(lhs, BitstreamSizeMode::DestFill);
                diag << srcSize;
                return nullptr;
            }

            dynamicSize = srcSize - targetWidth;
            if (elemSize.multiplier)
                dynamicSize -= dynamicSize % elemSize.multiplier; // do not exceed srcSize
        }
    }

    if (lhs.getSliceSize() > 0)
        rvalue = reOrder(std::move(rvalue), lhs.getSliceSize(), targetWidth + dynamicSize);

    SmallVector<ConstantValue*> packed;
    packBitstream(rvalue, packed);

    uint64_t bitOffset = 0;
    auto iter = std::cbegin(packed);
    auto iterEnd = std::cend(packed);
    if (!unpackConcatenation(lhs, iter, iterEnd, bitOffset, dynamicSize, context))
        return nullptr;

    // (iter==iterEnd && !bitOffset) implies target and source have exactly the same size.
    if (iter == iterEnd) {
        SLANG_ASSERT(dynamicSize == 0);
        if (bitOffset > 0) {
            // Target longer than source
            context.addDiag(diag::BadStreamSize, lhs.sourceRange) << srcSize + bitOffset << srcSize;
        }
    }
    else if (rhs.kind == ExpressionKind::Streaming) {
        // Target shorter than source; this is legal unless rhs is a streaming concatenation.
        SLANG_ASSERT(srcSize >= (*iter)->getBitstreamWidth());
        auto tSize = srcSize - (*iter++)->getBitstreamWidth() + bitOffset;
        while (iter != iterEnd)
            tSize -= (*iter++)->getBitstreamWidth();
        context.addDiag(diag::BadStreamSize, lhs.sourceRange) << tSize << srcSize;
    }

    return rvalue;
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
            sliceValue.insert(sliceValue.end(), old.begin() + lower, old.begin() + upper);
            sliceValue.insert(sliceValue.end(), more, defaultValue);
            SLANG_ASSERT(sliceValue.size() == range.width());
            return sliceValue;
        }
        else {
            SLANG_ASSERT(value.isQueue());
            const auto& old = value.queue();
            SVQueue sliceValue(old->cbegin() + lower, old->cbegin() + upper);
            sliceValue.insert(sliceValue.end(), more, defaultValue);
            SLANG_ASSERT(sliceValue.size() == range.width());
            return sliceValue;
        }
    }

    return std::move(value);
}

ConstantValue Bitstream::convertToBitVector(ConstantValue&& value, SourceRange sourceRange,
                                            EvalContext& context) {
    if (value.bad() || value.isInteger())
        return value;

    // We don't worry about width being too large for an integral type here because we limit
    // how large any constant value can be.
    const uint64_t width = value.getBitstreamWidth();
    auto& type = context.getCompilation().getType(bitwidth_t(width), IntegralFlags::FourState |
                                                                         IntegralFlags::Unsigned);

    return evaluateCast(type, std::move(value), sourceRange, context, /* isImplicit */ true);
}

} // namespace slang::ast
