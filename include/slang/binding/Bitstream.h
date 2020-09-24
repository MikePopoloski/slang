//------------------------------------------------------------------------------
//! @file Bitstream.h
//! @brief Helpers for implementing bit-stream casting and streaming operators
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/OperatorExpressions.h"

namespace slang {

class Bitstream {
public:
    /// Compile-time check that the source and destination types have the same dynamic bit-stream
    /// sizes.
    /// note: only Type and StreamingConcatenationExpression are allowed for T1/T2
    template<typename T1, typename T2>
    static bool dynamicSizesMatch(const T1& destination, const T2& source);

    /// Performs a bit-stream cast of @a value to @a type. If the conversion is not valid,
    /// returns nullptr (invalid value).
    static ConstantValue evaluateCast(const Type& type, ConstantValue&& value,
                                      SourceRange sourceRange, EvalContext& context,
                                      bool isImplicit = false);

    /// Compile-time check that streaming concatenation target has a bit-stream type source with
    /// enough bits. If the target is definitely invalid, a diagnostic will be issued.
    static bool canBeTarget(const StreamingConcatenationExpression& lhs, const Expression& rhs,
                            SourceLocation assignLoc, const BindContext& context);

    /// Compile-time check that streaming concatenation source has a bit-stream target type with
    /// enough bits. If the source is definitely invalid, a diagnostic will be issued.
    static bool canBeSource(const Type& target, const StreamingConcatenationExpression& rhs,
                            SourceLocation assignLoc, const BindContext& context);

    /// Compile-time check that bit-streaming cast on a streaming operator is valid.
    static bool isBitstreamCast(const Type& type, const StreamingConcatenationExpression& arg);

    /// Re-ordering of the generic stream. For source/packed concatenation, unpackWidth = 0. For
    /// target/unpacked concatenation, unpackWidth is the total width of target.
    static ConstantValue reOrder(ConstantValue&& value, size_t sliceSize, size_t unpackWidth = 0);

    /// Performs constant evaluation of an assignment with a streaming concatenation as the target
    static ConstantValue evaluateTarget(const StreamingConcatenationExpression& lhs,
                                        const Expression& rhs, EvalContext& context);

    /// Validates stream expression "with" expression range.
    static bool validStreamWithRange(const Type& arrayType, WithRangeKind kind,
                                     optional<int32_t> left, optional<int32_t> right,
                                     std::variant<const BindContext*, EvalContext*> context,
                                     SourceRange leftRange, SourceRange rightRange);

    /// Derives constant width from "with" expression range.
    static optional<int32_t> withRangeWidth(WithRangeKind kind, optional<int32_t> left,
                                            optional<int32_t> right);

    /// Evaluates stream "with" expression to a constant range.
    static optional<ConstantRange> evaluateWith(
        const Type& arrayType, const StreamingConcatenationExpression::WithExpression& with,
        EvalContext& context);

    /// Resize a constant array value from [0:size-1] to [lower:upper].
    static ConstantValue resizeToRange(ConstantValue&& value, ConstantRange range,
                                       ConstantValue defaultValue, bool keepArray = false);

private:
    Bitstream() = default;
};

} // namespace slang
