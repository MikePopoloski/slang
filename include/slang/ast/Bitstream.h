//------------------------------------------------------------------------------
//! @file Bitstream.h
//! @brief Helpers for implementing bit-stream casting and streaming operators
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/numeric/ConstantValue.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/Util.h"

namespace slang::ast {

class ASTContext;
class EvalContext;
class Expression;
class StreamingConcatenationExpression;
class Type;

/// Provides utility methods for working with bitstream operations.
class SLANG_EXPORT Bitstream {
public:
    /// Compile-time check that the source and destination types have the same dynamic bitstream
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
                            SourceLocation assignLoc, const ASTContext& context);

    /// Compile-time check that streaming concatenation source has a bit-stream target type with
    /// enough bits. If the source is definitely invalid, a diagnostic will be issued.
    static bool canBeSource(const Type& target, const StreamingConcatenationExpression& rhs,
                            SourceLocation assignLoc, const ASTContext& context);

    /// Compile-time check that bit-streaming cast on a streaming operator is valid.
    static bool isBitstreamCast(const Type& type, const StreamingConcatenationExpression& arg);

    /// Re-ordering of the generic stream. For source/packed concatenation, unpackWidth = 0. For
    /// target/unpacked concatenation, unpackWidth is the total width of target.
    static ConstantValue reOrder(ConstantValue&& value, size_t sliceSize, size_t unpackWidth = 0);

    /// Performs constant evaluation of an assignment with a streaming concatenation as the target.
    static ConstantValue evaluateTarget(const StreamingConcatenationExpression& lhs,
                                        const Expression& rhs, EvalContext& context);

    /// Resize a constant array value from [0:size-1] to [lower:upper].
    static ConstantValue resizeToRange(ConstantValue&& value, ConstantRange range,
                                       ConstantValue defaultValue, bool keepArray = false);

    /// Converts a bitstream value into a corresponding bit vector of the same width.
    static ConstantValue convertToBitVector(ConstantValue&& value, SourceRange sourceRange,
                                            EvalContext& context);

private:
    Bitstream() = default;
};

} // namespace slang::ast
