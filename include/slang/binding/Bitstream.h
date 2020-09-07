//------------------------------------------------------------------------------
//! @file Bitstream.h
//! @brief Helpers for implementing bit-stream casting and streaming operators
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

namespace slang {

class Type;
class ConstantValue;
class StreamingConcatenationExpression;
class Expression;
class BindContext;
class EvalContext;
class SourceRange;

class Bitstream {
public:
    /// Compile-time check that the source and destination types have the same dynamic bit-stream
    /// sizes.
    template<typename T1, typename T2>
    static bool dynamicSizesMatch(const T1& destination, const T2& source);

    /// Performs a bit-stream cast of @a value  to @a type. If the conversion is not valid,
    /// returns nullptr (invalid value).
    static ConstantValue castEval(const Type& type, const ConstantValue&, SourceRange,
                                  EvalContext&);

    /// Compile-time check that streaming concatenation target has a bit-stream type source with
    /// enought bits
    static bool streamingTargetCheck(const StreamingConcatenationExpression& lhs,
                                     const Expression& rhs, const BindContext&);

    /// Compile-time check that streaming concatenation source has a bit-stream target type  with
    /// enought bits
    static bool streamingSourceCheck(const Type& target,
                                     const StreamingConcatenationExpression& rhs,
                                     const BindContext&);

    /// Compile-time check that bit-streaming cast on a streaming operator is valid
    static bool streamingCastCheck(const Type& target, const StreamingConcatenationExpression& arg);

private:
    Bitstream() = default;
};

} // namespace slang
