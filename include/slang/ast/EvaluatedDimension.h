//------------------------------------------------------------------------------
//! @file EvaluatedDimension.h
//! @brief Helper type containing results of type dimension evaluation
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/numeric/ConstantValue.h"
#include "slang/util/Enum.h"

namespace slang::ast {

class Expression;
class Type;

// clang-format off
#define DK(x) \
    x(Unknown) \
    x(Range) \
    x(AbbreviatedRange) \
    x(Dynamic) \
    x(Associative) \
    x(Queue) \
    x(DPIOpenArray)
// clang-format on
SLANG_ENUM(DimensionKind, DK)
#undef DK

/// The result of evaluating dimension syntax nodes.
struct SLANG_EXPORT EvaluatedDimension {
    /// The kind of dimension indicated by the syntax nodes.
    DimensionKind kind = DimensionKind::Unknown;

    /// The compile-time constant range specifying the dimensions.
    ConstantRange range;

    /// If the dimension is for an associative type, this is a pointer to that type.
    /// Otherwise nullptr.
    const Type* associativeType = nullptr;

    /// If the dimension is for a queue type, this is the optionally specified
    /// max queue size.
    uint32_t queueMaxSize = 0;

    /// For Range and AbbreviatedRange kinds, the original left-bound expression
    /// as it appeared in the source (e.g. the expression for `W-1` in `[W-1:0]`),
    /// or nullptr if not applicable.
    const Expression* leftExpr = nullptr;

    /// For Range kind only, the original right-bound expression as it appeared in
    /// the source (e.g. the expression for `0` in `[W-1:0]`), or nullptr if not applicable.
    const Expression* rightExpr = nullptr;

    /// Indicates whether the dimension is for a range (as opposed to a single
    /// index or an associative array access, for example).
    bool isRange() const {
        return kind == DimensionKind::Range || kind == DimensionKind::AbbreviatedRange;
    }
};

} // namespace slang::ast
