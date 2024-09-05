//------------------------------------------------------------------------------
//! @file LValue.h
//! @brief Compile-time lvalue representation (for constant evaluation)
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/numeric/ConstantValue.h"

namespace slang::ast {

/// @brief A representation of an lvalue used for constant evaluation.
///
/// An lvalue is anything that can appear on the left hand side of an assignment
/// expression. It represents some storage location in memory that can be read
/// from and written to.
class SLANG_EXPORT LValue {
public:
    /// A concatenation of lvalues is also an lvalue and can be assigned to.
    struct Concat {
        /// The lvalue elements being concatenated.
        std::vector<LValue> elems;

        /// The kind of concatenation -- packed or unpacked.
        enum Kind { Packed, Unpacked } kind;

        /// Constructs a new Concat instance.
        Concat(std::vector<LValue>&& elems, Kind kind) : elems(std::move(elems)), kind(kind) {}
    };

    /// Default constructor -- results in an empty / invalid lvalue.
    LValue() = default;

    /// Implicit conversion from nullptr -- results in an empty / invalid lvalue.
    LValue(nullptr_t) {}

    LValue(const LValue&) = delete;
    LValue(LValue&& other) = default;

    /// Constructs a new lvalue that points to the given ConstantValue as a storage location.
    ///
    /// @note Memory for @a base must live beyond the lifetime of this lvalue.
    explicit LValue(ConstantValue& base) : value(Path{base}) {}

    /// Constructs a new lvalue that is a concatenation of the given elements.
    LValue(std::vector<LValue>&& elems, Concat::Kind kind) :
        value(Concat(std::move(elems), kind)) {}

    /// @returns true if the lvalue is invalid
    bool bad() const { return std::holds_alternative<std::monostate>(value); }

    /// @returns true if the lvalue is invalid
    explicit operator bool() const { return !bad(); }

    /// @brief Resolve the lvalue to a single target storage location.
    ///
    /// If the lvalue is invalid, or the path does not resolve to a single target
    /// (such as if it is a concatenation) returns nullptr.
    ConstantValue* resolve();

    /// Loads the lvalue, resolving all path elements and performing
    /// any necessary concatenations.
    ConstantValue load() const;

    /// Stores the given value into the storage pointed to by the lvalue.
    void store(const ConstantValue& value);

    /// Extends the lvalue by adding a bit slice.
    void addBitSlice(ConstantRange range);

    /// Extends the lvalue by adding an element index.
    void addIndex(int32_t index, ConstantValue&& defaultValue);

    /// @brief Extends the lvalue with a deliberate out-of-bounds value.
    ///
    /// This ensures that reads will return the default and writes will be ignored.
    void addIndexOutOfBounds(ConstantValue&& defaultValue);

    /// Extends the lvalue by adding an array slice.
    void addArraySlice(ConstantRange range, ConstantValue&& defaultValue);

    /// Extends the lvalue by adding a lookup of an associative array.
    void addArrayLookup(ConstantValue&& index, ConstantValue&& defaultValue);

private:
    ConstantValue* resolveInternal(std::optional<ConstantRange>& range);

    // A selection of a range of bits from an integral value.
    struct BitSlice {
        ConstantRange range;
    };

    // A selection of a single element from an array, string, struct, or union.
    struct ElementIndex {
        int32_t index = 0;
        ConstantValue defaultValue;
        bool forceOutOfBounds = false;
    };

    // A selection of a range of elements from an array.
    struct ArraySlice {
        ConstantRange range;
        ConstantValue defaultValue;
    };

    // A lookup of an element from an associative array.
    struct ArrayLookup {
        ConstantValue index;
        ConstantValue defaultValue;
    };

    using PathElement = std::variant<BitSlice, ElementIndex, ArraySlice, ArrayLookup>;
    struct Path {
        ConstantValue* base = nullptr;
        SmallVector<PathElement, 4> elements;

        explicit Path(ConstantValue& base) : base(&base) {}
    };

    // Every LValue is either a pointer to some variable plus a path of selections,
    // or it's a concatenation of other lvalues.
    std::variant<std::monostate, Path, Concat> value;
};

} // namespace slang::ast
