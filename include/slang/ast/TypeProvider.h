//------------------------------------------------------------------------------
//! @file TypeProvider.h
//! @brief Interface for accessing simple types during AST construction
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/types/Type.h"

namespace slang::ast {

/// Interface for accessing simple types during AST construction.
///
/// Typically types will be constructed and uniquified via the Compilation class.
/// This interface can be used to provide access to commonly used types in a
/// way that is abstracted from the underlying Compilation instance.
class TypeProvider {
public:
    /// The allocator used for type construction.
    BumpAllocator& alloc;

    /// Constructs a new TypeProvider instance.
    TypeProvider(BumpAllocator& alloc) : alloc(alloc) {}

    /// Get the built-in `bit` type.
    const Type& getBitType() const;

    /// Get the built-in `logic` type.
    const Type& getLogicType() const;

    /// Get the built-in `int` type.
    const Type& getIntType() const;

    /// Get the built-in `byte` type.
    const Type& getByteType() const;

    /// Get the built-in `integer` type.
    const Type& getIntegerType() const;

    /// Get the built-in `real` type.
    const Type& getRealType() const;

    /// Get the built-in `shortreal` type.
    const Type& getShortRealType() const;

    /// Get the built-in `string` type.
    const Type& getStringType() const;

    /// Get the built-in `void` type.
    const Type& getVoidType() const;

    /// Get the error type, which is used as a placeholder
    /// to represent an invalid type.
    const Type& getErrorType() const;

    /// Get the built-in `null` type.
    const Type& getNullType() const;

    /// Get the built-in `$` type.
    const Type& getUnboundedType() const;

    /// Get the built-in type used for the result of the `type()` operator.
    const Type& getTypeRefType() const;

    /// Gets an integral vector type with the given size and flags.
    const Type& getType(bitwidth_t width, bitmask<IntegralFlags> flags) const;

    /// Gets a scalar (single bit) type with the given flags.
    const Type& getScalarType(bitmask<IntegralFlags> flags) const;
};

} // namespace slang::ast
