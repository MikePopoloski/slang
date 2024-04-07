//------------------------------------------------------------------------------
//! @file OpaqueInstancePath.h
//! @brief Helper type for representing an opaque path to an instance
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/SmallVector.h"

namespace slang::syntax {
class SyntaxNode;
}

namespace slang::ast {

class Symbol;

/// Represents a path to a specific instance in a design.
///
/// The path is stored only via opaque syntax nodes, to allow it to generalize
/// across compilations (and so different sets of AST nodes) that share the
/// same underlying syntax.
class OpaqueInstancePath {
public:
    /// Constructs an empty instance path.
    OpaqueInstancePath() = default;

    /// @brief Constructs a path to the given symbol.
    ///
    /// If the given symbol is not an instance, the path will point to the
    /// nearest parent instance.
    explicit OpaqueInstancePath(const Symbol& symbol);

    /// @returns true if the path is empty
    [[nodiscard]] bool empty() const { return entries.empty(); }

    /// @brief An entry in the path.
    ///
    /// Each entry is either a syntax node that points to a piece of syntax
    /// that defines the hierarchy entry, or an integer that indicates an
    /// element of an instance or generate array.
    class Entry {
    public:
        /// Constructs an empty entry.
        Entry() : value(0) {}

        /// Construct an entry that that indicates an
        /// element of an instance or generate array.
        Entry(uint32_t index) : value(index) {}

        /// Constructs an entry that points to a piece of syntax that
        /// defines a hierarchy node.
        Entry(const syntax::SyntaxNode& syntax) : value(reinterpret_cast<uintptr_t>(&syntax)) {}

        /// Gets an opaque value that represents the entry; either the
        /// array index or the syntax node pointer.
        uintptr_t getOpaqueValue() const { return value; }

        /// Default comparison operator.
        auto operator<=>(const Entry& rhs) const = default;

    private:
        uintptr_t value;
    };

    /// The list of entries in the path.
    SmallVector<Entry> entries;

private:
    void buildPath(const Symbol& symbol);
};

} // namespace slang::ast

namespace std {

template<>
struct hash<slang::ast::OpaqueInstancePath::Entry> {
    size_t operator()(const slang::ast::OpaqueInstancePath::Entry& entry) const {
        return size_t(entry.getOpaqueValue());
    }
};

} // namespace std
