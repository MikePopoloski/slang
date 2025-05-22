//------------------------------------------------------------------------------
//! @file HierarchicalReference.h
//! @brief Helper type for representing a hierarchical reference
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <span>
#include <string_view>
#include <variant>

#include "slang/util/Util.h"

namespace slang {
class BumpAllocator;
}

namespace slang::ast {

class Compilation;
class Expression;
class InstanceSymbol;
class Symbol;
struct LookupResult;

/// Represents a hierarchical reference to a symbol.
class SLANG_EXPORT HierarchicalReference {
public:
    /// An element in the hierarchical path.
    struct Element {
        /// The symbol through which the path traverses.
        not_null<const Symbol*> symbol;

        /// The selector used to get to the @a symbol, either
        /// an index if the parent was an array, or a field name.
        std::variant<int32_t, std::pair<int32_t, int32_t>, std::string_view> selector;

        /// Constructs an element with a name selector.
        Element(const Symbol& symbol);

        /// Constructs an element with an index selector.
        Element(const Symbol& symbol, int32_t index);

        /// Constructs an element with a range selector.
        Element(const Symbol& symbol, std::pair<int32_t, int32_t> range);
    };

    /// The target symbol of the hierarchical reference.
    const Symbol* target = nullptr;

    /// The expression that was used to start the lookup,
    /// typically a HierarchicalValueExpression.
    const Expression* expr = nullptr;

    /// The resolved path to the target symbol.
    std::span<const Element> path;

    /// The number of times the path traverses upward before
    /// going back down the hierarchy to reach the target symbol.
    size_t upwardCount = 0;

    /// Default constructor.
    HierarchicalReference() = default;

    /// Constructs a HierarchicalReference from a lookup result.
    static HierarchicalReference fromLookup(Compilation& compilation, const LookupResult& result);

    /// Returns true if the hierarchical reference was resolved
    /// via an interface port connection.
    bool isViaIfacePort() const;

    /// Returns true if the hierarchical reference traverses upward through the hierarchy.
    bool isUpward() const;

    /// Returns a new HierarchicalReference that represents the joined
    /// path of this reference and another.
    const HierarchicalReference& join(BumpAllocator& alloc,
                                      const HierarchicalReference& other) const;
};

} // namespace slang::ast
