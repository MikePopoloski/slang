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

namespace slang::ast {

class Compilation;
class Expression;
class Symbol;
struct LookupResult;

/// Represents a hierarchical reference to a symbol.
class HierarchicalReference {
public:
    /// An element in the hierarchical path.
    struct Element {
        /// The symbol through which the path traverses.
        not_null<const Symbol*> symbol;
        std::variant<int32_t, std::string_view> selector;

        Element(const Symbol& symbol);
        Element(const Symbol& symbol, int32_t index);
    };

    const Symbol* target = nullptr;
    const Expression* expr = nullptr;
    std::span<const Element> path;
    size_t upwardCount = 0;

    HierarchicalReference() = default;

    static HierarchicalReference fromLookup(Compilation& compilation, const LookupResult& result);
};

} // namespace slang::ast
