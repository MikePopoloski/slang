//------------------------------------------------------------------------------
//! @file InstancePath.h
//! @brief Helper type for representing a hierarchical path to an instance
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

class InstancePath {
public:
    InstancePath() = default;
    explicit InstancePath(const Symbol& symbol);

    class Entry {
    public:
        Entry() : value(0) {}
        Entry(uint32_t index) : value(index) {}
        Entry(const syntax::SyntaxNode& syntax) : value(reinterpret_cast<uintptr_t>(&syntax)) {}

        uintptr_t getOpaqueValue() const { return value; }

        auto operator<=>(const Entry& rhs) const = default;

    private:
        uintptr_t value;
    };

    SmallVector<Entry> entries;

private:
    void buildPath(const Symbol& symbol);
};

} // namespace slang::ast

namespace std {

template<>
struct hash<slang::ast::InstancePath::Entry> {
    size_t operator()(const slang::ast::InstancePath::Entry& entry) const {
        return size_t(entry.getOpaqueValue());
    }
};

} // namespace std
