//------------------------------------------------------------------------------
//! @file StringTable.h
//! @brief Specialized string lookup table
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <memory>

#include "slang/util/Util.h"

namespace slang {

/// This class is a lookup table from string to value. It's optimized for
/// a known fixed set of keywords.
template<typename T>
class StringTable {
public:
    /// Constructs the string table with all possible entries (key / values) already provided.
    /// No other entries can be added after construction.
    StringTable(std::initializer_list<std::pair<string_view, T>> entries) {
        // Give ourselves a bunch of room for entries to hash by using double
        // the required number of entries. Also round up to power of two so that
        // we can use bitwise AND instead of mod for wraparound.
        capacity = (uint32_t)entries.size() * 2;
        capacity = roundUpToPow2(capacity);
        table = std::make_unique<Entry[]>(capacity);

        for (auto& entry : entries) {
            size_t hc = std::hash<string_view>()(entry.first);
            uint32_t index = hc & (capacity - 1);
            while (table[index].hashCode != 0)
                index = (index + 1) & (capacity - 1);

            table[index].key = entry.first;
            table[index].value = entry.second;
            table[index].hashCode = hc;
        }
    }

    /// Looks for an entry with the given @a key and sets @a value if found.
    /// @return true if the element is found, and false otherwise.
    bool lookup(string_view key, T& value) const {
        size_t hc = std::hash<string_view>()(key);
        uint32_t index = hc & (capacity - 1);
        do {
            if (table[index].hashCode == hc && table[index].key == key) {
                value = table[index].value;
                return true;
            }
            index = (index + 1) & (capacity - 1);
        } while (table[index].hashCode != 0);

        return false;
    }

private:
    struct Entry {
        string_view key;
        size_t hashCode = 0;
        T value;
    };
    std::unique_ptr<Entry[]> table;
    uint32_t capacity;

    static uint32_t roundUpToPow2(uint32_t n) {
        n--;
        n |= n >> 1;
        n |= n >> 2;
        n |= n >> 4;
        n |= n >> 8;
        n |= n >> 16;
        n++;
        return n;
    }
};

} // namespace slang
