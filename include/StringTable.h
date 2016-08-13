//------------------------------------------------------------------------------
// StringTable.h
// Specialized string lookup table.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>
#include <initializer_list>

#include "StringRef.h"

// TODO: use an offline tool to make this a minimal perfect hash.

namespace slang {

/// This class is a lookup table from string to value. It's optimized for
/// a known fixed set of keywords
template<typename T>
class StringTable {
public:
    StringTable(std::initializer_list<std::pair<StringRef, T>> entries) {
        // double count and round up to nearest power of 2
        capacity = (uint32_t)entries.size() * 2;
        capacity = roundUpToPow2(capacity);
        table = new Entry[capacity];

        for (auto& entry : entries) {
            size_t hc = entry.first.hash();
            uint32_t index = hc & (capacity - 1);
            while (table[index].hashCode != 0)
                index = (index + 1) & (capacity - 1);

            table[index].key = entry.first;
            table[index].value = entry.second;
            table[index].hashCode = hc;
        }
    }

    bool lookup(StringRef key, T& value) const {
        size_t hc = key.hash();
        uint32_t index = hc & (capacity - 1);
        do {
            if (table[index].hashCode == hc &&
                table[index].key == key) {
                value = table[index].value;
                return true;
            }
            index = (index + 1) & (capacity - 1);
        } while (table[index].hashCode != 0);

        return false;
    }

private:
    struct Entry {
        StringRef key;
        size_t hashCode = 0;
        T value;
    };
    Entry* table;
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

}