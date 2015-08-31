#pragma once

// Fixed-sized hash of string to value
// TODO: write a tool to find the best seed for given sets of elements

namespace slang {

template<typename T>
class StringTable {
public:
    StringTable(std::initializer_list<std::pair<StringRef, T>> entries) {
        // double count and round up to nearest power of 2
        capacity = (uint32_t)entries.size() * 2;
        capacity = roundUpToPow2(capacity);
        table = new Entry[capacity];

        for (auto& entry : entries) {
            uint32_t hc = hash(entry.first);
            uint32_t index = hc & (capacity - 1);
            while (table[index].hashCode != 0)
                index = (index + 1) & (capacity - 1);

            table[index].key = entry.first;
            table[index].value = entry.second;
            table[index].hashCode = hc;
        }
    }

    bool lookup(StringRef key, T& value) const {
        uint32_t hc = hash(key);
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
        uint32_t hashCode = 0;
        T value;
    };
    Entry* table;
    uint32_t capacity;

    static uint32_t hash(StringRef str) {
        const static uint32_t Seed = 1331238292; // oh yeah, great number right there
        return xxhash32(str.begin() + 1, str.length() - 1, Seed);
    }

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