#pragma once

#include <cstddef>
#include <cstdint>
#include <ostream>
#include <string>

// Immutable wrapper around a {pointer, length} pair to a string.
// This class does not own the string memory; it's up to the user
// to make sure it remains valid.

namespace slang {

class BumpAllocator;

class StringRef {
public:
    StringRef();
    StringRef(std::nullptr_t);
    StringRef(const char* ptr, uint32_t length);
    StringRef(const std::string& str);

    template<typename Container>
    explicit StringRef(const Container& container) :
        ptr(container.begin()),
        len(uint32_t(container.end() - ptr))
    {
    }

    template<size_t N>
    StringRef(const char(&str)[N]) :
        ptr(str), len(N-1)
    {
        static_assert(N > 0, "String literal array must have at least one element");
    }

    const char* begin() const { return ptr; }
    const char* end() const { return ptr + len; }
    uint32_t length() const { return len; }
    bool empty() const { return len == 0; }

    StringRef subString(uint32_t startIndex) const;
    StringRef subString(uint32_t startIndex, uint32_t subStringLength) const;

    size_t hash(size_t seed = Seed) const;
    StringRef intern(BumpAllocator& alloc) const;
    std::string toString() const;

    char operator[](uint32_t index) const;

    explicit operator bool() const { return !empty(); }

    friend std::ostream& operator<<(std::ostream& os, const StringRef& rhs);

    friend bool operator==(const StringRef& lhs, const std::string& rhs);
    friend bool operator==(const StringRef& lhs, const StringRef& rhs);
    friend bool operator==(const StringRef& lhs, const char* rhs);
    friend bool operator==(const std::string& lhs, const StringRef& rhs) { return operator==(rhs, lhs); }
    friend bool operator==(const char* lhs, const StringRef& rhs) { return operator==(rhs, lhs); }

    friend bool operator!=(const StringRef& lhs, const std::string& rhs) { return !operator==(lhs, rhs); }
    friend bool operator!=(const std::string& lhs, const StringRef& rhs) { return !operator==(lhs, rhs); }
    friend bool operator!=(const StringRef& lhs, const char* rhs) { return !operator==(lhs, rhs); }
    friend bool operator!=(const char* lhs, const StringRef& rhs) { return !operator==(lhs, rhs); }
    friend bool operator!=(const StringRef& lhs, const StringRef& rhs) { return !operator==(lhs, rhs); }

private:
    static constexpr uint64_t Seed = 0x3765936aa9a6c480; // chosen by fair dice roll

    const char* ptr;
    uint32_t len;
};

}

namespace std {

template<>
struct hash<slang::StringRef> {
    size_t operator()(const slang::StringRef& str) const {
        return str.hash();
    }
};

}