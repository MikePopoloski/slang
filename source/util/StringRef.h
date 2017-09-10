//------------------------------------------------------------------------------
// StringRef.h
// Lighweight view of a string.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <ostream>
#include <string>

#include "BumpAllocator.h"

namespace slang {

using StringRef = std::string_view;

//class StringRef : public string_view {
//public:
//    StringRef() = default;
//    StringRef(const char* str, size_t len) : string_view(str, len) {}
//    //StringRef(const char* str) : string_view(str) {}
//    StringRef(const string& str) : string_view(str) {}
//
//    StringRef(std::nullptr_t) = delete;
//
//    friend bool operator==(StringRef lhs, const string& rhs);
//    friend bool operator==(StringRef lhs, const char* rhs);
//    friend bool operator==(const string& lhs, StringRef rhs);
//    friend bool operator==(const char* lhs, StringRef rhs);
//};

inline StringRef intern(BumpAllocator& alloc, StringRef str) {
    if (str.empty())
        return str;

    char* data = (char*)alloc.allocate((uint32_t)str.length());
    str.copy(data, str.length());
    return StringRef(data, str.length());
}

//class BumpAllocator;
//
///// StringRef - Immutable wrapper around a {pointer, length} pair to a string.
///// This class does not own the string memory; it's up to the user to make sure
///// it remains valid.
/////
///// Note: there isn't necessarily a null terminator in the string.
//class StringRef {
//public:
//    StringRef();
//    StringRef(std::nullptr_t);
//    StringRef(const char* ptr, uint32_t length);
//    explicit StringRef(const std::string& str);
//
//    template<typename Container>
//    explicit StringRef(const Container& container) :
//        ptr(&*container.begin()),
//        len(uint32_t(container.size()))
//    {
//    }
//
//    /// Constructs a StringRef that refers to a char array (usually a string literal).
//    /// It's assumed that the array will have a null terminator.
//    template<size_t N>
//    StringRef(const char(&str)[N]) :
//        ptr(str), len(N-1)
//    {
//        static_assert(N > 0, "String literal array must have at least one element");
//    }
//
//    const char* begin() const { return ptr; }
//    const char* end() const { return ptr + len; }
//    uint32_t length() const { return len; }
//    bool empty() const { return len == 0; }
//
//    /// Retrieves a subset of the string using the given range. There's no copy of the data;
//    /// pointers still point to the original backing memory for the string.
//    StringRef subString(uint32_t startIndex) const;
//    StringRef subString(uint32_t startIndex, uint32_t subStringLength) const;
//
//    /// Hash the entire string using the given seed.
//    size_t hash(size_t seed = Seed) const;
//
//    /// Create a copy of the string using the given allocator to create backing memory.
//    StringRef intern(BumpAllocator& alloc) const;
//
//    /// Convert to std::string.
//    std::string toString() const;
//
//    char operator[](uint32_t index) const;
//
//    explicit operator bool() const { return !empty(); }
//
//    friend std::ostream& operator<<(std::ostream& os, const StringRef& rhs);
//
//    friend bool operator==(const StringRef& lhs, const std::string& rhs);
//    friend bool operator==(const StringRef& lhs, const StringRef& rhs);
//    friend bool operator==(const StringRef& lhs, const char* rhs);
//    friend bool operator==(const std::string& lhs, const StringRef& rhs) { return operator==(rhs, lhs); }
//    friend bool operator==(const char* lhs, const StringRef& rhs) { return operator==(rhs, lhs); }
//
//    friend bool operator!=(const StringRef& lhs, const std::string& rhs) { return !operator==(lhs, rhs); }
//    friend bool operator!=(const std::string& lhs, const StringRef& rhs) { return !operator==(lhs, rhs); }
//    friend bool operator!=(const StringRef& lhs, const char* rhs) { return !operator==(lhs, rhs); }
//    friend bool operator!=(const char* lhs, const StringRef& rhs) { return !operator==(lhs, rhs); }
//    friend bool operator!=(const StringRef& lhs, const StringRef& rhs) { return !operator==(lhs, rhs); }
//
//    friend bool operator<(const StringRef& lhs, const StringRef& rhs) { return std::lexicographical_compare(lhs.begin(), lhs.end(), rhs.begin(), rhs.end()); }
//    friend bool operator<=(const StringRef& lhs, const StringRef& rhs) { return lhs < rhs && lhs == rhs; }
//    friend bool operator>=(const StringRef& lhs, const StringRef& rhs) { return !(lhs < rhs); }
//    friend bool operator>(const StringRef& lhs, const StringRef& rhs) { return lhs >= rhs && lhs != rhs; }
//
//private:
//    static constexpr uint64_t Seed = 0x3765936aa9a6c480; // chosen by fair dice roll
//
//    const char* ptr;
//    uint32_t len;
//};
//
}