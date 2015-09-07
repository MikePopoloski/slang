#pragma once

#include "Debug.h"
#include "Hash.h"

// Immutable wrapper around a {pointer, length} pair to a string.
// This class does not own the string memory; it's up to the user
// to make sure it remains valid.

namespace slang {

class StringRef {
public:
    StringRef() :
        ptr(nullptr), count(0) {
    }

    StringRef(std::nullptr_t) :
        ptr(nullptr), count(0) {
    }

    StringRef(const char* ptr, uint32_t length) :
        ptr(ptr), count(length) {

        ASSERT((count & NullMask) == 0);
    }

    StringRef(const std::string& str) :
        ptr(str.c_str()), count((uint32_t)str.length() + 1) {

        checkNullTerminator();
    }

    // this constructor is meant for string literals
    template<size_t N>
    StringRef(const char(&str)[N]) :
        ptr(str), count(N) {

        checkNullTerminator();
    }

    const char* begin() const { return ptr; }
    const char* end() const { return ptr + length(); }

    uint32_t length() const { return count & ~NullMask; }
    bool empty() const { return length() == 0; }
    bool isNullTerminated() const { return (count & NullMask) != 0; }

    StringRef subString(uint32_t startIndex) const {
        ASSERT(startIndex <= length());
        return subString(startIndex, length() - startIndex);
    }

    StringRef subString(uint32_t startIndex, uint32_t subStringLength) const {
        ASSERT(startIndex + subStringLength <= length());
        return StringRef(ptr + startIndex, subStringLength);
    }

    size_t hash(size_t seed = Seed) const {
        if (empty())
            return 0;
        return slang::xxhash(ptr, length(), seed);
    }

    StringRef intern(BumpAllocator& alloc) const {
        if (empty())
            return StringRef();

        // +1 for trailing zero, which we might as well add here since we're allocating anyway
        uint32_t l = length();
        char* dest = reinterpret_cast<char*>(alloc.allocate(l + 1));
        memcpy(dest, ptr, l);
        dest[l] = '\0';
        return StringRef(dest, l);
    }

    char operator[](uint32_t index) const {
        ASSERT(index < length());
        return ptr[index];
    }

    explicit operator bool() const {
        return !empty();
    }

    std::ostream& operator<<(std::ostream& os) {
        if (!empty())
            os << std::string(ptr, length());
        return os;
    }

    friend bool operator==(const StringRef& lhs, const std::string& rhs) {
        if (lhs.length() != rhs.length())
            return false;

        return rhs.compare(0, rhs.length(), lhs.ptr, lhs.length()) == 0;
    }

    friend bool operator==(const StringRef& lhs, const StringRef& rhs) {
        if (lhs.length() != rhs.length())
            return false;

        return strncmp(lhs.ptr, rhs.ptr, std::min(lhs.length(), rhs.length())) == 0;
    }

    friend bool operator==(const StringRef& lhs, const char* rhs) {
        const char* ptr = lhs.ptr;
        uint32_t l = lhs.length();
        for (uint32_t i = 0; i < l; i++) {
            if (*ptr++ != *rhs++)
                return false;
        }

        // rhs should be null now, otherwise the lengths differ
        return *rhs == 0;
    }

    friend bool operator==(const std::string& lhs, const StringRef& rhs) { return operator==(rhs, lhs); }
    friend bool operator==(const char* lhs, const StringRef& rhs) { return operator==(rhs, lhs); }

    friend bool operator!=(const StringRef& lhs, const std::string& rhs) { return !operator==(lhs, rhs); }
    friend bool operator!=(const std::string& lhs, const StringRef& rhs) { return !operator==(lhs, rhs); }
    friend bool operator!=(const StringRef& lhs, const char* rhs) { return !operator==(lhs, rhs); }
    friend bool operator!=(const char* lhs, const StringRef& rhs) { return !operator==(lhs, rhs); }
    friend bool operator!=(const StringRef& lhs, const StringRef& rhs) { return !operator==(lhs, rhs); }

private:
    static const uint32_t NullMask = 1u << 31;
    static const uint64_t Seed = 0x3765936aa9a6c480; // chosen by fair dice roll

    const char* ptr;
    uint32_t count;

    void checkNullTerminator() {
        ASSERT((count & NullMask) == 0);
        if (count > 0 && ptr[count - 1] == '\0') {
            count--;
            count |= NullMask;
        }
    }
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