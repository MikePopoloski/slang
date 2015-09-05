#pragma once

// Immutable wrapper around a {pointer, length} pair to a string.
// This class does not own the string memory; it's up to the user
// to make sure it remains valid.

namespace slang {

class StringRef {
public:
    StringRef() :
        ptr(nullptr), len(0) {
    }

    StringRef(std::nullptr_t) :
        ptr(nullptr), len(0) {
    }

    StringRef(const char* ptr, uint32_t length) :
        ptr(ptr), len(length) {
    }

    StringRef(const std::string& str) :
        ptr(str.c_str()), len(str.length()) {
    }

    StringRef(const Buffer<char>& buffer) :
        ptr(buffer.cbegin()), len(buffer.count()) {
    }

    // this constructor is meant for string literals
    template<size_t N>
    StringRef(const char(&str)[N]) :
        ptr(str), len(N - 1) {
    }

    const char* begin() const { return ptr; }
    const char* end() const { return ptr + len; }

    uint32_t length() const { return len; }
    bool empty() const { return len == 0; }
    bool isNullTerminated() const { return ptr != nullptr && ptr[len] == '\0'; }

    StringRef subString(uint32_t startIndex) const {
        ASSERT(startIndex <= len);
        return subString(startIndex, len - startIndex);
    }

    StringRef subString(uint32_t startIndex, uint32_t length) const {
        ASSERT(startIndex + length <= len);
        return StringRef(ptr + startIndex, length);
    }

    size_t hash(size_t seed = Seed) const {
        if (empty())
            return 0;
        return slang::xxhash(ptr, len, seed);
    }

    StringRef intern(Allocator& alloc) const {
        if (empty())
            return StringRef();

        // +1 for trailing zero, which we might as well add here since we're allocating anyway
        char* dest = reinterpret_cast<char*>(alloc.allocate(len + 1));
        memcpy(dest, ptr, len);
        dest[len] = '\0';
        return StringRef(dest, len);
    }

    char operator[](uint32_t index) const {
        ASSERT(index < len);
        return ptr[index];
    }

    explicit operator bool() const {
        return !empty();
    }

    friend bool operator==(const StringRef& lhs, const std::string& rhs) {
        if (lhs.len != rhs.length())
            return false;

        return rhs.compare(0, rhs.length(), lhs.ptr, lhs.len) == 0;
    }

    friend bool operator==(const StringRef& lhs, const StringRef& rhs) {
        if (lhs.len != rhs.len)
            return false;

        return strncmp(lhs.ptr, rhs.ptr, std::min(lhs.len, rhs.len)) == 0;
    }

    friend bool operator==(const StringRef& lhs, const char* rhs) {
        const char* ptr = lhs.ptr;
        for (uint32_t i = 0; i < lhs.len; i++) {
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
    static const uint64_t Seed = 0x3765936aa9a6c480; // chosen by fair dice roll

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