//------------------------------------------------------------------------------
// StringRef.cpp
// Lighweight view of a string.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "StringRef.h"

#include <algorithm>
#include <cstring>

#include "BumpAllocator.h"
#include "Debug.h"
#include "Hash.h"

namespace slang {

StringRef::StringRef() :
    ptr(nullptr), len(0)
{
}

StringRef::StringRef(std::nullptr_t) :
    ptr(nullptr), len(0)
{
}

StringRef::StringRef(const char* ptr, uint32_t length) :
    ptr(ptr), len(length)
{
}

StringRef::StringRef(const std::string& str) :
    ptr(str.c_str()), len((uint32_t)str.length())
{
}

StringRef StringRef::subString(uint32_t startIndex) const {
    ASSERT(startIndex <= len);
    return subString(startIndex, len - startIndex);
}

StringRef StringRef::subString(uint32_t startIndex, uint32_t subStringLength) const {
    ASSERT(startIndex + subStringLength <= len);
    return StringRef(ptr + startIndex, subStringLength);
}

size_t StringRef::hash(size_t seed) const {
    if (empty())
        return 0;
    return slang::xxhash(ptr, len, seed);
}

StringRef StringRef::intern(BumpAllocator& alloc) const {
    if (empty())
        return StringRef();

    char* dest = reinterpret_cast<char*>(alloc.allocate(len));
    memcpy(dest, ptr, len);
    return StringRef(dest, len);
}

std::string StringRef::toString() const {
    return std::string(ptr, len);
}

char StringRef::operator[](uint32_t index) const {
    ASSERT(index < len);
    return ptr[index];
}

std::ostream& operator<<(std::ostream& os, const StringRef& rhs) {
    if (rhs)
        os << std::string(rhs.ptr, rhs.len);
    return os;
}

bool operator==(const StringRef& lhs, const std::string& rhs) {
    if (lhs.len != rhs.length())
        return false;

    return rhs.compare(0, rhs.length(), lhs.ptr, lhs.len) == 0;
}

bool operator==(const StringRef& lhs, const StringRef& rhs) {
    if (lhs.len != rhs.len)
        return false;

    return strncmp(lhs.ptr, rhs.ptr, std::min(lhs.len, rhs.len)) == 0;
}

bool operator==(const StringRef& lhs, const char* rhs) {
    if (!rhs)
        return lhs.empty();

    const char* ptr = lhs.ptr;
    for (uint32_t i = 0; i < lhs.len; i++) {
        if (*ptr++ != *rhs++)
            return false;
    }

    // rhs should be null now, otherwise the lengths differ
    return *rhs == 0;
}

}