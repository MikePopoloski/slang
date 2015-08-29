#pragma once

namespace slang {

class StringRef {
public:
    StringRef() 
        : ptr(nullptr), length(0) {
    }

    StringRef(const char* ptr, uint32_t length)
        : ptr(ptr), length(length) {
    }

    void CopyTo(std::string& buffer) const {
        buffer.append(ptr, length);
    }

    const char* Ptr() const { return ptr; }
    uint32_t Length() const { return length; }

    inline friend bool operator ==(const StringRef& lhs, const std::string& rhs) {
        return rhs.compare(0, rhs.size(), lhs.Ptr(), lhs.Length()) == 0;
    }

private:
    const char* ptr;
    uint32_t length;
};

}