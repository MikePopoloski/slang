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

private:
    const char* ptr;
    uint32_t length;
};

}