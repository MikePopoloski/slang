#pragma once

namespace slang {

class SourceManager;

struct BufferID {
    bool valid() const { return id != 0; }
    bool operator==(const BufferID& rhs) const { return id == rhs.id; }
    bool operator!=(const BufferID& rhs) const { return !(*this == rhs); }

    explicit operator bool() const {
        return valid();
    }
    uint32_t id = 0;

protected:
    static BufferID get(uint32_t value) {
        BufferID result;
        result.id = value;
        return result;
    }
    uint32_t getValue() const { return id; }

private:
    friend class SourceManager;
};

// Represents a location in source code. The SourceManager can decode this into
// file, line, and column information.

class SourceLocation {
public:
    SourceLocation() : offset(0) {}
    SourceLocation(BufferID buffer, uint32_t offset) :
        buffer(buffer), offset(offset)
    {
    }

    bool isValid() const { return offset != 0; }

    bool operator ==(const SourceLocation& rhs) {
        return offset == rhs.offset;
    }

    bool operator !=(const SourceLocation& rhs) {
        return offset != rhs.offset;
    }

    bool operator <(const SourceLocation& rhs) {
        return offset < rhs.offset;
    }
    BufferID buffer;
    uint32_t offset;

private:
};

}