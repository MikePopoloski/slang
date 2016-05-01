#pragma once

#include "Handle.h"

namespace slang {

class SourceManager;

struct FileID : public HandleBase<FileID> {
    friend class SourceManager;
};

// Represents a location in source code. The SourceManager can decode this into
// file, line, and column information.

class SourceLocation {
public:
    SourceLocation() : offset(0) {}
    SourceLocation(FileID file, uint32_t offset) :
        file(file), offset(offset)
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
    FileID file;
    uint32_t offset;

private:
};

}