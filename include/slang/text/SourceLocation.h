//------------------------------------------------------------------------------
// SourceLocation.h
// Source element location tracking.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang {

class SourceManager;

/// BufferID - Represents a source buffer.
///
/// Buffers can either be source code loaded from a file, assigned
/// from text in memory, or they can represent a macro expansion.
/// Each time a macro is expanded a new BufferID is allocated to track
/// the expansion location and original definition location.
struct BufferID {
    bool valid() const { return id != 0; }

    bool operator==(const BufferID& rhs) const { return id == rhs.id; }
    bool operator!=(const BufferID& rhs) const { return !(*this == rhs); }
    bool operator<(const BufferID& rhs) const { return id < rhs.id; }
    bool operator<=(const BufferID& rhs) const { return id <= rhs.id; }
    bool operator>(const BufferID& rhs) const { return rhs < *this; }
    bool operator>=(const BufferID& rhs) const { return rhs <= *this; }

    uint32_t getId() const { return id; }

    explicit operator bool() const { return valid(); }

private:
    uint32_t id = 0;

    static BufferID get(uint32_t value) {
        BufferID result;
        result.id = value;
        return result;
    }
    uint32_t getValue() const { return id; }

    friend class SourceManager;
};

/// This class represents a location in source code (or within a macro expansion).
/// The SourceManager can decode this into file, line, and column information if
/// it's a file location, or into expanded and original locations if it's a
/// macro location.
class SourceLocation {
public:
    SourceLocation() : charOffset(0) {}
    SourceLocation(BufferID buffer, uint32_t offset) : bufferID(buffer), charOffset(offset) {}

    BufferID buffer() const { return bufferID; }
    uint32_t offset() const { return charOffset; }
    bool valid() const { return bufferID.valid(); }

    explicit operator bool() const { return valid(); }

    /// Computes a source location that is offset from the current one.
    /// Note that there is no error checking to ensure that the location
    /// still points to a valid place in the source.
    template<typename T, typename = std::enable_if_t<std::is_integral_v<T>>>
    SourceLocation operator+(T delta) const {
        return SourceLocation(bufferID, (uint32_t)((T)charOffset + delta));
    }

    template<typename T, typename = std::enable_if_t<std::is_integral_v<T>>>
    SourceLocation operator-(T delta) const {
        return SourceLocation(bufferID, (uint32_t)((T)charOffset - delta));
    }

   int64_t operator-(SourceLocation loc) const {
        ASSERT(loc.buffer() == bufferID);
        return (int64_t)charOffset - (int64_t)loc.charOffset;
    }

    bool operator==(const SourceLocation& rhs) const {
        return bufferID == rhs.bufferID && charOffset == rhs.charOffset;
    }

    bool operator!=(const SourceLocation& rhs) const { return !(*this == rhs); }

    bool operator<(const SourceLocation& rhs) const {
        if (bufferID != rhs.bufferID)
            return bufferID < rhs.bufferID;
        return charOffset < rhs.charOffset;
    }

private:
    BufferID bufferID;
    uint32_t charOffset;
};

/// Combines a pair of source locations that denote a range of source text.
/// This is mostly used for diagnostic reporting purposes.
class SourceRange {
public:
    SourceRange() {}
    SourceRange(SourceLocation startLoc, SourceLocation endLoc) :
        startLoc(startLoc), endLoc(endLoc) {}

    SourceLocation start() const { return startLoc; }
    SourceLocation end() const { return endLoc; }

private:
    SourceLocation startLoc;
    SourceLocation endLoc;
};

} // namespace slang

namespace std {

template<>
struct hash<slang::BufferID> {
    size_t operator()(const slang::BufferID& obj) const { return obj.getId(); }
};

template<>
struct hash<slang::SourceLocation> {
    size_t operator()(const slang::SourceLocation& obj) const {
        size_t seed = 0;
        slang::hash_combine(seed, obj.buffer());
        slang::hash_combine(seed, obj.offset());
        return seed;
    }
};

} // namespace std
