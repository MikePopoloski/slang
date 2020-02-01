//------------------------------------------------------------------------------
//! @file SourceLocation.h
//! @brief Source element location tracking
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Hash.h"
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
    BufferID() = default;
    constexpr BufferID(uint32_t value, string_view name) :
#ifdef DEBUG
        name(name),
#endif
        id(value) {
        (void)name;
    }

    bool valid() const { return id != 0; }

    bool operator==(const BufferID& rhs) const { return id == rhs.id; }
    bool operator!=(const BufferID& rhs) const { return !(*this == rhs); }
    bool operator<(const BufferID& rhs) const { return id < rhs.id; }
    bool operator<=(const BufferID& rhs) const { return id <= rhs.id; }
    bool operator>(const BufferID& rhs) const { return rhs < *this; }
    bool operator>=(const BufferID& rhs) const { return rhs <= *this; }

    constexpr uint32_t getId() const { return id; }

    explicit operator bool() const { return valid(); }

    static BufferID getPlaceholder() { return BufferID(UINT32_MAX, ""sv); }

#ifdef DEBUG
    string_view name;
#endif

private:
    uint32_t id = 0;
};

/// This class represents a location in source code (or within a macro expansion).
/// The SourceManager can decode this into file, line, and column information if
/// it's a file location, or into expanded and original locations if it's a
/// macro location.
class SourceLocation {
public:
    constexpr SourceLocation() : bufferID(0), charOffset(0) {}
    constexpr SourceLocation(BufferID buffer, size_t offset) :
#ifdef DEBUG
        bufferName(buffer.name),
#endif
        bufferID(buffer.getId()), charOffset(offset) {
    }

    BufferID buffer() const {
#ifdef DEBUG
        return BufferID(bufferID, bufferName);
#else
        return BufferID(bufferID, ""sv);
#endif
    }

    size_t offset() const { return charOffset; }
    bool valid() const { return buffer().valid(); }

    explicit operator bool() const { return valid(); }

    /// Computes a source location that is offset from the current one.
    /// Note that there is no error checking to ensure that the location
    /// still points to a valid place in the source.
    template<typename T, typename = std::enable_if_t<std::is_integral_v<T>>>
    SourceLocation operator+(T delta) const {
        return SourceLocation(buffer(), size_t((T)charOffset + delta));
    }

    template<typename T, typename = std::enable_if_t<std::is_integral_v<T>>>
    SourceLocation operator-(T delta) const {
        return SourceLocation(buffer(), size_t((T)charOffset - delta));
    }

    ptrdiff_t operator-(SourceLocation loc) const {
        ASSERT(loc.buffer() == buffer());
        return (ptrdiff_t)charOffset - (ptrdiff_t)loc.charOffset;
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

    bool operator>=(const SourceLocation& rhs) const { return !(*this < rhs); }

#ifdef DEBUG
    string_view bufferName;
#endif

    static const SourceLocation NoLocation;

private:
    uint64_t bufferID : 28;
    uint64_t charOffset : 36;
};

inline constexpr const SourceLocation SourceLocation::NoLocation{ BufferID((1u << 28) - 1, ""),
                                                                  (1ull << 36) - 1 };

#ifndef DEBUG
static_assert(sizeof(SourceLocation) == 8);
#endif

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

/// Represents a source buffer; that is, the actual text of the source
/// code along with an identifier for the buffer which potentially
/// encodes its include stack.
struct SourceBuffer {
    string_view data;
    BufferID id;

    explicit operator bool() const { return id.valid(); }
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
