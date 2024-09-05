//------------------------------------------------------------------------------
//! @file SourceLocation.h
//! @brief Source element location tracking
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <filesystem>
#include <string>
#include <vector>

#include "slang/util/Hash.h"
#include "slang/util/Util.h"

namespace slang {

/// BufferID - Represents a source buffer.
///
/// Buffers can either be source code loaded from a file, assigned
/// from text in memory, or they can represent a macro expansion.
/// Each time a macro is expanded a new BufferID is allocated to track
/// the expansion location and original definition location.
struct SLANG_EXPORT BufferID {
    BufferID() = default;
    constexpr BufferID(uint32_t value, std::string_view name) :
#ifdef DEBUG
        name(name),
#endif
        id(value) {
        (void)name;
    }

    /// @return true if the ID is for a valid buffer, and false if not.
    [[nodiscard]] bool valid() const { return id != 0; }

    // Comparison operators are implemented manually so that we don't
    // bother comparing the buffer name in debug builds.
    bool operator==(const BufferID& rhs) const { return id == rhs.id; }
    std::strong_ordering operator<=>(const BufferID& rhs) const { return id <=> rhs.id; }

    /// @return an integer representing the raw buffer ID.
    constexpr uint32_t getId() const { return id; }

    /// @return true if the ID is for a valid buffer, and false if not.
    explicit operator bool() const { return valid(); }

    /// @return a placeholder buffer ID. It should be used only for
    /// locations where the buffer doesn't actually matter and won't
    /// be observed.
    static BufferID getPlaceholder() { return BufferID(UINT32_MAX, ""sv); }

#ifdef DEBUG
    std::string_view name;
#endif

private:
    uint32_t id = 0;
};

/// This class represents a location in source code (or within a macro expansion).
/// The SourceManager can decode this into file, line, and column information if
/// it's a file location, or into expanded and original locations if it's a
/// macro location.
class SLANG_EXPORT SourceLocation {
public:
    constexpr SourceLocation() : bufferID(0), charOffset(0) {}
    constexpr SourceLocation(BufferID buffer, uint64_t offset) :
#ifdef DEBUG
        bufferName(buffer.name),
#endif
        bufferID(buffer.getId()), charOffset(offset) {
    }

    /// @return an identifier for the buffer that contains this location.
    BufferID buffer() const {
#ifdef DEBUG
        return BufferID(bufferID, bufferName);
#else
        return BufferID(bufferID, ""sv);
#endif
    }

    /// @return the character offset of this location within the source buffer.
    [[nodiscard]] size_t offset() const { return (size_t)charOffset; }

    /// @return true if the location is valid, and false if not.
    [[nodiscard]] bool valid() const { return buffer().valid(); }

    /// @return true if the location is valid, and false if not.
    explicit operator bool() const { return valid(); }

    /// Computes a source location that is offset from the current one.
    /// Note that there is no error checking to ensure that the location
    /// still points to a valid place in the source.
    template<std::integral T>
    SourceLocation operator+(T delta) const {
        return SourceLocation(buffer(), size_t((T)charOffset + delta));
    }

    template<std::integral T>
    SourceLocation operator-(T delta) const {
        return SourceLocation(buffer(), size_t((T)charOffset - delta));
    }

    template<std::integral T>
    SourceLocation& operator+=(T delta) {
        charOffset = size_t((T)charOffset + delta);
        return *this;
    }

    template<std::integral T>
    SourceLocation& operator-=(T delta) {
        charOffset = size_t((T)charOffset - delta);
        return *this;
    }

    ptrdiff_t operator-(SourceLocation loc) const {
        SLANG_ASSERT(loc.buffer() == buffer());
        return (ptrdiff_t)charOffset - (ptrdiff_t)loc.charOffset;
    }

    bool operator==(const SourceLocation& rhs) const {
        // Implemented manually so that we don't bother comparing the
        // buffer name in debug builds.
        return bufferID == rhs.bufferID && charOffset == rhs.charOffset;
    }

    std::strong_ordering operator<=>(const SourceLocation& rhs) const {
        if (auto cmp = uint32_t(bufferID) <=> uint32_t(rhs.bufferID); cmp != 0)
            return cmp;
        return charOffset <=> rhs.charOffset;
    }

#ifdef DEBUG
    std::string_view bufferName;
#endif

    /// A location that is reserved to represent "no location" at all.
    static const SourceLocation NoLocation;

private:
    uint64_t bufferID : 28;
    uint64_t charOffset : 36;
};

#ifndef DEBUG
static_assert(sizeof(SourceLocation) == 8);
#endif

/// Combines a pair of source locations that denote a range of source text.
class SLANG_EXPORT SourceRange {
public:
    SourceRange() {}
    SourceRange(SourceLocation startLoc, SourceLocation endLoc) :
        startLoc(startLoc), endLoc(endLoc) {}

    /// @return the start of the range.
    SourceLocation start() const { return startLoc; }

    /// @return the end of the range.
    SourceLocation end() const { return endLoc; }

    /// @return true if @a location is within the range.
    bool contains(const SourceLocation& loc) const { return loc >= startLoc && loc < endLoc; }

    bool operator==(const SourceRange& rhs) const = default;

    /// A range that is reserved to represent "no location" at all.
    static const SourceRange NoLocation;

private:
    SourceLocation startLoc;
    SourceLocation endLoc;
};

/// @brief A named collection of source buffers that form a library.
///
/// Each buffer is associated with one library. Libraries are
/// uniqued by name, so identity for the rest of the program is
/// by object address, not by the name string.
struct SLANG_EXPORT SourceLibrary {
    /// The name of the library.
    std::string name;

    /// Additional include directories that are used when
    /// parsing files that are part of this library.
    std::vector<std::filesystem::path> includeDirs;

    /// The priority of this library relative to others in the
    /// search order. Lower numbers are higher priority.
    int priority = 0;

    /// Set to true if this is the default library.
    bool isDefault = false;

    /// Default constructor.
    SourceLibrary() = default;

    /// Constructs a new source library object with the given name.
    SourceLibrary(std::string&& name, int priority) : name(std::move(name)), priority(priority) {}
};

/// Represents a source buffer; that is, the actual text of the source
/// code along with an identifier for the buffer which potentially
/// encodes its include stack.
struct SLANG_EXPORT SourceBuffer {
    /// A view into the text comprising the buffer.
    std::string_view data;

    /// The library associated with the buffer.
    const SourceLibrary* library = nullptr;

    /// The ID assigned to the buffer.
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

template<>
struct hash<slang::SourceRange> {
    size_t operator()(const slang::SourceRange& obj) const {
        size_t seed = 0;
        slang::hash_combine(seed, obj.start());
        slang::hash_combine(seed, obj.end());
        return seed;
    }
};

} // namespace std
