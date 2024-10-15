//------------------------------------------------------------------------------
//! @file BumpAllocator.h
//! @brief Fast allocator based on pointer bumping
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <cstring>
#include <new>
#include <span>
#include <type_traits>

#include "slang/util/Util.h"

namespace slang {

/// BumpAllocator - Fast O(1) allocator.
///
/// Allocates items sequentially in memory, with underlying memory allocated in
/// blocks as needed. Individual items cannot be deallocated; the entire thing
/// must be destroyed to release the memory.
class SLANG_EXPORT BumpAllocator {
public:
    BumpAllocator();
    ~BumpAllocator();

    BumpAllocator(BumpAllocator&& other) noexcept;
    BumpAllocator& operator=(BumpAllocator&& other) noexcept;

    BumpAllocator(const BumpAllocator&) = delete;
    BumpAllocator& operator=(const BumpAllocator&) = delete;

    /// Construct a new item using the allocator.
    /// NOTE: the type of object being created must be trivially destructible,
    /// since the allocator won't run destructors when freeing memory.
    template<typename T, typename... Args>
    T* emplace(Args&&... args) {
        static_assert(std::is_trivially_destructible_v<T>);
        return new (allocate(sizeof(T), alignof(T))) T(std::forward<Args>(args)...);
    }

    /// Allocate @a size bytes of memory with the given @a alignment.
    byte* allocate(size_t size, size_t alignment) {
        byte* base = alignPtr(head->current, alignment);
        byte* next = base + size;
        if (next > endPtr)
            return allocateSlow(size, alignment);

        head->current = next;
        return base;
    }

    /// Copies the contents of the given span into a new memory region
    /// allocated and owned by this allocator and returns a span pointing to it.
    template<typename T>
    [[nodiscard]] std::span<T> copyFrom(std::span<const T> src) {
        auto len = src.size();
        if (len == 0)
            return {};

        auto dest = reinterpret_cast<T*>(allocate(len * sizeof(T), alignof(T)));
        std::memcpy(dest, src.data(), len * sizeof(T));

        return std::span<T>(dest, len);
    }

    /// Steals ownership of all of the memory contents of the given allocator.
    /// The other allocator will be in a moved-from state after the call.
    void steal(BumpAllocator&& other);

protected:
    // Allocations are tracked as a linked list of segments.
    struct Segment {
        Segment* prev;
        byte* current;
    };

    Segment* head;
    byte* endPtr;

    enum { INITIAL_SIZE = 512, SEGMENT_SIZE = 4096 };

    // Slow path handling of allocation.
    byte* allocateSlow(size_t size, size_t alignment);

    static byte* alignPtr(byte* ptr, size_t alignment) {
        return reinterpret_cast<byte*>((reinterpret_cast<uintptr_t>(ptr) + alignment - 1) &
                                       ~(alignment - 1));
    }

    static Segment* allocSegment(Segment* prev, size_t size);
};

/// A strongly-typed version of the BumpAllocator, which has the additional
/// behavior of calling destructors on all elements when the allocator
/// itself is destructed.
template<typename T>
class TypedBumpAllocator : public BumpAllocator {
public:
    TypedBumpAllocator() = default;
    TypedBumpAllocator(TypedBumpAllocator&& other) noexcept : BumpAllocator(std::move(other)) {}
    ~TypedBumpAllocator() {
        Segment* seg = head;
        while (seg) {
            for (T* cur = (T*)(seg + 1); cur != (T*)seg->current; cur++)
                cur->~T();
            seg = seg->prev;
        }
    }

    /// Construct a new item using the allocator.
    template<typename... Args>
    T* emplace(Args&&... args) {
        return new (allocate(sizeof(T), alignof(T))) T(std::forward<Args>(args)...);
    }
};

} // namespace slang
