//------------------------------------------------------------------------------
// BumpAllocator.h
// Fast allocator based on pointer bumping.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>
#include <utility>

namespace slang {

/// BumpAllocator - Fast O(1) allocator.
///
/// Allocates items sequentially in memory, with underlying memory allocated in
/// blocks of a configurable size. Individual items cannot be deallocated;
/// the entire thing must be destroyed to release the memory.
class BumpAllocator {
public:
    /// Constructs a new allocator with the given segment size. It's probably a good idea
    /// to make the segment size a multiple of the page size.
    explicit BumpAllocator(uint32_t segmentSize = 8192);
    ~BumpAllocator();

    BumpAllocator(BumpAllocator&& other) = default;
    BumpAllocator& operator=(BumpAllocator&& other) = default;

    BumpAllocator(const BumpAllocator&) = delete;
    BumpAllocator& operator=(const BumpAllocator&) = delete;

    /// Construct a new item using the allocator.
    template<typename T, typename... Args>
    T* emplace(Args&&... args) {
        return new (allocate(sizeof(T))) T(std::forward<Args>(args)...);
    }

    /// Allocate @a size bytes of memory.
    uint8_t* allocate(uint32_t size);

private:
    struct Segment {
        Segment* prev;
        uint8_t* current;
    };

    Segment* head;
    uint8_t* endPtr;
    uint32_t segmentSize;

    static Segment* allocSegment(Segment* prev, uint32_t size);
};

}
