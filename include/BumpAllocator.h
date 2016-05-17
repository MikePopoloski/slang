#pragma once

#include <cstdint>
#include <utility>

// Simple bump allocator that can't deallocate individual items.
// When none of the memory is needed anymore, the whole thing can be freed.

namespace slang {

class BumpAllocator {
public:
    explicit BumpAllocator(uint32_t segmentSize = 8192);
    ~BumpAllocator();

    BumpAllocator(const BumpAllocator&) = delete;
    BumpAllocator& operator=(const BumpAllocator&) = delete;

    template<typename T, typename... Args>
    T* emplace(Args&&... args) {
        return new (allocate(sizeof(T))) T(std::forward<Args>(args)...);
    }

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