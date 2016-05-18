#include "BumpAllocator.h"

#include <cstdlib>

namespace slang {

BumpAllocator::BumpAllocator(uint32_t segmentSize) :
    segmentSize(segmentSize + sizeof(Segment))
{
    head = allocSegment(nullptr, this->segmentSize);
    endPtr = (uint8_t*)head + this->segmentSize;
}

BumpAllocator::~BumpAllocator() {
    Segment* seg = head;
    while (seg) {
        Segment* prev = seg->prev;
        free(seg);
        seg = prev;
    }
}

uint8_t* BumpAllocator::allocate(uint32_t size) {
    // simple case: we have room in the current block
    uint8_t* result = head->current;
    uint8_t* next = head->current + size;
    if (next <= endPtr) {
        head->current = next;
        return result;
    }

    // for really large allocations, give them their own segment
    if (size > (segmentSize >> 1)) {
        head->prev = allocSegment(head->prev, size + sizeof(Segment));
        return head->prev->current;
    }

    // otherwise, allocate a new block
    head = allocSegment(head, segmentSize);
    endPtr = (uint8_t*)head + segmentSize;
    return allocate(size);
}

BumpAllocator::Segment* BumpAllocator::allocSegment(Segment* prev, uint32_t size) {
    auto seg = (Segment*)malloc(size);
    seg->prev = prev;
    seg->current = (uint8_t*)seg + sizeof(Segment);

    return seg;
}

}
