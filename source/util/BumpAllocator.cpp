//------------------------------------------------------------------------------
// BumpAllocator.cpp
// Fast allocator based on pointer bumping
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/util/BumpAllocator.h"

#include <new>

namespace slang {

BumpAllocator::BumpAllocator() {
    head = allocSegment(nullptr, INITIAL_SIZE);
    endPtr = (byte*)head + INITIAL_SIZE;
}

BumpAllocator::~BumpAllocator() {
    Segment* seg = head;
    while (seg) {
        Segment* prev = seg->prev;
        ::operator delete(seg);
        seg = prev;
    }
}

BumpAllocator::BumpAllocator(BumpAllocator&& other) noexcept :
    head(std::exchange(other.head, nullptr)), endPtr(other.endPtr) {
}

BumpAllocator& BumpAllocator::operator=(BumpAllocator&& other) noexcept {
    if (this != &other) {
        this->~BumpAllocator();
        new (this) BumpAllocator(std::move(other));
    }
    return *this;
}

void BumpAllocator::steal(BumpAllocator&& other) {
    Segment* seg = other.head;
    if (!seg)
        return;

    while (seg->prev)
        seg = seg->prev;

    seg->prev = head->prev;
    head->prev = std::exchange(other.head, nullptr);
}

byte* BumpAllocator::allocateSlow(size_t size, size_t alignment) {
    // for really large allocations, give them their own segment
    if (size > (SEGMENT_SIZE >> 1)) {
        size = (size + alignment - 1) & ~(alignment - 1);
        head->prev = allocSegment(head->prev, size + sizeof(Segment));
        return alignPtr(head->prev->current, alignment);
    }

    // otherwise, start a new block
    head = allocSegment(head, SEGMENT_SIZE);
    endPtr = (byte*)head + SEGMENT_SIZE;
    return allocate(size, alignment);
}

BumpAllocator::Segment* BumpAllocator::allocSegment(Segment* prev, size_t size) {
    auto seg = (Segment*)::operator new(size);
    seg->prev = prev;
    seg->current = (byte*)seg + sizeof(Segment);
    return seg;
}

} // namespace slang
