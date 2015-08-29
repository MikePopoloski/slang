#pragma once

// Simple block allocator that can't deallocate individual items.
// When none of the memory is needed anymore, the whole thing can be freed.

namespace slang {

class Allocator {
public:
    explicit Allocator(uint32_t segmentSize = 8192)
        : segmentSize(segmentSize + sizeof(Segment)) {

        head = allocSegment(nullptr, this->segmentSize);
        endPtr = (uint8_t*)head + this->segmentSize;
    }

    ~Allocator() {
        Segment* seg = head;
        while (seg) {
            Segment* prev = seg->prev;
            free(seg);
            seg = prev;
        }
    }

    Allocator(const Allocator&) = delete;
    Allocator& operator=(const Allocator&) = delete;

    template<typename T, typename... Args>
    T* emplace(Args&&... args) {
        return new (allocate(sizeof(T))) T(std::forward<Args>(args)...);
    }

    uint8_t* allocate(uint32_t size) {
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
        return allocate(size);
    }

private:
    struct Segment {
        Segment* prev;
        uint8_t* current;
    };

    Segment* head;
    uint8_t* endPtr;
    uint32_t segmentSize;

    static Segment* allocSegment(Segment* prev, uint32_t size) {
        auto seg = (Segment*)malloc(size);
        seg->prev = prev;
        seg->current = (uint8_t*)seg + sizeof(Segment);

        return seg;
    }
};

}