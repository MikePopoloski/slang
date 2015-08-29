#pragma once

// Simple block allocator that can't deallocate individual items.
// When none of the memory is needed anymore, the whole thing can be freed.

namespace slang {

class Allocator final {
public:
    explicit Allocator(uint32_t segmentSize = 8192)
        : segmentSize(segmentSize + sizeof(Segment)) {

        head = NewSegment(nullptr, this->segmentSize);
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

    template<typename T, typename... Args>
    T* Allocate(Args&&... args) {
        return new (Allocate(sizeof(T))) T(std::forward<Args>(args)...);
    }

    template<typename T>
    T* Copy(T* source, uint32_t count) {
        T* newArray = reinterpret_cast<T*>(Allocate(count * sizeof(T)));
        for (uint32_t i = 0; i < count; i++)
            new (&newArray[i]) T(*source++);
        return newArray;
    }

    template<typename T>
    T* AllocateArray(uint32_t count) {
        static_assert(std::is_pod<T>::value, "Array type must be POD");
        return reinterpret_cast<T*>(Allocate(count * sizeof(T)));
    }

    uint8_t* Allocate(uint32_t size) {
        // simple case: we have room in the current block
        uint8_t* result = head->current;
        uint8_t* next = head->current + size;
        if (next <= endPtr) {
            head->current = next;
            return result;
        }

        // for really large allocations, give them their own segment
        if (size > (segmentSize >> 1)) {
            head->prev = NewSegment(head->prev, size + sizeof(Segment));
            return head->prev->current;
        }

        // otherwise, allocate a new block
        head = NewSegment(head, segmentSize);
        return Allocate(size);
    }

private:
    struct Segment {
        Segment* prev;
        uint8_t* current;
    };

    Segment* head;
    uint8_t* endPtr;
    uint32_t segmentSize;

    static Segment* NewSegment(Segment* prev, uint32_t size) {
        auto seg = (Segment*)malloc(size);
        seg->prev = prev;
        seg->current = (uint8_t*)seg + sizeof(Segment);

        return seg;
    }
};

}