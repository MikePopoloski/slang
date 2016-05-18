#pragma once

#include <deque>

#include "Buffer.h"

namespace slang {

// TODO: clean this up

template<typename T>
class BufferPool {
public:
    BufferPool() {}
    ~BufferPool() {
        for (auto& buffer : buffers)
            delete buffer;
    }

    template<typename TWrapped>
    struct BufferWrapper {
        BufferPool* pool;
        Buffer<TWrapped>* buffer;

        BufferWrapper(BufferPool* pool, Buffer<TWrapped>* buffer) : pool(pool), buffer(buffer) {}
        ~BufferWrapper() { pool->free(buffer); }

        bool empty() const { return buffer->empty(); }

        void append(const TWrapped& item) { buffer->append(item); }
        void appendRange(const TWrapped* begin, const TWrapped* end) { buffer->appendRange(begin, end); }

        template<typename Container>
        void appendRange(const Container& container) { buffer->appendRange(container); }

        template<typename... Args>
        void emplace(Args&&... args) { buffer->emplace<Args...>(std::forward<Args>(args)...); }

        void clear() { buffer->clear(); }

        ArrayRef<TWrapped> copy(BumpAllocator& alloc) const { return buffer->copy(alloc); }

        Buffer<TWrapped>& get() { return *buffer; }

        operator Buffer<TWrapped>&() { return *buffer; }
    };

    BufferWrapper<T> get() {
        if (buffers.empty())
            return BufferWrapper<T>(this, new Buffer<T>());

        Buffer<T>* result = buffers.back();
        buffers.pop_back();
        result->clear();
        return BufferWrapper<T>(this, result);
    }

    // potentially unsafe; only use this for compatible types (pointers, etc)
    template<typename U>
    BufferWrapper<U> getAs() {
        if (buffers.empty())
            return BufferWrapper<U>(this, (Buffer<U>*)new Buffer<T>());

        Buffer<T>* result = buffers.back();
        buffers.pop_back();
        result->clear();
        return BufferWrapper<U>(this, (Buffer<U>*)result);
    }

    void free(void* buffer) {
        buffers.push_back((Buffer<T>*)buffer);
    }

private:
    std::deque<Buffer<T>*> buffers;
};

}
