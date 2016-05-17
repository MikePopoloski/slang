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

    template<typename T>
    struct BufferWrapper {
        BufferPool* pool;
        Buffer<T>* buffer;

        BufferWrapper(BufferPool* pool, Buffer<T>* buffer) : pool(pool), buffer(buffer) {}
        ~BufferWrapper() { pool->free(buffer); }

        bool empty() const { return buffer->empty(); }

        void append(const T& item) { buffer->append(item); }
        void appendRange(const T* begin, const T* end) { buffer->appendRange(begin, end); }

        template<typename Container>
        void appendRange(const Container& container) { buffer->appendRange(container); }

        template<typename... Args>
        void emplace(Args&&... args) { buffer->emplace<Args...>(std::forward<Args>(args)...); }

        void clear() { buffer->clear(); }

        ArrayRef<T> copy(BumpAllocator& alloc) const { return buffer->copy(alloc); }

        Buffer<T>& get() { return *buffer; }

        operator Buffer<T>&() { return *buffer; }
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