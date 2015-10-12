#pragma once

#include "Buffer.h"

namespace slang {

template<typename T>
class BufferPool {
public:
    BufferPool() {}
    ~BufferPool() {
        for (auto& buffer : buffers)
            delete buffer;
    }

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

        ArrayRef<T> copy(BumpAllocator& alloc) const { return buffer->copy(alloc); }

        Buffer<T>& get() { return *buffer; }

        operator Buffer<T>&() { return *buffer; }
    };

    BufferWrapper get() {
        if (buffers.empty())
            return BufferWrapper(this, new Buffer<T>());

        Buffer<T>* result = buffers.back();
        buffers.pop_back();
        result->clear();
        return BufferWrapper(this, result);
    }

    void free(Buffer<T>* buffer) {
        buffers.push_back(buffer);
    }

private:
    std::deque<Buffer<T>*> buffers;
};

}