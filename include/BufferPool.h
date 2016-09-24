//------------------------------------------------------------------------------
// BufferPool.h
// Pool of allocated Buffers that can be loaned out for temporary operations.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <memory>
#include <vector>

#include "Buffer.h"

namespace slang {

/// The point of BufferPool<T> is to avoid allocating new buffer memory all over the
/// place whenever we need a temporary little array to hold something. Once we've built
/// up a dynamically sized list and know exactly how large it should be, we call copy()
/// to allocate a fized size array. The temporary Buffer can then be returned and reused.
template<typename T>
class BufferPool {
public:
    BufferPool() {}

    // not copyable
    BufferPool(const BufferPool&) = delete;
    BufferPool& operator=(const BufferPool&) = delete;

    /// Simple RAII wrapper so that pooled buffers get returned automatically at the end of a scope.
    template<typename TWrapped>
    struct BufferWrapper {
        BufferPool<T>* pool;
        Buffer<TWrapped>* buffer;

        BufferWrapper(BufferPool<T>* pool, Buffer<TWrapped>* buffer) : pool(pool), buffer(buffer) {}
        ~BufferWrapper() { pool->free(buffer); }

        bool empty() const { return buffer->empty(); }
        T* begin() { return buffer->begin(); }
        T* end() { return buffer->end(); }

        T& back() {
            return buffer->back();
        }

        void pop() {
            buffer->pop();
        }

        void append(const TWrapped& item) { buffer->append(item); }
        void appendRange(const TWrapped* begin, const TWrapped* end) { buffer->appendRange(begin, end); }

        template<typename Container>
        void appendRange(const Container& container) { buffer->appendRange(container); }

        template<typename... Args>
        void emplace(Args&&... args) { buffer->emplace(std::forward<Args>(args)...); }

        void clear() { buffer->clear(); }

        ArrayRef<TWrapped> copy(BumpAllocator& alloc) const { return buffer->copy(alloc); }

        Buffer<TWrapped>& get() { return *buffer; }

        operator Buffer<TWrapped>&() { return *buffer; }
    };

    /// Get a buffer from the pool. If there aren't any available, a new one
    /// will be allocated first.
    BufferWrapper<T> get() {
        if (buffers.empty())
            return BufferWrapper<T>(this, makeNew());

        Buffer<T>* result = buffers.back();
        buffers.pop_back();
        result->clear();
        return BufferWrapper<T>(this, result);
    }

    /// Gets a buffer from the pool but reinterprets the type of data in the
    /// buffer. This is inherently unsafe; only use this for types that you
    /// know will be compatible (like pointers).
    ///
    /// This mostly exists so that we can have one BufferPool<SyntaxNode*> and use
    /// it for all types derived from SyntaxNode.
    template<typename U>
    BufferWrapper<U> getAs() {
        if (buffers.empty())
            return BufferWrapper<U>(this, (Buffer<U>*)makeNew());

        Buffer<T>* result = buffers.back();
        buffers.pop_back();
        result->clear();
        return BufferWrapper<U>(this, (Buffer<U>*)result);
    }

    /// Returns a buffer to the pool.
    void free(void* buffer) {
        buffers.push_back((Buffer<T>*)buffer);
    }

private:
    Buffer<T>* makeNew() {
        backingMem.emplace_back(new Buffer<T>());
        return backingMem.back().get();
    }

    std::vector<std::unique_ptr<Buffer<T>>> backingMem;
    std::vector<Buffer<T>*> buffers;
};

}
