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
    class BufferWrapper {
    public:
        BufferWrapper(BufferPool<T>* pool, Buffer<TWrapped>* buffer) : pool(pool), buffer(buffer) {}
        ~BufferWrapper() { pool->free(buffer); }

        Buffer<TWrapped>& get() { return *buffer; }
        Buffer<TWrapped>* operator->() { return buffer; }
        operator Buffer<TWrapped>&() { return *buffer; }

    private:
        BufferPool<T>* pool;
        Buffer<TWrapped>* buffer;
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
