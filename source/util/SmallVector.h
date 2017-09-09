//------------------------------------------------------------------------------
// SmallVector.h
// Implements fast resizable array template.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <cstdlib>
#include <cstring>
#include <iterator>

#include "span.h"
#include "BumpAllocator.h"
#include "Debug.h"

namespace slang {

/// SmallVector<T> - A fast growable array.
///
/// SmallVector a vector-like growable array that allocates its first N elements
/// on the stack. As long as you don't need more room than that, there are no
/// heap allocations. Otherwise we spill over into the heap. This is the base class
/// for the actual sized implementation; it's split apart so that this one can be
/// used in more general interfaces that don't care about the explicit stack size.
template<typename T>
class SmallVector {
public:
    T* begin() { return data; }
    T* end() { return data + len; }
    const T* begin() const { return data; }
    const T* end() const { return data + len; }
    const T* cbegin() const { return data; }
    const T* cend() const { return data + len; }

    const T& front() const {
        ASSERT(len);
        return data[0];
    }

    const T& back() const {
        ASSERT(len);
        return data[len - 1];
    }

    T& front() {
        ASSERT(len);
        return data[0];
    }

    T& back() {
        ASSERT(len);
        return data[len - 1];
    }

    uint32_t size() const { return len; }
    bool empty() const { return len == 0; }

    /// Clear all elements but retain underlying storage.
    void clear() {
        destructElements();
        len = 0;
    }

    /// Remove the last element from the array. Asserts if empty.
    void pop() {
        ASSERT(len);
        len--;
        data[len].~T();
    }

    /// Add an element to the end of the array.
    void append(const T& item) {
        amortizeCapacity();
        new (&data[len++]) T(item);
    }

    /// Add a range of elements to the end of the array.
    template<typename Container>
    void appendRange(const Container& container) {
        appendIterator(std::begin(container), std::end(container));
    }

    /// Add a range of elements to the end of the array.
    void appendRange(const T* begin, const T* end) {
        if (std::is_trivially_copyable<T>()) {
            uint32_t count = (uint32_t)std::distance(begin, end);
            uint32_t newLen = len + count;
            ensureSize(newLen);

            T* ptr = data + len;
            memcpy(ptr, begin, count * sizeof(T));
            len = newLen;
        }
        else {
            appendIterator(begin, end);
        }
    }

    /// Add a range of elements to the end of the array, supporting
    /// simple forward iterators.
    template<typename It>
    void appendIterator(It begin, It end) {
        uint32_t count = (uint32_t)(end - begin);
        uint32_t newLen = len + count;
        ensureSize(newLen);

        T* ptr = data + len;
        while (begin != end)
            new (ptr++) T(*begin++);

        len = newLen;
    }

    /// Construct a new element at the end of the array.
    template<typename... Args>
    void emplace(Args&&... args) {
        amortizeCapacity();
        new (&data[len++]) T(std::forward<Args>(args)...);
    }

    /// Adds @a size elements to the array (default constructed).
    void extend(uint32_t size) {
        ensureSize(len + size);
        len += size;
    }

    /// Creates a copy of the array using the given allocator.
    span<T const> copy(BumpAllocator& alloc) const {
        if (len == 0)
            return nullptr;

        const T* source = data;
        T* dest = reinterpret_cast<T*>(alloc.allocate(len * sizeof(T)));
        for (uint32_t i = 0; i < len; i++)
            new (&dest[i]) T(*source++);
        return span<T const>(dest, len);
    }

    T& operator[](int index) { return data[index]; }
    const T& operator[](int index) const { return data[index]; }

    /// Indicates whether we are still "small", which means we are still on the stack.
    bool isSmall() const { return (void*)data == (void*)firstElement; }

protected:
    // Protected to disallow construction or deletion via base class.
    // This way we don't need a virtual destructor, or vtable at all.
    SmallVector() {}
    explicit SmallVector(uint32_t capacity) : capacity(capacity) {}
    ~SmallVector() { cleanup(); }

    template<typename TType, uint32_t N>
    friend class SmallVectorSized;

    T* data = reinterpret_cast<T*>(&firstElement[0]);
    uint32_t len = 0;
    uint32_t capacity;

    // Always allocate room for one element, the first stack allocated element.
    // This way the base class can be generic with respect to how many elements
    // can actually fit onto the stack.
    char firstElement[sizeof(T)];
    // Don't put any variables after firstElement; we expect that the derived
    // class will fill in stack space here.

    void resize() {
        T* newData = (T*)malloc(capacity * sizeof(T));
        if (std::is_trivially_copyable<T>())
            memcpy(newData, data, len * sizeof(T));
        else {
            // We assume we can trivially std::move elements here. Don't do anything dumb like
            // putting throwing move types into this container.
            for (uint32_t i = 0; i < len; i++)
                new (&newData[i]) T(std::move(data[i]));
        }

        cleanup();
        data = newData;
    }

    void amortizeCapacity() {
        if (len == capacity) {
            capacity = capacity * 2;
            if (capacity == 0)
                capacity = 4;
            resize();
        }
    }

    void ensureSize(uint32_t size) {
        if (size > capacity) {
            capacity = size;
            resize();
        }
    }

    void destructElements() {
        if (!std::is_trivially_destructible<T>()) {
            for (uint32_t i = 0; i < len; i++)
                data[i].~T();
        }
    }

    void cleanup() {
        destructElements();
        if (!isSmall())
            free(data);
    }
};

template<typename T, uint32_t N>
class SmallVectorSized : public SmallVector<T> {
    static_assert(N > 1, "Must have at least two elements in SmallVector stack size");
    static_assert(sizeof(T) * N <= 1024, "Initial size of SmallVector is over 1KB");

public:
    SmallVectorSized() : SmallVector<T>(N) {}

    SmallVectorSized(SmallVectorSized<T, N>&& other) noexcept :
        SmallVectorSized(static_cast<SmallVector<T>&&>(other)) {}

    SmallVectorSized(SmallVector<T>&& other) noexcept {
        if (other.isSmall()) {
            this->len = 0;
            this->capacity = sizeof(T) * N;
            this->data = reinterpret_cast<T*>(&this->firstElement[0]);
            this->appendRange(other.begin(), other.end());
        }
        else {
            this->data = other.data;
            this->len = other.len;
            this->capacity = other.capacity;

            other.data = nullptr;
            other.len = 0;
            other.capacity = 0;
        }
    }

    // not copyable
    SmallVectorSized(const SmallVectorSized&) = delete;
    SmallVectorSized& operator=(const SmallVectorSized&) = delete;

    SmallVectorSized& operator=(SmallVector<T>&& other) noexcept {
        if (this != &other) {
            this->cleanup();
            new (this) SmallVectorSized(std::move(other));
        }
        return *this;
    }

private:
    char stackBase[(N - 1) * sizeof(T)];
};

/// Vector is a specific alias of SmallVectorSized for cases where
/// we don't really care about the stack allocation aspects of SmallVector.
template<typename T>
using Vector = SmallVectorSized<T, 4>;

}
