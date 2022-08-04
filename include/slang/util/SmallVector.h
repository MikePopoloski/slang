//------------------------------------------------------------------------------
//! @file SmallVector.h
//! @brief Implements fast resizable array template
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <cstdlib>
#include <cstring>
#include <iterator>

#include "slang/util/BumpAllocator.h"

namespace slang {

/// SmallVector<T> - A fast growable array.
///
/// SmallVector is a vector-like growable array that allocates its first N elements
/// on the stack. As long as you don't need more room than that, there are no
/// heap allocations -- otherwise we spill over into the heap. This is the base class
/// for the actual sized implementation; it's split apart so that this one can be
/// used in more general interfaces that don't care about the explicit stack size.
template<typename T>
class SmallVector {
public:
    using value_type = T;
    using index_type = int;
    using pointer = T*;
    using reference = T&;
    using size_type = size_t;

    /// @return a pointer / iterator to the beginning of the array.
    [[nodiscard]] T* begin() { return data_; }

    /// @return a pointer / iterator to the end of the array.
    [[nodiscard]] T* end() { return data_ + len; }

    /// @return a pointer / iterator to the beginning of the array.
    [[nodiscard]] const T* begin() const { return data_; }

    /// @return a pointer / iterator to the end of the array.
    [[nodiscard]] const T* end() const { return data_ + len; }

    /// @return a pointer / iterator to the beginning of the array.
    [[nodiscard]] const T* cbegin() const { return data_; }

    /// @return a pointer / iterator to the end of the array.
    [[nodiscard]] const T* cend() const { return data_ + len; }

    /// @return a reference to the first element in the array. The array must not be empty!
    [[nodiscard]] const T& front() const {
        ASSERT(len);
        return data_[0];
    }

    /// @return a reference to the last element in the array. The array must not be empty!
    [[nodiscard]] const T& back() const {
        ASSERT(len);
        return data_[len - 1];
    }

    /// @return a reference to the first element in the array. The array must not be empty!
    [[nodiscard]] T& front() {
        ASSERT(len);
        return data_[0];
    }

    /// @return a reference to the last element in the array. The array must not be empty!
    [[nodiscard]] T& back() {
        ASSERT(len);
        return data_[len - 1];
    }

    /// @return a pointer to the underlying array.
    [[nodiscard]] T* data() const noexcept { return data_; }

    /// @return the number of elements in the array.
    [[nodiscard]] size_t size() const noexcept { return len; }

    /// @return true if the array is empty, and false if it has elements in it.
    [[nodiscard]] bool empty() const noexcept { return len == 0; }

    /// Clear all elements but retain underlying storage.
    void clear() {
        destructElements();
        len = 0;
    }

    /// Remove the last element from the array. Asserts if empty.
    void pop() {
        ASSERT(len);
        len--;
        data_[len].~T();
    }

    /// Add an element to the end of the array.
    void append(const T& item) {
        amortizeCapacity();
        new (&data_[len++]) T(item);
    }

    /// Add a range of elements to the end of the array.
    template<typename Container>
    void appendRange(const Container& container) {
        appendIterator(std::begin(container), std::end(container));
    }

    /// Add a range of elements to the end of the array.
    void appendRange(const T* begin, const T* end) {
        if constexpr (std::is_trivially_copyable<T>()) {
            size_t count = (size_t)std::distance(begin, end);
            size_t newLen = len + count;
            ensureCapacity(newLen);

            T* ptr = data_ + len;
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
        size_t count = (size_t)(end - begin);
        size_t newLen = len + count;
        ensureCapacity(newLen);

        T* ptr = data_ + len;
        while (begin != end)
            new (ptr++) T(*begin++);

        len = newLen;
    }

    /// Construct a new element at the end of the array.
    template<typename... Args>
    void emplace(Args&&... args) {
        amortizeCapacity();
        new (&data_[len++]) T(std::forward<Args>(args)...);
    }

    /// Adds @a size elements to the array (default constructed).
    void extend(size_t size) {
        ensureCapacity(len + size);
        len += size;
    }

    /// Ensure that there is enough allocated memory in the array for at least @a size objects.
    void reserve(size_t size) { ensureCapacity(size); }

    /// Resize the array. If larger than the current size, default construct new elements to
    /// fill the gap. If smaller than the current size, the length is shrunk as if by repeatedly
    /// calling pop().
    void resize(size_t size) {
        if (size > len) {
            ensureCapacity(size);
        }
        else {
            if constexpr (!std::is_trivially_destructible<T>()) {
                for (size_t i = size; i < len; i++)
                    data_[i].~T();
            }
        }
        len = size;
    }

    /// Creates a copy of the array using the given allocator.
    span<T> copy(BumpAllocator& alloc) const {
        if (len == 0)
            return {};

        const T* source = data_;
        T* dest = reinterpret_cast<T*>(alloc.allocate(len * sizeof(T), alignof(T)));
        for (size_t i = 0; i < len; i++)
            new (&dest[i]) T(*source++);
        return span<T>(dest, len);
    }

    using ConstElem = std::add_const_t<std::conditional_t<
        std::is_pointer_v<T>, std::add_pointer_t<std::add_const_t<std::remove_pointer_t<T>>>, T>>;

    /// Creates a constant copy of the array using the given allocator.
    /// If the array holds pointers, const is added to the pointed-to type as well.
    span<ConstElem> ccopy(BumpAllocator& alloc) const {
        auto copied = copy(alloc);
        return span<ConstElem>(copied.data(), copied.size());
    }

    T& operator[](size_t index) { return data_[index]; }
    const T& operator[](size_t index) const { return data_[index]; }

#if defined(__GNUC__) && !defined(__clang__)
#    pragma GCC diagnostic push
#    pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif
    /// Indicates whether we are still "small", which means we are still on the stack.
    bool isSmall() const {
        return (void*)data_ == (void*)firstElement;
    }
#if defined(__GNUC__) && !defined(__clang__)
#    pragma GCC diagnostic pop
#endif

protected:
    // Protected to disallow construction or deletion via base class.
    // This way we don't need a virtual destructor, or vtable at all.
    SmallVector() {
    }
    explicit SmallVector(size_t capacity) : capacity(capacity) {
    }
    ~SmallVector() {
        cleanup();
    }

    template<typename TType, size_t N>
    friend class SmallVectorSized;

    T* data_ = reinterpret_cast<T*>(&firstElement[0]);
    size_t len = 0;
    size_t capacity = 0;

    // Always allocate room for one element, the first stack allocated element.
    // This way the base class can be generic with respect to how many elements
    // can actually fit onto the stack.
    alignas(T) char firstElement[sizeof(T)];
    // Don't put any variables after firstElement; we expect that the derived
    // class will fill in stack space here.

    void realloc() {
        T* newData = (T*)malloc(capacity * sizeof(T));
        if constexpr (std::is_trivially_copyable<T>())
            memcpy(newData, data_, len * sizeof(T));
        else {
            // We assume we can trivially std::move elements here. Don't do anything dumb like
            // putting throwing move types into this container.
            for (size_t i = 0; i < len; i++)
                new (&newData[i]) T(std::move(data_[i]));
        }

        cleanup();
        data_ = newData;
    }

    void amortizeCapacity() {
        if (len == capacity) {
            capacity = capacity * 2;
            if (capacity == 0)
                capacity = 4;
            realloc();
        }
    }

    void ensureCapacity(size_t size) {
        if (size > capacity) {
            capacity = size;
            realloc();
        }
    }

    void destructElements() {
        if constexpr (!std::is_trivially_destructible<T>()) {
            for (size_t i = 0; i < len; i++)
                data_[i].~T();
        }
    }

    void cleanup() {
        destructElements();
        if (!isSmall())
            free(data_);
    }
};

/// A concrete, sized version of the SmallVector<T> template.
/// The template parameter N is the number of elements that will be allocated on the stack.
template<typename T, size_t N>
class SmallVectorSized : public SmallVector<T> {
    static_assert(N > 1, "Must have at least two elements in SmallVector stack size");
    static_assert(sizeof(T) * N <= 1024, "Initial size of SmallVector is over 1KB");

public:
    SmallVectorSized() : SmallVector<T>(N) {}

    /// Constructs the SmallVectorSized with the given capacity. If that capacity is less than
    /// the preallocated stack size `N` it will be ignored. Otherwise it will perform a heap
    /// allocation right away.
    explicit SmallVectorSized(size_t capacity) : SmallVector<T>(N) { this->reserve(capacity); }

    SmallVectorSized(SmallVectorSized<T, N>&& other) noexcept :
        SmallVectorSized(static_cast<SmallVector<T>&&>(other)) {}

    SmallVectorSized(SmallVector<T>&& other) noexcept {
        if (other.isSmall()) {
            this->len = 0;
            this->capacity = N;
            this->data_ = reinterpret_cast<T*>(&this->firstElement[0]);
            this->appendRange(other.begin(), other.end());
        }
        else {
            this->data_ = other.data_;
            this->len = other.len;
            this->capacity = other.capacity;

            other.data_ = nullptr;
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
    alignas(T) char stackBase[(N - 1) * sizeof(T)];
};

} // namespace slang
