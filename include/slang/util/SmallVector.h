//------------------------------------------------------------------------------
//! @file SmallVector.h
//! @brief Implements fast resizable array template
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <algorithm>
#include <iterator>
#include <limits>
#include <memory>
#include <span>
#include <utility>

#include "slang/util/BumpAllocator.h"

namespace slang {

namespace detail {

[[noreturn]] SLANG_EXPORT void throwOutOfRange();
[[noreturn]] SLANG_EXPORT void throwLengthError();

} // namespace detail

/// @brief Base class for a fast growable array
///
/// SmallVector is a vector-like growable array that allocates its first N elements
/// on the stack. As long as you don't need more room than that, there are no
/// heap allocations -- otherwise we spill over into the heap. This is the base class
/// that erases the stack size template parameter for use with generic code.
template<typename T>
class SmallVectorBase {
public:
    using value_type = T;
    using size_type = size_t;
    using difference_type = ptrdiff_t;
    using const_iterator = const T*;
    using iterator = T*;

    using const_reverse_iterator = std::reverse_iterator<const_iterator>;
    using reverse_iterator = std::reverse_iterator<iterator>;

    using pointer = T*;
    using reference = T&;
    using const_pointer = const T*;
    using const_reference = const T&;

    /// @return an iterator to the beginning of the array.
    [[nodiscard]] constexpr iterator begin() noexcept { return data_; }

    /// @return an iterator to the end of the array.
    [[nodiscard]] constexpr iterator end() noexcept { return data_ + len; }

    /// @return an iterator to the beginning of the array.
    [[nodiscard]] constexpr const_iterator begin() const noexcept { return data_; }

    /// @return an iterator to the end of the array.
    [[nodiscard]] constexpr const_iterator end() const noexcept { return data_ + len; }

    /// @return a reverse iterator to the end of the array.
    [[nodiscard]] constexpr reverse_iterator rbegin() noexcept { return reverse_iterator(end()); }

    /// @return a reverse iterator to the end of the array.
    [[nodiscard]] constexpr const_reverse_iterator rbegin() const noexcept {
        return const_reverse_iterator(end());
    }

    /// @return a reverse iterator to the end of the array.
    [[nodiscard]] constexpr reverse_iterator rend() noexcept { return reverse_iterator(begin()); }

    /// @return a reverse iterator to the end of the array.
    [[nodiscard]] constexpr const_reverse_iterator rend() const noexcept {
        return const_reverse_iterator(begin());
    }

    /// @return a reference to the first element in the array. The array must not be empty!
    [[nodiscard]] constexpr const_reference front() const {
        SLANG_ASSERT(len);
        return data_[0];
    }

    /// @return a reference to the last element in the array. The array must not be empty!
    [[nodiscard]] constexpr const_reference back() const {
        SLANG_ASSERT(len);
        return data_[len - 1];
    }

    /// @return a reference to the first element in the array. The array must not be empty!
    [[nodiscard]] constexpr reference front() {
        SLANG_ASSERT(len);
        return data_[0];
    }

    /// @return a reference to the last element in the array. The array must not be empty!
    [[nodiscard]] constexpr reference back() {
        SLANG_ASSERT(len);
        return data_[len - 1];
    }

    /// @return a pointer to the underlying array.
    [[nodiscard]] constexpr pointer data() noexcept { return data_; }

    /// @return a pointer to the underlying array.
    [[nodiscard]] constexpr const_pointer data() const noexcept { return data_; }

    /// @return the number of elements in the array.
    [[nodiscard]] constexpr size_type size() const noexcept { return len; }

    /// @return the number of elements that can be held in currently allocated storage.
    [[nodiscard]] constexpr size_type capacity() const noexcept { return cap; }

    /// @return the maximum number of elements that could ever fit in the array,
    /// assuming the system had enough memory to support it.
    [[nodiscard]] constexpr size_type max_size() const noexcept {
        return std::numeric_limits<difference_type>::max() / sizeof(T);
    }

    /// @return true if the array is empty, and false if it has elements in it.
    [[nodiscard]] constexpr bool empty() const noexcept { return len == 0; }

    /// Ensures that there is enough allocated memory in the array for at least @a size objects.
    void reserve(size_type newCapacity) {
        if (newCapacity > cap) {
            if (newCapacity > max_size())
                detail::throwLengthError();

            reallocateTo(newCapacity);
        }
    }

    /// Resizes the array. If larger than the current size, value constructs new elements to
    /// fill the gap. If smaller than the current size, the length is shrunk and elements
    /// are destructed.
    void resize(size_type newSize) { resizeImpl(newSize, ValueInitTag()); }

    /// Resizes the array. If larger than the current size, adds new elements as copies of
    /// @a value to fill the gap. If smaller than the current size, the length is shrunk and
    /// elements are destructed.
    void resize(size_t newSize, const T& value) { resizeImpl(newSize, value); }

    /// Resizes the array. If larger than the current size, default constructs new elements to
    /// fill the gap. If smaller than the current size, the length is shrunk and elements
    /// are destructed.
    void resize_for_overwrite(size_type newSize)
        requires(std::is_standard_layout_v<T>)
    {
        resizeImpl(newSize, DefaultInitTag());
    }

    /// Clears all elements but retain underlying storage.
    void clear() noexcept {
        std::ranges::destroy(*this);
        len = 0;
    }

    /// Removes the last element from the array. The array must not be empty!
    void pop_back() {
        SLANG_ASSERT(len);
        len--;
        std::ranges::destroy_at(data_ + len);
    }

    /// Adds an element to the end of the array.
    void push_back(const T& item) { emplace_back(item); }

    /// Adds an element to the end of the array.
    void push_back(T&& item) { emplace_back(std::move(item)); }

    /// Constructs a new element at the end of the array.
    template<typename... Args>
    reference emplace_back(Args&&... args) {
        if (len == cap)
            return *emplaceRealloc(end(), std::forward<Args>(args)...);

        new (end()) T(std::forward<Args>(args)...);
        len++;
        return back();
    }

    /// Appends a range of elements to the end of the array.
    template<std::input_iterator TIter>
    void append(TIter first, TIter last) {
        auto numElems = static_cast<size_type>(std::ranges::distance(first, last));
        auto newSize = len + numElems;
        reserve(newSize);

        std::ranges::uninitialized_copy(first, last, end(), end() + numElems);
        len = newSize;
    }

    /// Appends a range of elements to the end of the array.
    template<std::ranges::input_range TContainer>
    void append_range(const TContainer& container) {
        append(std::ranges::begin(container), std::ranges::end(container));
    }

    /// Appends @a count copies of @a value to the end of the array.
    void append(size_type count, const T& value) {
        // Make a temporary copy of the value in case it already lives inside our array.
        T temp(value);

        auto newSize = len + count;
        reserve(newSize);

        std::ranges::uninitialized_fill_n(end(), count, temp);
        len = newSize;
    }

    /// Resets the contents of the array to be @a count copies of @a value.
    void assign(size_type count, const T& value) {
        if (count > capacity()) {
            // Make a temporary copy of the value in case it already lives inside our array.
            T temp(value);

            // Clear our our contents and reserve space for the new values.
            clear();
            reserve(count);

            // Fill the range.
            std::ranges::uninitialized_fill_n(begin(), count, temp);
            len = count;
            return;
        }

        std::ranges::fill_n(begin(), std::min(count, size()), value);
        if (count > size())
            std::ranges::uninitialized_fill_n(end(), count - size(), value);
        else if (count < size())
            std::ranges::destroy(begin() + count, end());
        len = count;
    }

    /// Resets the contents of the array to be the contents of the given range.
    template<std::input_iterator TIter>
    void assign(TIter first, TIter last) {
        clear();
        append(first, last);
    }

    /// Resets the contents of the array to be the contents of the given range.
    template<std::ranges::input_range TContainer>
    void assign_range(const TContainer& container) {
        assign(std::ranges::begin(container), std::ranges::end(container));
    }

    /// Constructs a new element at the specified position in the array.
    template<typename... Args>
    iterator emplace(const_iterator pos, Args&&... args) {
        auto result = const_cast<iterator>(pos);
        if (len == cap)
            return emplaceRealloc(result, std::forward<Args>(args)...);

        if (pos == end()) {
            // Emplace at end can be constructed in place.
            new (end()) T(std::forward<Args>(args)...);
            len++;
            return result;
        }

        // Construct a temporary to avoid aliasing an existing element we're about to move.
        T temp(std::forward<Args>(args)...);

        // Manually move the last element backward by one because it's uninitialized space.
        new (end()) T(std::move(back()));

        // Now move everything else and insert our temporary.
        std::ranges::move_backward(result, end() - 1, end());
        *result = std::move(temp);

        len++;
        return result;
    }

    /// Inserts the given value at the specified position in the array.
    iterator insert(const_iterator pos, const T& val) { return emplace(pos, val); }

    /// Inserts the given value at the specified position in the array.
    iterator insert(const_iterator pos, T&& val) { return emplace(pos, std::move(val)); }

    /// Inserts a range of elements at the specified position in the array.
    template<std::ranges::input_range TContainer>
    iterator insert_range(const_iterator pos, const TContainer& container) {
        return insert(pos, std::ranges::begin(container), std::ranges::end(container));
    }

    /// Inserts a range of elements at the specified position in the array.
    template<std::input_iterator TIter>
    iterator insert(const_iterator pos, TIter first, TIter last) {
        auto offset = static_cast<size_type>(pos - begin());
        if (pos == end()) {
            append(first, last);
            return begin() + offset;
        }

        // Make space for new elements.
        auto numElems = static_cast<size_type>(std::ranges::distance(first, last));
        auto newSize = len + numElems;
        reserve(newSize);

        // Reset the iterator since reserve() may have invalidated it.
        auto result = begin() + offset;

        // If there are more existing elements between the insertion point and
        // the end of the range than there are being inserted we can use a
        // simpler approach for insertion.
        auto existingOverlap = static_cast<size_type>(end() - result);
        if (existingOverlap >= numElems) {
            auto oldEnd = end();
            append(std::move_iterator<iterator>(end() - numElems),
                   std::move_iterator<iterator>(end()));

            std::ranges::move_backward(result, oldEnd - numElems, oldEnd);
            std::ranges::copy(first, last, result);
            return result;
        }

        // Move over elements we're about to overwrite.
        std::uninitialized_move(result, end(), begin() + newSize - existingOverlap);

        // Copy in the new elements.
        first = std::ranges::copy_n(first,
                                    static_cast<std::iter_difference_t<TIter>>(existingOverlap),
                                    result)
                    .in;

        // Insert the non-overwritten middle part.
        std::ranges::uninitialized_copy(first, last, end(), end() + numElems - existingOverlap);
        len = newSize;
        return result;
    }

    /// Inserts @a count copies of @a value at the specified position in the array.
    iterator insert(const_iterator pos, size_type count, const T& value) {
        auto offset = static_cast<size_type>(pos - begin());
        if (pos == end()) {
            append(count, value);
            return begin() + offset;
        }

        // Make a temporary copy of the value in case it already lives inside our array.
        T temp(value);

        // Make space for new elements.
        auto newSize = len + count;
        reserve(newSize);

        // Reset the iterator since reserve() may have invalidated it.
        auto result = begin() + offset;

        // If there are more existing elements between the insertion point and
        // the end of the range than there are being inserted we can use a
        // simpler approach for insertion.
        auto existingOverlap = static_cast<size_type>(end() - result);
        if (existingOverlap >= count) {
            auto oldEnd = end();
            append(std::move_iterator<iterator>(end() - count),
                   std::move_iterator<iterator>(end()));

            std::ranges::move_backward(result, oldEnd - count, oldEnd);
            std::ranges::fill_n(result, count, temp);
            return result;
        }

        // Move over elements we're about to overwrite.
        std::uninitialized_move(result, end(), begin() + newSize - existingOverlap);

        // Copy in the new elements.
        std::ranges::fill_n(result, existingOverlap, temp);

        // Insert the non-overwritten middle part.
        std::ranges::uninitialized_fill_n(end(), count - existingOverlap, temp);
        len = newSize;
        return result;
    }

    /// Removes the elements at @a pos from the array.
    iterator erase(const_iterator pos) {
        // const_cast is fine, this is a non-const member function.
        iterator result = const_cast<iterator>(pos);

        std::ranges::move(result + 1, end(), result);
        pop_back();
        return result;
    }

    /// Removes all elements between @a first and @a last from the array.
    iterator erase(const_iterator first, const_iterator last) {
        // const_cast is fine, this is a non-const member function.
        iterator result = const_cast<iterator>(first);

        if (first != last) {
            auto newLast = std::ranges::move(const_cast<iterator>(last), end(),
                                             const_cast<iterator>(first))
                               .out;
            std::ranges::destroy(newLast, end());
            len = static_cast<size_type>(newLast - begin());
        }

        return result;
    }

    /// Swaps the contents of @a rhs with this array.
    void swap(SmallVectorBase& rhs);

    /// Creates a copy of the array using the given allocator.
    [[nodiscard]] std::span<T> copy(BumpAllocator& alloc) const {
        if (len == 0)
            return {};

        pointer dest = reinterpret_cast<pointer>(alloc.allocate(len * sizeof(T), alignof(T)));
        std::ranges::uninitialized_copy(begin(), end(), dest, dest + len);

        return std::span<T>(dest, len);
    }

    using ConstElem = std::add_const_t<std::conditional_t<
        std::is_pointer_v<T>, std::add_pointer_t<std::add_const_t<std::remove_pointer_t<T>>>, T>>;

    /// Creates a constant copy of the array using the given allocator.
    /// If the array holds pointers, const is added to the pointed-to type as well.
    [[nodiscard]] std::span<ConstElem> ccopy(BumpAllocator& alloc) const {
        auto copied = copy(alloc);
        return std::span<ConstElem>(copied.data(), copied.size());
    }

    /// @return the element at the given position in the array.
    constexpr reference operator[](size_type index) {
        SLANG_ASSERT(index < len);
        return data_[index];
    }

    /// @return the element at the given position in the array.
    constexpr const_reference operator[](size_type index) const {
        SLANG_ASSERT(index < len);
        return data_[index];
    }

    /// @return the element at the given position in the array.
    constexpr reference at(size_type index) {
        if (index >= len)
            detail::throwOutOfRange();
        return data_[index];
    }

    /// @return the element at the given position in the array.
    constexpr const_reference at(size_type index) const {
        if (index >= len)
            detail::throwOutOfRange();
        return data_[index];
    }

    /// Indicates whether we are still "small", which means we are still on the stack.
    [[nodiscard]] constexpr bool isSmall() const noexcept {
        return (const void*)data_ == (const void*)firstElement;
    }

protected:
    // Protected to disallow construction or deletion via base class.
    // This way we don't need a virtual destructor, or vtable at all.
    SmallVectorBase() noexcept = default;
    explicit SmallVectorBase(size_type capacity) noexcept : cap(capacity) {}
    ~SmallVectorBase() { cleanup(); }

    SmallVectorBase& operator=(const SmallVectorBase& rhs);
    SmallVectorBase& operator=(SmallVectorBase&& rhs);

private:
    template<typename TType, size_t N>
    friend class SmallVector;

    pointer data_ = reinterpret_cast<pointer>(&firstElement[0]);
    size_type len = 0;
    size_type cap = 0;

#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4324) // structure was padded due to alignment specifier
#endif
    // Always allocate room for one element, the first stack allocated element.
    // This way the base class can be generic with respect to how many elements
    // can actually fit onto the stack.
    alignas(T) char firstElement[sizeof(T)];
    // Don't put any variables after firstElement; we expect that the derived
    // class will fill in stack space here.
#ifdef _MSC_VER
#    pragma warning(pop)
#endif

    struct DefaultInitTag {};
    struct ValueInitTag {};

    void cleanup() {
        std::ranges::destroy(*this);
        if (!isSmall())
            ::operator delete(data_);
    }

    template<typename... Args>
    pointer emplaceRealloc(const pointer pos, Args&&... args);

    template<typename TVal>
    void resizeRealloc(size_type newSize, const TVal& val);

    template<typename TVal>
    void resizeImpl(size_type newSize, const TVal& val) {
        if (newSize < len) {
            std::ranges::destroy(begin() + newSize, end());
            len = newSize;
            return;
        }

        if (newSize > len) {
            if (newSize > cap) {
                // Copy the value in case it's inside our existing array.
                TVal temp(val);
                resizeRealloc(newSize, temp);
                return;
            }

            if constexpr (std::is_same_v<T, TVal>) {
                std::ranges::uninitialized_fill_n(end(), ptrdiff_t(newSize - len), val);
            }
            else if constexpr (std::is_same_v<TVal, DefaultInitTag>) {
                std::ranges::uninitialized_default_construct_n(end(), ptrdiff_t(newSize - len));
            }
            else {
                std::ranges::uninitialized_value_construct_n(end(), ptrdiff_t(newSize - len));
            }
            len = newSize;
        }
    }

    void reallocateTo(size_type newCapacity) {
        auto newData = (pointer)::operator new(newCapacity * sizeof(T));
        std::uninitialized_move(begin(), end(), newData);

        cleanup();
        cap = newCapacity;
        data_ = newData;
    }

    constexpr size_type calculateGrowth(size_type newSize) const {
        const auto max = max_size();
        if (cap > max - cap)
            return max;

        const size_type doubled = cap * 2;
        if (doubled < newSize)
            return newSize;

        return doubled;
    }
};

namespace detail {

template<typename T>
constexpr size_t calculateDefaultSmallVectorElems() {
    // As a default, try to fit the vector into one cache line.
    // Assume 64 is a reasonable approximation of modern cache line sizes.
    size_t preferredSize = 64;
    size_t availableSize = preferredSize - sizeof(T*) - 2 * sizeof(size_t);
    size_t numElems = availableSize / sizeof(T);
    return numElems < 2 ? 2 : numElems;
}

} // namespace detail

/// A tag type used in a SmallVector constructor to indicate that the passed
/// capacity parameter is only for reserving uninitialized memory and not
/// actually adding elements to the container.
struct UninitializedTag {};

/// A concrete, sized version of the SmallVectorBase<T> template.
/// The template parameter N is the number of elements that will be allocated on the stack.
template<typename T, size_t N = detail::calculateDefaultSmallVectorElems<T>()>
class SmallVector : public SmallVectorBase<T> {
    static_assert(N > 1, "Must have at least two elements in SmallVector stack size");
    static_assert(sizeof(T) * N <= 1024, "Initial size of SmallVector is over 1KB");

public:
    using Base = SmallVectorBase<T>;
    using size_type = typename Base::size_type;
    using pointer = typename Base::pointer;

    /// Default constructs the SmallVector.
    SmallVector() noexcept : Base(N) {}

    /// Constructs the SmallVector with the given capacity. If that capacity is less than
    /// the preallocated stack size `N` it will be ignored. Otherwise it will perform a heap
    /// allocation right away. Unlike std::vector this does not add any elements to the container.
    explicit SmallVector(size_type capacity, UninitializedTag) : Base(N) {
        this->reserve(capacity);
    }

    /// Constructs the SmallVector from the given range of elements.
    template<std::input_iterator TIter>
    SmallVector(TIter first, TIter last) {
        this->append(first, last);
    }

    /// Constructs the SmallVector from the given range.
    template<std::ranges::input_range TRange>
    explicit SmallVector(TRange range) {
        this->append_range(range);
    }

    /// Copy constructs from another vector.
    SmallVector(const SmallVector& other) : SmallVector(static_cast<const Base&>(other)) {}

    /// Copy constructs from another vector.
    SmallVector(const Base& other) : Base(N) { this->append(other.begin(), other.end()); }

    /// Move constructs from another vector.
    SmallVector(SmallVector&& other) : SmallVector(static_cast<Base&&>(other)) {}

    /// Move constructs from another vector.
    SmallVector(Base&& other) {
        if (other.isSmall()) {
            this->cap = N;
            this->append(std::move_iterator(other.begin()), std::move_iterator(other.end()));
        }
        else {
            this->data_ = std::exchange(other.data_, nullptr);
            this->len = std::exchange(other.len, 0);
            this->cap = std::exchange(other.cap, 0);
        }
    }

    /// Copy assignment from another vector.
    SmallVector& operator=(const Base& rhs) {
        Base::operator=(rhs);
        return *this;
    }
    SmallVector& operator=(const SmallVector& rhs) {
        Base::operator=(rhs);
        return *this;
    }

    /// Move assignment from another vector.
    SmallVector& operator=(Base&& rhs) {
        Base::operator=(std::move(rhs));
        return *this;
    }
    SmallVector& operator=(SmallVector&& rhs) {
        Base::operator=(std::move(rhs));
        return *this;
    }

    /// Requests the removal of unused capacity.
    void shrink_to_fit() {
        if (this->isSmall())
            return;

        // If the number of elements doesn't fit in our stack capacity
        // just reallocate to a smaller heap array. Otherwise copy elements
        // into our stack capacity and make the vector small again.
        if (this->size() > N) {
            this->reallocateTo(this->size());
        }
        else {
            auto newData = reinterpret_cast<pointer>(&this->firstElement[0]);
            std::uninitialized_move(this->begin(), this->end(), newData);

            this->cleanup();
            this->cap = N;
            this->data_ = newData;
        }
    }

private:
    alignas(T) char stackBase[(N - 1) * sizeof(T)];
};

template<typename T>
inline bool operator==(const SmallVectorBase<T>& lhs, const SmallVectorBase<T>& rhs) {
    return std::ranges::equal(lhs, rhs);
}

template<typename T>
inline auto operator<=>(const SmallVectorBase<T>& lhs, const SmallVectorBase<T>& rhs) {
    return std::lexicographical_compare_three_way(lhs.begin(), lhs.end(), rhs.begin(), rhs.end());
}

template<typename T>
void SmallVectorBase<T>::swap(SmallVectorBase<T>& rhs) {
    if (this == &rhs)
        return;

    // We can only do a true swap if neither vector is small.
    if (!isSmall() && !rhs.isSmall()) {
        std::swap(data_, rhs.data_);
        std::swap(len, rhs.len);
        std::swap(cap, rhs.cap);
        return;
    }

    // Make sure each container has enough space for each other's elements.
    reserve(rhs.size());
    rhs.reserve(size());

    // Swap the shared elements.
    size_type numShared = std::min(size(), rhs.size());
    for (size_type i = 0; i < numShared; i++)
        std::swap((*this)[i], rhs[i]);

    // Copy over the extra elements from whichever side is larger.
    if (size() > rhs.size()) {
        std::ranges::uninitialized_copy(begin() + numShared, end(), rhs.end(),
                                        rhs.end() + size() - numShared);
        rhs.len = len;

        std::ranges::destroy(begin() + numShared, end());
        len = numShared;
    }
    else if (rhs.size() > size()) {
        std::ranges::uninitialized_copy(rhs.begin() + numShared, rhs.end(), end(),
                                        end() + rhs.size() - numShared);
        len = rhs.len;

        std::ranges::destroy(rhs.begin() + numShared, rhs.end());
        rhs.len = numShared;
    }
}

template<typename T>
SmallVectorBase<T>& SmallVectorBase<T>::operator=(const SmallVectorBase<T>& rhs) {
    if (this == &rhs)
        return *this;

    // If we already have sufficient space assign the common elements,
    // then destroy any excess.
    if (len >= rhs.size()) {
        iterator newEnd;
        if (rhs.size())
            newEnd = std::ranges::copy(rhs, begin()).out;
        else
            newEnd = begin();

        std::ranges::destroy(newEnd, end());
        len = rhs.size();
        return *this;
    }

    if (capacity() < rhs.size()) {
        // If we have to grow to have enough elements, destroy the current elements.
        // This allows us to avoid copying them during the grow.
        clear();
        reserve(rhs.size());
    }
    else if (len) {
        // Otherwise, use assignment for the already-constructed elements.
        std::ranges::copy(rhs.begin(), rhs.begin() + len, begin());
    }

    // Copy construct the new elements in place.
    std::ranges::uninitialized_copy(rhs.begin() + len, rhs.end(), begin() + len,
                                    begin() + rhs.size());
    len = rhs.size();
    return *this;
}

template<typename T>
SmallVectorBase<T>& SmallVectorBase<T>::operator=(SmallVectorBase<T>&& rhs) {
    if (this == &rhs)
        return *this;

    // If the rhs isn't small, clear this vector and then steal its buffer.
    if (!rhs.isSmall()) {
        cleanup();
        this->data_ = std::exchange(rhs.data_, nullptr);
        this->len = std::exchange(rhs.len, 0);
        this->cap = std::exchange(rhs.cap, 0);
        return *this;
    }

    // If we already have sufficient space assign the common elements,
    // then destroy any excess.
    if (len >= rhs.size()) {
        iterator newEnd;
        if (rhs.size())
            newEnd = std::ranges::move(rhs, begin()).out;
        else
            newEnd = begin();

        std::ranges::destroy(newEnd, end());
        len = rhs.size();
        rhs.clear();
        return *this;
    }

    if (capacity() < rhs.size()) {
        // If we have to grow to have enough elements, destroy the current elements.
        // This allows us to avoid copying them during the grow.
        clear();
        reserve(rhs.size());
    }
    else if (len) {
        // Otherwise, use assignment for the already-constructed elements.
        std::ranges::move(rhs.begin(), rhs.begin() + len, begin());
    }

    // Move construct the new elements in place.
    std::uninitialized_move(rhs.begin() + len, rhs.end(), begin() + len);
    len = rhs.size();
    rhs.clear();
    return *this;
}

template<typename T>
template<typename... Args>
typename SmallVectorBase<T>::pointer SmallVectorBase<T>::emplaceRealloc(const pointer pos,
                                                                        Args&&... args) {
    if (len == max_size())
        detail::throwLengthError();

    auto newCap = calculateGrowth(len + 1);
    auto offset = static_cast<size_type>(pos - begin());
    auto newData = (pointer)::operator new(newCap * sizeof(T));

    // First construct the new element in the new memory,
    // so that we don't corrupt the new element if it relied on
    // existing elements we're about to move around.
    auto newPos = newData + offset;
    new (newPos) T(std::forward<Args>(args)...);

    // Now move elements to the new memory.
    if (pos == end()) {
        std::uninitialized_move(begin(), end(), newData);
    }
    else {
        std::uninitialized_move(begin(), pos, newData);
        std::uninitialized_move(pos, end(), newPos + 1);
    }

    cleanup();
    len++;
    cap = newCap;
    data_ = newData;
    return newPos;
}

template<typename T>
template<typename TVal>
void SmallVectorBase<T>::resizeRealloc(size_type newSize, const TVal& val) {
    SLANG_ASSERT(newSize > len);
    if (newSize > max_size())
        detail::throwLengthError();

    auto newCap = calculateGrowth(newSize);
    auto newData = (pointer)::operator new(newCap * sizeof(T));

    std::uninitialized_move(begin(), end(), newData);

    if constexpr (std::is_same_v<T, TVal>) {
        std::ranges::uninitialized_fill_n(newData + len, ptrdiff_t(newSize - len), val);
    }
    else if constexpr (std::is_same_v<TVal, DefaultInitTag>) {
        std::ranges::uninitialized_default_construct_n(newData + len, ptrdiff_t(newSize - len));
    }
    else {
        std::ranges::uninitialized_value_construct_n(newData + len, ptrdiff_t(newSize - len));
    }

    cleanup();
    len = newSize;
    cap = newCap;
    data_ = newData;
}

} // namespace slang

namespace std {

template<typename T>
inline void swap(slang::SmallVectorBase<T>& lhs, slang::SmallVectorBase<T>& rhs) {
    lhs.swap(rhs);
}

template<typename T, unsigned N>
inline void swap(slang::SmallVector<T, N>& lhs, slang::SmallVector<T, N>& rhs) {
    lhs.swap(rhs);
}

} // end namespace std
