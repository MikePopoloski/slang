//------------------------------------------------------------------------------
//! @file Iterator.h
//! @brief Helper classes for working with iterators
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

namespace slang {

// Note: Design mostly taken from llvm's iterator.h.

/// Base class that hides most of the iterator boilerplate from you.
/// Derive from this template and then implement methods as follows:
///
/// Forward Iterators:
///   (All of the following methods)
///   - DerivedT &operator=(const DerivedT& R);
///   - bool operator==(const DerivedT& R) const;
///   - const T& operator*() const;
///   - T& operator*();
///   - DerivedT& operator++();
///
/// Bidirectional Iterators:
///   (All methods of forward iterators, plus the following)
///   - DerivedT& operator--();
///
/// Random-access Iterators:
///   (All methods of bidirectional iterators excluding the following)
///   - DerivedT& operator++();
///   - DerivedT& operator--();
///   (and plus the following)
///   - bool operator<(const DerivedT& RHS) const;
///   - difference_type operator-(const DerivedT& R) const;
///   - DerivedT& operator+=(difference_type N);
///   - DerivedT& operator-=(difference_type N);
///
template<typename DerivedT, typename IteratorCategoryT, typename T,
         typename DifferenceTypeT = std::ptrdiff_t, typename PointerT = T*,
         typename ReferenceT = T&>
class iterator_facade {
protected:
    enum {
        IsRandomAccess = std::is_base_of<std::random_access_iterator_tag, IteratorCategoryT>::value,
        IsBidirectional =
            std::is_base_of<std::bidirectional_iterator_tag, IteratorCategoryT>::value,
    };

    /// A proxy object for computing a reference via indirecting a copy of an
    /// iterator. This is used in APIs which need to produce a reference via
    /// indirection but for which the iterator object might be a temporary.
    /// The proxy preserves the iterator internally and exposes the indirected
    /// reference via a conversion operator.
    class ReferenceProxy {
        friend iterator_facade;

        DerivedT I;

        ReferenceProxy(DerivedT I) : I(std::move(I)) {}

    public:
        operator ReferenceT() const { return *I; }
    };

public:
    using iterator_category = IteratorCategoryT;
    using value_type = T;
    using difference_type = DifferenceTypeT;
    using pointer = PointerT;
    using reference = ReferenceT;

    DerivedT operator+(difference_type n) const {
        static_assert(std::is_base_of<iterator_facade, DerivedT>::value,
                      "Must pass the derived type to this template!");
        static_assert(IsRandomAccess,
                      "The '+' operator is only defined for random access iterators.");
        DerivedT tmp = *static_cast<const DerivedT*>(this);
        tmp += n;
        return tmp;
    }

    friend DerivedT operator+(difference_type n, const DerivedT& i) {
        static_assert(IsRandomAccess,
                      "The '+' operator is only defined for random access iterators.");
        return i + n;
    }

    DerivedT operator-(difference_type n) const {
        static_assert(IsRandomAccess,
                      "The '-' operator is only defined for random access iterators.");
        DerivedT tmp = *static_cast<const DerivedT*>(this);
        tmp -= n;
        return tmp;
    }

    DerivedT& operator++() {
        static_assert(std::is_base_of<iterator_facade, DerivedT>::value,
                      "Must pass the derived type to this template!");
        return static_cast<DerivedT*>(this)->operator+=(1);
    }

    DerivedT operator++(int) {
        DerivedT tmp = *static_cast<DerivedT*>(this);
        ++*static_cast<DerivedT*>(this);
        return tmp;
    }

    DerivedT& operator--() {
        static_assert(IsBidirectional,
                      "The decrement operator is only defined for bidirectional iterators.");
        return static_cast<DerivedT*>(this)->operator-=(1);
    }

    DerivedT operator--(int) {
        static_assert(IsBidirectional,
                      "The decrement operator is only defined for bidirectional iterators.");
        DerivedT tmp = *static_cast<DerivedT*>(this);
        --*static_cast<DerivedT*>(this);
        return tmp;
    }

    bool operator!=(const DerivedT& RHS) const {
        return !static_cast<const DerivedT*>(this)->operator==(RHS);
    }

    bool operator>(const DerivedT& RHS) const {
        static_assert(IsRandomAccess,
                      "Relational operators are only defined for random access iterators.");
        return !static_cast<const DerivedT*>(this)->operator<(RHS) &&
               !static_cast<const DerivedT*>(this)->operator==(RHS);
    }

    bool operator<=(const DerivedT& RHS) const {
        static_assert(IsRandomAccess,
                      "Relational operators are only defined for random access iterators.");
        return !static_cast<const DerivedT*>(this)->operator>(RHS);
    }

    bool operator>=(const DerivedT& RHS) const {
        static_assert(IsRandomAccess,
                      "Relational operators are only defined for random access iterators.");
        return !static_cast<const DerivedT*>(this)->operator<(RHS);
    }

    pointer operator->() { return &static_cast<DerivedT*>(this)->operator*(); }
    pointer operator->() const { return &static_cast<const DerivedT*>(this)->operator*(); }

    ReferenceProxy operator[](difference_type n) {
        static_assert(IsRandomAccess, "Subscripting is only defined for random access iterators.");
        return ReferenceProxy(static_cast<DerivedT*>(this)->operator+(n));
    }

    ReferenceProxy operator[](difference_type n) const {
        static_assert(IsRandomAccess, "Subscripting is only defined for random access iterators.");
        return ReferenceProxy(static_cast<const DerivedT*>(this)->operator+(n));
    }
};

} // namespace slang
