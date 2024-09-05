//------------------------------------------------------------------------------
//! @file Bag.h
//! @brief General container of arbitrary objects, keyed by type
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <any>
#include <typeindex>
#include <typeinfo>

#include "slang/util/Hash.h"
#include "slang/util/TypeTraits.h"

namespace slang {

/// Bag - A general container of arbitrary objects.
///
/// The Bag container is a collection of various type-erased objects that can
/// be looked up by their original type. This is useful for things like passing
/// around a collection of various options to different subsystems without needing
/// to have cross dependencies between them.
class SLANG_EXPORT Bag {
public:
    Bag() = default;

    template<typename... T>
    Bag(T&&... items) {
        (set(std::forward<decltype(items)>(items)), ...);
    }

    /// Returns true if there are no items in the bag.
    [[nodiscard]] bool empty() const { return items.empty(); }

    /// Adds or overwrites an existing element of type T in the bag
    /// (making a copy in the process).
    template<typename T>
    void set(const T& item) {
        items[SLANG_TYPEOF(T)] = item;
    }

    /// Adds or overwrites an existing element of type T in the bag
    /// (moving in the new item in the process).
    template<typename T>
    void set(T&& item) {
        items[SLANG_TYPEOF(T)] = std::forward<T>(item);
    }

    /// Gets an element of type T from the bag, if it exists.
    /// Otherwise returns nullptr.
    template<typename T>
    const T* get() const {
        auto it = items.find(SLANG_TYPEOF(T));
        if (it == items.end())
            return nullptr;
        return std::any_cast<T>(&it->second);
    }

    /// Gets an element of type T from the bag, if it exists.
    /// Otherwise adds a default constructed element to the bag
    /// and returns a reference to it.
    template<typename T>
    T& insertOrGet() {
        auto& item = items[SLANG_TYPEOF(T)];
        if (!item.has_value())
            item.template emplace<T>();
        return *std::any_cast<T>(&item);
    }

    /// Gets an element of type T from the bag, if it exists.
    /// Otherwise returns a default constructed T.
    template<typename T>
    T getOrDefault() const {
        const T* result = get<T>();
        if (result)
            return *result;
        return T();
    }

private:
    flat_hash_map<SLANG_TYPEINDEX, std::any> items;
};

} // namespace slang
