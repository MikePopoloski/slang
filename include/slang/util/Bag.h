//------------------------------------------------------------------------------
//! @file Bag.h
//! @brief General container of arbitrary objects, keyed by type
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <any>
#include <typeindex>
#include <typeinfo>

#include "slang/util/Hash.h"

namespace slang {

/// Bag - A general container of arbitrary objects.
///
/// The Bag container is a collection of various type-erased objects that can
/// be looked up by their original type. This is useful for things like passing
/// around a collection of various options to different subsystems without needing
/// to have cross dependencies between them.
class Bag {
public:
    Bag() = default;

    template<typename... T>
    Bag(T&&... items) {
        (set(std::forward<decltype(items)>(items)), ...);
    }

    /// Adds or overwrites an existing element of type T in the bag
    /// (making a copy in the process).
    template<typename T>
    void set(const T& item) {
        items[std::type_index(typeid(T))] = item;
    }

    /// Adds or overwrites an existing element of type T in the bag
    /// (moving in the new item in the process).
    template<typename T>
    void set(T&& item) {
        items[std::type_index(typeid(T))] = std::forward<T>(item);
    }

    /// Gets an element of type T from the bag, if it exists.
    /// Otherwise returns nullptr.
    template<typename T>
    const T* get() const {
        auto it = items.find(std::type_index(typeid(T)));
        if (it == items.end())
            return nullptr;
        return std::any_cast<T>(&it->second);
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
    flat_hash_map<std::type_index, std::any> items;
};

} // namespace slang
