//------------------------------------------------------------------------------
// Bag.h
// General container of arbitrary objects, keyed by type.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <any>
#include <typeindex>
#include <typeinfo>

#include "flat_hash_map.hpp"

namespace slang {

/// Bag - A general container of arbitrary objects.
///
/// The Bag container is a collection of various type-erased objects that can
/// be looked up by their original type. This is useful for things like passing
/// around a collection of various options to different subsystems without needing
/// to have cross dependencies between them.
class Bag {
public:
    template<typename T>
    void add(const T& item) {
        items[std::type_index(typeid(T))] = item;
    }

    template<typename T>
    void add(T&& item) {
        items[std::type_index(typeid(T))] = std::move(item);
    }

    template<typename T>
    const T* get() const {
        auto it = items.find(std::type_index(typeid(T)));
        if (it == items.end())
            return nullptr;
        return std::any_cast<T>(&it->second);
    }

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

}