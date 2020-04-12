//------------------------------------------------------------------------------
//! @file InstanceCache.h
//! @brief Caching of instantiated modules, interfaces, and programs
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>

#include "slang/util/Util.h"

namespace slang {

class ConstantValue;
class Definition;
class InstanceBodySymbol;
class Type;

class InstanceCacheKey {
public:
    InstanceCacheKey(const Definition& def, span<const ConstantValue* const> paramValues,
                     span<const Type* const> typeParams);

    void setInterfacePortKeys(span<const InstanceCacheKey* const> keys);

    const Definition& getDefinition() const { return *definition; }
    size_t hash() const { return savedHash; }

    bool operator==(const InstanceCacheKey& other) const;
    bool operator!=(const InstanceCacheKey& other) const { return !(*this == other); }

private:
    void computeHash();

    const Definition* definition;
    span<const ConstantValue* const> paramValues;
    span<const Type* const> typeParams;
    span<const InstanceCacheKey* const> interfacePorts;
    size_t savedHash;
};

class InstanceCache {
public:
    const InstanceBodySymbol* find(const InstanceCacheKey& key) const;
    void insert(const InstanceBodySymbol& instance);

    size_t getHitCount() const { return hits; }
    size_t getMissCount() const { return misses; }

private:
    struct Hasher {
        size_t operator()(const InstanceCacheKey& key) const { return key.hash(); }
    };

    flat_hash_map<InstanceCacheKey, const InstanceBodySymbol*, Hasher> cache;
    mutable size_t hits = 0;
    mutable size_t misses = 0;
};

} // namespace slang