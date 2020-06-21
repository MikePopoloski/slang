//------------------------------------------------------------------------------
// InstanceCache.cpp
// Caching of instantiated modules, interfaces, and programs
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/compilation/InstanceCache.h"

#include "slang/compilation/Definition.h"
#include "slang/numeric/ConstantValue.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/symbols/Type.h"
#include "slang/util/Hash.h"

namespace slang {

InstanceCacheKey::InstanceCacheKey(const Definition& def,
                                   span<const ConstantValue* const> paramValues,
                                   span<const Type* const> typeParams) :
    definition(&def),
    paramValues(paramValues), typeParams(typeParams) {
    computeHash();
}

void InstanceCacheKey::setInterfacePortKeys(span<const InstanceCacheKey* const> keys) {
    // If we previously has interface ports set, we need to back out their
    // contribution to the hash.
    if (!interfacePorts.empty())
        computeHash();

    interfacePorts = keys;
    for (auto key : keys)
        hash_combine(savedHash, key->hash());
}

void InstanceCacheKey::computeHash() {
    size_t h = 0;
    hash_combine(h, definition);
    for (auto val : paramValues)
        hash_combine(h, val ? val->hash() : 0);
    for (auto type : typeParams)
        hash_combine(h, type ? type->hash() : 0);
    savedHash = h;
}

bool InstanceCacheKey::operator==(const InstanceCacheKey& other) const {
    if (savedHash != other.savedHash || definition != other.definition ||
        paramValues.size() != other.paramValues.size() ||
        typeParams.size() != other.typeParams.size() ||
        interfacePorts.size() != other.interfacePorts.size()) {
        return false;
    }

    for (auto lit = paramValues.begin(), rit = other.paramValues.begin(); lit != paramValues.end();
         lit++, rit++) {
        const ConstantValue* l = *lit;
        const ConstantValue* r = *rit;
        if (l && r) {
            if (!l->equivalentTo(*r))
                return false;
        }
        else {
            if (l != r)
                return false;
        }
    }

    for (auto lit = typeParams.begin(), rit = other.typeParams.begin(); lit != typeParams.end();
         lit++, rit++) {
        const Type* l = *lit;
        const Type* r = *rit;
        if (l && r) {
            if (!l->isMatching(*r))
                return false;
        }
        else {
            if (l != r)
                return false;
        }
    }

    for (auto lit = interfacePorts.begin(), rit = other.interfacePorts.begin();
         lit != interfacePorts.end(); lit++, rit++) {
        const InstanceCacheKey* l = *lit;
        const InstanceCacheKey* r = *rit;
        if (*l != *r)
            return false;
    }

    return true;
}

const InstanceBodySymbol* InstanceCache::find(const InstanceCacheKey& key) const {
    auto it = cache.find(key);
    if (it == cache.end()) {
        misses++;
        return nullptr;
    }

    hits++;
    return it->second;
}

void InstanceCache::insert(const InstanceBodySymbol& instance) {
    cache.emplace(instance.getCacheKey(), &instance);
}

} // namespace slang