//------------------------------------------------------------------------------
//! @file InstanceCacheKey.h
//! @brief Hash key for instance symbols
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <vector>

#include "slang/util/SmallMap.h"
#include "slang/util/Util.h"

namespace slang::ast {

class InstanceSymbol;
class ModportSymbol;

/// A key type used for hashing instance symbols.
class InstanceCacheKey {
public:
    InstanceCacheKey(const InstanceSymbol& symbol, bool& valid,
                     SmallSet<const InstanceSymbol*, 2>& visitedInstances);

    bool operator==(const InstanceCacheKey& other) const;
    bool operator!=(const InstanceCacheKey& other) const { return !(*this == other); }

    size_t hash() const { return savedHash; }

    static bool isEligibleForCaching(const InstanceSymbol& symbol);

private:
    not_null<const InstanceSymbol*> symbol;
    std::vector<std::pair<InstanceCacheKey, const ModportSymbol*>> ifaceKeys;
    size_t savedHash;
};

} // namespace slang::ast

namespace slang {

template<>
struct hash<ast::InstanceCacheKey> {
    size_t operator()(const ast::InstanceCacheKey& key) const noexcept { return key.hash(); }
};

} // namespace slang
