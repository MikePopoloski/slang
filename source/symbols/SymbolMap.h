//------------------------------------------------------------------------------
// SymbolMap.h
// Mapping data structure for lookup up symbols.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "flat_hash_map.hpp"

#include "util/Util.h"

namespace slang {

class Symbol;

/// A helper data structure for looking up symbols in a scope.
/// This primarily hides away the hashmap and lookup logic.
class SymbolMap {
public:
    // Each entry in the name map is comprised of the actual symbol along with
    // an index denoting ordering of elements within the scope. This ordering is
    // used when looking up names to determine whether a particular symbol is
    // visible (i.e. has been declared before being referenced). For names imported
    // from other scopes, this can either be a logical index of where they would live
    // in this lexical scope, or UINT32_MAX if ordering should be ignored.
    struct NameEntry {
        const Symbol* symbol;
        uint32_t index;
    };

    /// Adds a symbol to the map. The index, if provided, indicates
    /// where in the scope's list of members the symbol can be found.
    void add(const Symbol& symbol, uint32_t index = UINT32_MAX);

    /// Looks for a symbol with the given name and returns its entry if found.
    /// If not found, returns nullptr.
    const NameEntry* find(string_view name) const;

private:
    flat_hash_map<string_view, NameEntry> map;
};

}