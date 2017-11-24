//------------------------------------------------------------------------------
// SymbolMap.cpp
// Mapping data structure for lookup up symbols.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "SymbolMap.h"

#include "Symbol.h"

namespace slang {

void SymbolMap::add(const Symbol& symbol, uint32_t index) {
    map.emplace(symbol.name, NameEntry { &symbol, index });
}

const SymbolMap::NameEntry* SymbolMap::find(string_view name) const {
    auto it = map.find(name);
    if (it == map.end())
        return nullptr;

    return &it->second;
}

}