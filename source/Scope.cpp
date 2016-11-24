#include "Scope.h"
#include "Symbol.h"

namespace slang {

void Scope::add(const Symbol* symbol) {
    ASSERT(symbol);
    
    StringRef name = symbol->name();
    ASSERT(name.length() > 0);

    table.emplace(symbol->name(), symbol);
}

const Symbol* Scope::lookup(StringRef name) {
    auto it = table.find(name);
    if (it == table.end())
        return nullptr;
    return it->second;
}

}