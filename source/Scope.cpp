#include "Scope.h"
#include "Symbol.h"

namespace slang {

static const Scope emptyScope;
const Scope* const Scope::Empty = &emptyScope;

void Scope::add(const Symbol* symbol) {
    ASSERT(symbol);
    table.emplace(symbol->name, symbol);
}

const Symbol* Scope::lookup(StringRef name) const {
    auto it = table.find(name);
    if (it == table.end())
        return nullptr;
    return it->second;
}

}