#include "Scope.h"
#include "Symbol.h"

namespace slang {

static const Scope emptyScope;
const Scope* const Scope::Empty = &emptyScope;

bool Scope::add(const Symbol *symbol) {
    ASSERT(symbol);
    if (!table.emplace(symbol->name, symbol).second) return false;
    list.emplace_back(symbol);
    return true;
}

const Symbol *Scope::lookup(StringRef name, bool local) const {
    auto it = table.find(name);
    if (it != table.end()) return it->second;
    if (local) return nullptr;
    for (auto scope : parents) {
        auto sym = scope->lookup(name);
        if (sym) return sym;
    }
    return nullptr;
}

const Symbol* Scope::getNth(const SymbolKind& kind, size_t index) const {
    // TODO: poor man's iterator
    for (const Symbol* s : list) {
        if (s->kind == kind ) {
            if (index == 0)
                return s;
            index--;
        }
    }
    return nullptr;
}

std::string Scope::toString() const {
    std::string result;
    for (const Symbol* sym : list)
        result += std::string("[") + sym->name.toString() + std::string("]");
    return result;
}


}
