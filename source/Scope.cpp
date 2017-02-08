#include "Scope.h"
#include "Symbol.h"

namespace slang {

static const Scope emptyScope;
const Scope* const Scope::Empty = &emptyScope;

Scope::Scope() : parentScope{nullptr} {}

bool Scope::add(const Symbol *symbol) {
    ASSERT(symbol);
    if (!table.emplace(symbol->name, symbol).second) return false;
    list.emplace_back(symbol);
    return true;
}

const Symbol *Scope::lookup(StringRef name, bool local) const {
    for (auto scope = this; scope && scope != Scope::Empty; scope = scope->parent()) {
        auto it = scope->table.find(name);
        if (it != scope->table.end()) return it->second;
        if (local) return nullptr;
    }
    return nullptr;
}

const Symbol* Scope::getNth(const SymbolKind& kind, size_t index) const {
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
